/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cEL
import Salt.HB.L2cER

/-!
# HB-L2c family estimates — the JUNK-ROW budgets (Wave 2a, node HB-L2c)

The `junkExpr` contributions to the exact overshoot (freeze §S4, amended by the
catch-#245 house ruling: the junk row owns the junk-block class on BOTH sides of BOTH
sums), stated and proven with the frozen conclusion shapes:

* `EL_cJunk_bound` — the `(c)`-junk (priced FIRST; v-junk ∨ w-junk): window elements
  divisible by a small-base (`p ≤ Zz`) squarefull (`e ≥ 2`) prime power exceeding
  `z^{1/4}`, on the `n`- or `n+2`-side.  Counted over the biUnion of `{n : p^e ∣ n}`
  and the shifted `{n : p^e ∣ n+2}` with the geometric-tail majorant
  (`z^{1/16−1/4} = z^{−3/16} ≤ z^{−1/8}`):  `≤ 16·exp(2·z0)·(x / z^{1/8})·L'³`.
* `ER_wJunk_bound` — the `E_R` w-side junk row (#245 amendment 2): the same class
  restricted to the `n+2` side, weighted `Λ(n)·(Λ̃−Λ)(n+2)`, via the shared card
  bound:  `≤ 16·exp(2·z0)·(x / z^{1/8})·L'³`.
* `EL_corners_bound` — the corners row: the large-squarefull corner classes
  (`p^e > x^{1/4}`, `e ≥ 2`, either side — subsuming the `>√x` even blocks, the
  pure-pp `m = 1` squarefull side, and the `>x^{1/4}` squarefull corners):
  `≤ 24576·exp(2·z0)·(x^{9/10})·L'³`.

The `Cmain` are explicit absolute constants; the frozen master hypotheses
`(hz100 : 100^16 ≤ z) (hz8 : L'^8 ≤ z) (hzx : z³ ≤ x)` are carried verbatim (`hz8` is
not consumed by these rows).

Single-writer file (`L2cELJunk.lean`); imports the frozen `L2cEL`/`L2cER`/`L2cCore`
surfaces and touches no landed file (`All.lean` is Wave 3's responsibility).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — the `(c)`-junk subset and its sum -/

open Classical in
/-- **The `(c)`-junk subset** of the window: elements `n` divisible (on the `n`- or the
    `n+2`-side) by a small-base (`p ≤ Zz`) squarefull (`e ≥ 2`) prime power exceeding
    `z^{1/4}`.  A superset of the genuine small-base squarefull `v`/`w`-blocks, so the
    budget covers the freeze's `(c)`-junk for both routings. -/
noncomputable def cJunkSet (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (l2cWindow χ z x).filter (fun n =>
    ∃ p e, p.Prime ∧ p ≤ Zz z ∧ 2 ≤ e ∧
      (z : ℝ) ^ ((1 : ℝ) / 4) < ((p ^ e : ℕ) : ℝ) ∧ (p ^ e ∣ n ∨ p ^ e ∣ (n + 2)))

/-- **The `(c)`-junk sum** `Σ_{n ∈ cJunkSet} (Λ̃−Λ)(n)·Λ̃(n+2)` — the part of `E_L`
    priced by the geometric-tail junk budget. -/
noncomputable def cJunkSum (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ cJunkSet χ z x, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

/-! ## §1 — the interval-multiples counting primitives (crude, no `+1`) -/

/-- `#{n ∈ (x,2x] : d ∣ n} ≤ 2x/d` (subset of `(0,2x]`, whose `d`-multiples number `2x/d`). -/
lemma cJunk_dvd_count (x d : ℕ) (_hd : 0 < d) :
    (((Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)).card : ℝ) ≤ (2 * (x : ℝ)) / d := by
  have hsub : (Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)
      ⊆ (Finset.Ioc 0 (2 * x)).filter (fun n => d ∣ n) := by
    apply Finset.filter_subset_filter
    intro n hn; rw [Finset.mem_Ioc] at hn ⊢; omega
  calc (((Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)).card : ℝ)
      ≤ (((Finset.Ioc 0 (2 * x)).filter (fun n => d ∣ n)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (((2 * x) / d : ℕ) : ℝ) := by rw [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ (2 * (x : ℝ)) / d := by
        have := Nat.cast_div_le (m := 2 * x) (n := d) (α := ℝ); push_cast at this ⊢; linarith

/-- `#{n ∈ (x,2x] : d ∣ n+2} ≤ (2x+2)/d` (shift `n ↦ n+2` into `(0,2x+2]`). -/
lemma cJunk_dvd_count_shift (x d : ℕ) (_hd : 0 < d) :
    (((Finset.Ioc x (2 * x)).filter (fun n => d ∣ (n + 2))).card : ℝ)
      ≤ (2 * (x : ℝ) + 2) / d := by
  set S := (Finset.Ioc x (2 * x)).filter (fun n => d ∣ (n + 2)) with hS
  have hinj : Function.Injective (fun n => n + 2) := add_left_injective 2
  have himg : S.image (fun n => n + 2)
      ⊆ (Finset.Ioc 0 (2 * x + 2)).filter (fun m => d ∣ m) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨n, hnS, rfl⟩ := hm
    rw [hS, Finset.mem_filter, Finset.mem_Ioc] at hnS
    rw [Finset.mem_filter, Finset.mem_Ioc]
    obtain ⟨⟨hxn, hn2x⟩, hdvd⟩ := hnS
    exact ⟨⟨by omega, by omega⟩, hdvd⟩
  have hcard_eq : S.card = (S.image (fun n => n + 2)).card :=
    (Finset.card_image_of_injective S hinj).symm
  calc (S.card : ℝ) = ((S.image (fun n => n + 2)).card : ℝ) := by rw [hcard_eq]
    _ ≤ (((Finset.Ioc 0 (2 * x + 2)).filter (fun m => d ∣ m)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card himg
    _ = (((2 * x + 2) / d : ℕ) : ℝ) := by rw [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ (2 * (x : ℝ) + 2) / d := by
        have := Nat.cast_div_le (m := 2 * x + 2) (n := d) (α := ℝ)
        push_cast at this ⊢; linarith

/-- The per-pair count: `#{n ∈ (x,2x] : d ∣ n ∨ d ∣ n+2} ≤ 2·(2x+2)/d`. -/
lemma cJunk_pair_count (x d : ℕ) (hd : 0 < d) :
    (((Finset.Ioc x (2 * x)).filter (fun n => d ∣ n ∨ d ∣ (n + 2))).card : ℝ)
      ≤ 2 * (2 * (x : ℝ) + 2) / d := by
  have hor : (Finset.Ioc x (2 * x)).filter (fun n => d ∣ n ∨ d ∣ (n + 2))
      = (Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)
        ∪ (Finset.Ioc x (2 * x)).filter (fun n => d ∣ (n + 2)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (((Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)).card : ℝ)
      ≤ (2 * (x : ℝ) + 2) / d := by
    have := cJunk_dvd_count x d hd
    have hmono : (2 * (x : ℝ)) / d ≤ (2 * (x : ℝ) + 2) / d := by
      apply div_le_div_of_nonneg_right (by linarith) hdr.le
    linarith
  have h2 : (((Finset.Ioc x (2 * x)).filter (fun n => d ∣ (n + 2))).card : ℝ)
      ≤ (2 * (x : ℝ) + 2) / d := cJunk_dvd_count_shift x d hd
  rw [hor]
  calc (((Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)
          ∪ (Finset.Ioc x (2 * x)).filter (fun n => d ∣ (n + 2))).card : ℝ)
      ≤ (((Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)).card : ℝ)
        + (((Finset.Ioc x (2 * x)).filter (fun n => d ∣ (n + 2))).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ (2 * (x : ℝ) + 2) / d + (2 * (x : ℝ) + 2) / d := by linarith
    _ = 2 * (2 * (x : ℝ) + 2) / d := by ring

/-! ## §2 — the scale facts and the `(c)`-junk index pairs -/

/-- `log 2 ≥ 1/2` (from `log(1/2) ≤ 1/2 − 1`, no numeric tables). -/
lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  rw [one_div, Real.log_inv] at h
  linarith

/-- `log 2 ≤ 1` (from `log y ≤ y − 1`). -/
lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

/-- The binary exponent range: `(log₂(2x+2) : ℝ) ≤ 2·L'`. -/
lemma natLog_le_two_Lwin (x : ℕ) :
    ((Nat.log 2 (2 * x + 2) : ℕ) : ℝ) ≤ 2 * Lwin x := by
  have h2E : (2 : ℕ) ^ Nat.log 2 (2 * x + 2) ≤ 2 * x + 2 :=
    Nat.pow_log_le_self 2 (by omega)
  have hR : (2 : ℝ) ^ Nat.log 2 (2 * x + 2) ≤ 2 * (x : ℝ) + 2 := by exact_mod_cast h2E
  have hlog : ((Nat.log 2 (2 * x + 2) : ℕ) : ℝ) * Real.log 2 ≤ Lwin x := by
    rw [Lwin, ← Real.log_pow]
    exact Real.log_le_log (by positivity) hR
  have hE0 : (0 : ℝ) ≤ ((Nat.log 2 (2 * x + 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [half_le_log_two,
    mul_nonneg hE0 (by linarith [half_le_log_two] : (0 : ℝ) ≤ Real.log 2 - 1 / 2)]

open Classical in
/-- **The `(c)`-junk index pairs** `(p,e)`: `2 ≤ p ≤ Zz`, `2 ≤ e ≤ log₂(2x+2)`,
    `z^{1/4} < p^e` — the small-base squarefull blocks the geometric tail prices. -/
noncomputable def cJunkPairs (z x : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 (Zz z)) ×ˢ (Finset.Icc 2 (Nat.log 2 (2 * x + 2)))).filter
    (fun pe => (z : ℝ) ^ ((1 : ℝ) / 4) < ((pe.1 ^ pe.2 : ℕ) : ℝ))

/-- The `(c)`-junk cover: every junk element is a multiple of some indexed `p^e`
    (on the `n`- or the `n+2`-side). -/
lemma cJunkSet_subset_biUnion (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    cJunkSet χ z x ⊆ (cJunkPairs z x).biUnion
      (fun pe => (Finset.Ioc x (2 * x)).filter
        (fun n => pe.1 ^ pe.2 ∣ n ∨ pe.1 ^ pe.2 ∣ (n + 2))) := by
  intro n hn
  simp only [cJunkSet, Finset.mem_filter] at hn
  obtain ⟨hnw, p, e, hp, hpZ, he2, hgt, hdvd⟩ := hn
  have hnI : n ∈ Finset.Ioc x (2 * x) := l2cWindow_subset χ z x hnw
  have hnIoc := Finset.mem_Ioc.mp hnI
  have hpe_le : p ^ e ≤ 2 * x + 2 := by
    rcases hdvd with h | h
    · exact le_trans (Nat.le_of_dvd (by omega) h) (by omega)
    · exact le_trans (Nat.le_of_dvd (by omega) h) (by omega)
  have heE : e ≤ Nat.log 2 (2 * x + 2) :=
    Nat.le_log_of_pow_le (by norm_num)
      (le_trans (Nat.pow_le_pow_left hp.two_le e) hpe_le)
  rw [Finset.mem_biUnion]
  exact ⟨(p, e), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpZ⟩,
      Finset.mem_Icc.mpr ⟨he2, heE⟩⟩, hgt⟩,
    Finset.mem_filter.mpr ⟨hnI, hdvd⟩⟩

/-! ## §3 — the `(c)`-junk card bound -/

/-- **The `(c)`-junk card bound.**  `#cJunkSet ≤ 16·L'·x/z^{1/8}` (per-pair count
    `≤ 2(2x+2)·z^{−1/4}`, `≤ z^{1/16}·2L'` pairs, `z^{1/16−1/4} = z^{−3/16} ≤ z^{−1/8}`). -/
lemma cJunkSet_card_le (χ : DirichletCharacter ℂ q) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ((cJunkSet χ z x).card : ℝ)
      ≤ 16 * Lwin x * ((x : ℝ) / (z : ℝ) ^ ((1 : ℝ) / 8)) := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz1R : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hz0R : (0 : ℝ) < (z : ℝ) := by linarith
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by
    refine le_trans ?_ hzx
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hz1R 3
    simpa using this
  have hq0 : (0 : ℝ) < (z : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hz0R _
  have hL0 : 0 ≤ Lwin x := Lwin_nonneg x
  -- step 1: the biUnion cover
  have h1 : ((cJunkSet χ z x).card : ℝ)
      ≤ ∑ pe ∈ cJunkPairs z x,
          (((Finset.Ioc x (2 * x)).filter
            (fun n => pe.1 ^ pe.2 ∣ n ∨ pe.1 ^ pe.2 ∣ (n + 2))).card : ℝ) := by
    have hA := Finset.card_le_card (cJunkSet_subset_biUnion χ z x)
    have hB := Finset.card_biUnion_le (s := cJunkPairs z x)
      (t := fun pe => (Finset.Ioc x (2 * x)).filter
        (fun n => pe.1 ^ pe.2 ∣ n ∨ pe.1 ^ pe.2 ∣ (n + 2)))
    exact_mod_cast le_trans hA hB
  -- step 2: each pair contributes ≤ 2(2x+2)/z^{1/4}
  have h2 : ∀ pe ∈ cJunkPairs z x,
      (((Finset.Ioc x (2 * x)).filter
        (fun n => pe.1 ^ pe.2 ∣ n ∨ pe.1 ^ pe.2 ∣ (n + 2))).card : ℝ)
        ≤ 2 * (2 * (x : ℝ) + 2) / (z : ℝ) ^ ((1 : ℝ) / 4) := by
    intro pe hpe
    simp only [cJunkPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpe
    obtain ⟨⟨⟨hp2, _⟩, _, _⟩, hgt⟩ := hpe
    have hdpos : 0 < pe.1 ^ pe.2 := pow_pos (by omega) pe.2
    have hinv : 1 / ((pe.1 ^ pe.2 : ℕ) : ℝ) ≤ 1 / (z : ℝ) ^ ((1 : ℝ) / 4) :=
      one_div_le_one_div_of_le hq0 hgt.le
    calc (((Finset.Ioc x (2 * x)).filter
          (fun n => pe.1 ^ pe.2 ∣ n ∨ pe.1 ^ pe.2 ∣ (n + 2))).card : ℝ)
        ≤ 2 * (2 * (x : ℝ) + 2) / ((pe.1 ^ pe.2 : ℕ) : ℝ) :=
          cJunk_pair_count x (pe.1 ^ pe.2) hdpos
      _ = 2 * (2 * (x : ℝ) + 2) * (1 / ((pe.1 ^ pe.2 : ℕ) : ℝ)) := by ring
      _ ≤ 2 * (2 * (x : ℝ) + 2) * (1 / (z : ℝ) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * (2 * (x : ℝ) + 2) / (z : ℝ) ^ ((1 : ℝ) / 4) := by ring
  -- step 3: the pair count is ≤ z^{1/16}·2L'
  have hcard : ((cJunkPairs z x).card : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) * (2 * Lwin x) := by
    have hle1 : (cJunkPairs z x).card ≤ Zz z * Nat.log 2 (2 * x + 2) := by
      calc (cJunkPairs z x).card
          ≤ ((Finset.Icc 2 (Zz z)) ×ˢ (Finset.Icc 2 (Nat.log 2 (2 * x + 2)))).card :=
            Finset.card_filter_le _ _
        _ = (Finset.Icc 2 (Zz z)).card * (Finset.Icc 2 (Nat.log 2 (2 * x + 2))).card :=
            Finset.card_product _ _
        _ ≤ Zz z * Nat.log 2 (2 * x + 2) := by
            apply Nat.mul_le_mul <;> (rw [Nat.card_Icc]; omega)
    have hZzR : ((Zz z : ℕ) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := by
      simp only [Zz]; exact Nat.floor_le (by positivity)
    calc ((cJunkPairs z x).card : ℝ)
        ≤ ((Zz z : ℕ) : ℝ) * ((Nat.log 2 (2 * x + 2) : ℕ) : ℝ) := by exact_mod_cast hle1
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 16) * (2 * Lwin x) :=
          mul_le_mul hZzR (natLog_le_two_Lwin x) (Nat.cast_nonneg _) (by positivity)
  -- assembly
  have h3 : ((cJunkSet χ z x).card : ℝ)
      ≤ ((cJunkPairs z x).card : ℝ) * (2 * (2 * (x : ℝ) + 2) / (z : ℝ) ^ ((1 : ℝ) / 4)) := by
    refine le_trans h1 ?_
    have := Finset.sum_le_card_nsmul (cJunkPairs z x) _ _ h2
    rwa [nsmul_eq_mul] at this
  have hbr0 : (0 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) * (2 * Lwin x) * (1 / (z : ℝ) ^ ((1 : ℝ) / 4)) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  calc ((cJunkSet χ z x).card : ℝ)
      ≤ ((cJunkPairs z x).card : ℝ) * (2 * (2 * (x : ℝ) + 2) / (z : ℝ) ^ ((1 : ℝ) / 4)) := h3
    _ ≤ ((z : ℝ) ^ ((1 : ℝ) / 16) * (2 * Lwin x))
          * (2 * (2 * (x : ℝ) + 2) / (z : ℝ) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (2 * (2 * (x : ℝ) + 2))
          * ((z : ℝ) ^ ((1 : ℝ) / 16) * (2 * Lwin x) * (1 / (z : ℝ) ^ ((1 : ℝ) / 4))) := by
        ring
    _ ≤ (8 * (x : ℝ))
          * ((z : ℝ) ^ ((1 : ℝ) / 16) * (2 * Lwin x) * (1 / (z : ℝ) ^ ((1 : ℝ) / 4))) :=
        mul_le_mul_of_nonneg_right (by linarith) hbr0
    _ = 16 * Lwin x * (x : ℝ) * ((z : ℝ) ^ ((1 : ℝ) / 16) / (z : ℝ) ^ ((1 : ℝ) / 4)) := by ring
    _ = 16 * Lwin x * (x : ℝ) * (z : ℝ) ^ ((1 : ℝ) / 16 - (1 : ℝ) / 4) := by
        rw [Real.rpow_sub hz0R]
    _ ≤ 16 * Lwin x * (x : ℝ) * (z : ℝ) ^ (-((1 : ℝ) / 8)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hz1R (by norm_num))
          (mul_nonneg (mul_nonneg (by norm_num) hL0) (Nat.cast_nonneg x))
    _ = 16 * Lwin x * ((x : ℝ) / (z : ℝ) ^ ((1 : ℝ) / 8)) := by
        rw [Real.rpow_neg (le_of_lt hz0R)]
        ring

/-! ## §4 — the per-summand caps (crude, junk-row grade)

Junk rows price by cardinality: each summand is capped by `e^{2z₀}·L'²` (the crude caps
are exactly right here — catch #245 amendment 4 confirms the sharp single-block cap is
mandatory only for the *family* rows, not the junk rows). -/

/-- The left-summand cap: on the window, `(Λ̃−Λ)(n)·Λ̃(n+2) ≤ e^{2z₀}·L'²`. -/
lemma left_summand_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hz2 : 2 ≤ z) (hn : n ∈ l2cWindow χ z x) :
    (LamTilde χ n - Λ n) * LamTilde χ (n + 2) ≤ Real.exp (2 * z0 z x) * Lwin x ^ 2 := by
  have hc1 := lamTilde_cap_window χ hsq hz2 hn
  have hc2 := lamTilde_cap_window_add_two χ hsq hz2 hn
  have ha : LamTilde χ n - Λ n ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x :=
    le_trans (sub_le_self _ vonMangoldt_nonneg) hc1
  have hb0 : 0 ≤ LamTilde χ (n + 2) := lamTilde_nonneg χ hsq (n + 2)
  have hcap0 : (0 : ℝ) ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x :=
    mul_nonneg (Real.exp_pos _).le (Lwin_nonneg x)
  have hz00 : 0 ≤ z0 z x := z0_nonneg hz2
  have hexp : Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x)
      ≤ Real.exp (2 * z0 z x) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg hz00 (by linarith [log_two_le_one] : (0 : ℝ) ≤ 1 - Real.log 2)]
  calc (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ (Real.exp (Real.log 2 * z0 z x) * Lwin x)
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x) := mul_le_mul ha hc2 hb0 hcap0
    _ = (Real.exp (Real.log 2 * z0 z x) * Real.exp (Real.log 2 * z0 z x)) * Lwin x ^ 2 := by
        ring
    _ ≤ Real.exp (2 * z0 z x) * Lwin x ^ 2 :=
        mul_le_mul_of_nonneg_right hexp (pow_nonneg (Lwin_nonneg x) 2)

/-- The right-summand cap: on the window, `Λ(n)·(Λ̃−Λ)(n+2) ≤ e^{2z₀}·L'²`
    (`Λ(n) ≤ L'` from `L2cER.l2cWindow_vonMangoldt_cap`). -/
lemma right_summand_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hz2 : 2 ≤ z) (hn : n ∈ l2cWindow χ z x) :
    Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) ≤ Real.exp (2 * z0 z x) * Lwin x ^ 2 := by
  have h1 : Λ n ≤ Lwin x := l2cWindow_vonMangoldt_cap χ hn
  have h2 : LamTilde χ (n + 2) - Λ (n + 2) ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x :=
    le_trans (sub_le_self _ vonMangoldt_nonneg) (lamTilde_cap_window_add_two χ hsq hz2 hn)
  have hb0 : 0 ≤ LamTilde χ (n + 2) - Λ (n + 2) := lamTilde_sub_nonneg χ hsq (n + 2)
  have hz00 : 0 ≤ z0 z x := z0_nonneg hz2
  have hexp : Real.exp (Real.log 2 * z0 z x) ≤ Real.exp (2 * z0 z x) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg hz00 (by linarith [log_two_le_one] : (0 : ℝ) ≤ 2 - Real.log 2)]
  calc Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ Lwin x * (Real.exp (Real.log 2 * z0 z x) * Lwin x) :=
        mul_le_mul h1 h2 hb0 (Lwin_nonneg x)
    _ = Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2 := by ring
    _ ≤ Real.exp (2 * z0 z x) * Lwin x ^ 2 :=
        mul_le_mul_of_nonneg_right hexp (pow_nonneg (Lwin_nonneg x) 2)

/-! ## §5 — the `(c)`-junk budget (the frozen `x/z^{1/8}` junkExpr row) -/

/-- **`EL_cJunk_bound` — the `(c)`-junk budget** (freeze §S4, priced FIRST; extended per
    the catch-#245 house amendments to own the junk-block class on both sides, v-junk ∨
    w-junk; the conclusion is the frozen junkExpr `x/z^{1/8}` shape with `Cmain = 16`). -/
theorem EL_cJunk_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (_hz8 : (Lwin x) ^ 8 ≤ (z : ℝ)) (hzx : (z : ℝ) ^ 3 ≤ x) :
    cJunkSum χ z x
      ≤ 16 * Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ ((1 : ℝ) / 8)) * Lwin x ^ 3 := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hsub : cJunkSet χ z x ⊆ l2cWindow χ z x := fun n hn => by
    simp only [cJunkSet, Finset.mem_filter] at hn; exact hn.1
  have hsum : cJunkSum χ z x
      ≤ ((cJunkSet χ z x).card : ℝ) * (Real.exp (2 * z0 z x) * Lwin x ^ 2) := by
    rw [cJunkSum]
    have := Finset.sum_le_card_nsmul (cJunkSet χ z x) _ _
      (fun n hn => left_summand_cap χ hsq hz2 (hsub hn))
    rwa [nsmul_eq_mul] at this
  have hM0 : (0 : ℝ) ≤ Real.exp (2 * z0 z x) * Lwin x ^ 2 :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg (Lwin_nonneg x) 2)
  calc cJunkSum χ z x
      ≤ ((cJunkSet χ z x).card : ℝ) * (Real.exp (2 * z0 z x) * Lwin x ^ 2) := hsum
    _ ≤ (16 * Lwin x * ((x : ℝ) / (z : ℝ) ^ ((1 : ℝ) / 8)))
          * (Real.exp (2 * z0 z x) * Lwin x ^ 2) :=
        mul_le_mul_of_nonneg_right (cJunkSet_card_le χ hz100 hzx) hM0
    _ = 16 * Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ ((1 : ℝ) / 8)) * Lwin x ^ 3 := by
        ring

/-! ## §6 — the `E_R` w-side junk row (catch-#245 amendment 2) -/

open Classical in
/-- **The `E_R` w-junk subset**: window elements whose `n+2` side carries a junk block
    (`p ≤ Zz`, `e ≥ 2`, `z^{1/4} < p^e`, `p^e ∣ n+2`) — the class the guarded `E_R`
    mirror families exclude. -/
noncomputable def wJunkSet (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (l2cWindow χ z x).filter (fun n =>
    ∃ p e, p.Prime ∧ p ≤ Zz z ∧ 2 ≤ e ∧
      (z : ℝ) ^ ((1 : ℝ) / 4) < ((p ^ e : ℕ) : ℝ) ∧ p ^ e ∣ (n + 2))

/-- **The `E_R` w-junk sum** `Σ_{n ∈ wJunkSet} Λ(n)·(Λ̃−Λ)(n+2)`. -/
noncomputable def wJunkSum (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ wJunkSet χ z x, Λ n * (LamTilde χ (n + 2) - Λ (n + 2))

/-- The w-junk class sits inside the two-sided `(c)`-junk class. -/
lemma wJunkSet_subset_cJunkSet (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    wJunkSet χ z x ⊆ cJunkSet χ z x := by
  intro n hn
  simp only [wJunkSet, Finset.mem_filter] at hn
  simp only [cJunkSet, Finset.mem_filter]
  obtain ⟨hnw, p, e, hp, hpZ, he2, hgt, hdvd⟩ := hn
  exact ⟨hnw, p, e, hp, hpZ, he2, hgt, Or.inr hdvd⟩

/-- **`ER_wJunk_bound` — the `E_R` w-side junk budget** (catch-#245 amendment 2): the
    junkExpr `x/z^{1/8}` shape with `Cmain = 16`, via the shared `(c)`-junk card bound. -/
theorem ER_wJunk_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (_hz8 : (Lwin x) ^ 8 ≤ (z : ℝ)) (hzx : (z : ℝ) ^ 3 ≤ x) :
    wJunkSum χ z x
      ≤ 16 * Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ ((1 : ℝ) / 8)) * Lwin x ^ 3 := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hsub : wJunkSet χ z x ⊆ l2cWindow χ z x := fun n hn => by
    simp only [wJunkSet, Finset.mem_filter] at hn; exact hn.1
  have hcard : ((wJunkSet χ z x).card : ℝ) ≤ ((cJunkSet χ z x).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (wJunkSet_subset_cJunkSet χ z x)
  have hsum : wJunkSum χ z x
      ≤ ((wJunkSet χ z x).card : ℝ) * (Real.exp (2 * z0 z x) * Lwin x ^ 2) := by
    rw [wJunkSum]
    have := Finset.sum_le_card_nsmul (wJunkSet χ z x) _ _
      (fun n hn => right_summand_cap χ hsq hz2 (hsub hn))
    rwa [nsmul_eq_mul] at this
  have hM0 : (0 : ℝ) ≤ Real.exp (2 * z0 z x) * Lwin x ^ 2 :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg (Lwin_nonneg x) 2)
  calc wJunkSum χ z x
      ≤ ((wJunkSet χ z x).card : ℝ) * (Real.exp (2 * z0 z x) * Lwin x ^ 2) := hsum
    _ ≤ ((cJunkSet χ z x).card : ℝ) * (Real.exp (2 * z0 z x) * Lwin x ^ 2) :=
        mul_le_mul_of_nonneg_right hcard hM0
    _ ≤ (16 * Lwin x * ((x : ℝ) / (z : ℝ) ^ ((1 : ℝ) / 8)))
          * (Real.exp (2 * z0 z x) * Lwin x ^ 2) :=
        mul_le_mul_of_nonneg_right (cJunkSet_card_le χ hz100 hzx) hM0
    _ = 16 * Real.exp (2 * z0 z x) * ((x : ℝ) / (z : ℝ) ^ ((1 : ℝ) / 8)) * Lwin x ^ 3 := by
        ring

/-! ## §7 — the corners row (the frozen `x^{9/10}` junkExpr row)

The corner set: window elements carrying a **large squarefull block** `p^e > x^{1/4}`
(`e ≥ 2`) on either side.  This subsumes the freeze's corner classes that price as junk:
the even-block `e`-split's `2^e > √x` side (`e ≥ 2` automatic), the `m = 1` pure-pp side
when squarefull, and the `> x^{1/4}` squarefull corners.  The non-squarefull corner
pieces (prime blocks) are family-sifted per the #245 amendments — they are exactly the
`Zz`-rough cofactor routes of the guarded family slices. -/

open Classical in
/-- **The corner set**: window elements with a squarefull block `p^e > x^{1/4}` (`e ≥ 2`)
    dividing `n` or `n+2`. -/
noncomputable def cornerSet (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (l2cWindow χ z x).filter (fun n =>
    ∃ p e, p.Prime ∧ 2 ≤ e ∧ (x : ℝ) ^ ((1 : ℝ) / 4) < ((p ^ e : ℕ) : ℝ) ∧
      (p ^ e ∣ n ∨ p ^ e ∣ (n + 2)))

/-- **The corners sum** `Σ_{n ∈ cornerSet} (Λ̃−Λ)(n)·Λ̃(n+2)`. -/
noncomputable def cornersSum (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ cornerSet χ z x, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

open Classical in
/-- **The corner index pairs** `(p,e)`: `p ≤ 2x+2` prime, `2 ≤ e ≤ log₂(2x+2)`,
    `x^{1/4} < p^e`. -/
noncomputable def cornerPairs (x : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.Icc 2 (2 * x + 2)).filter Nat.Prime)
      ×ˢ (Finset.Icc 2 (Nat.log 2 (2 * x + 2)))).filter
    (fun pe => (x : ℝ) ^ ((1 : ℝ) / 4) < ((pe.1 ^ pe.2 : ℕ) : ℝ))

/-- The corner cover: every corner element is a multiple of some indexed `p^e`. -/
lemma cornerSet_subset_biUnion (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    cornerSet χ z x ⊆ (cornerPairs x).biUnion
      (fun pe => (Finset.Ioc x (2 * x)).filter
        (fun n => pe.1 ^ pe.2 ∣ n ∨ pe.1 ^ pe.2 ∣ (n + 2))) := by
  intro n hn
  simp only [cornerSet, Finset.mem_filter] at hn
  obtain ⟨hnw, p, e, hp, he2, hgt, hdvd⟩ := hn
  have hnI : n ∈ Finset.Ioc x (2 * x) := l2cWindow_subset χ z x hnw
  have hnIoc := Finset.mem_Ioc.mp hnI
  have hpe_le : p ^ e ≤ 2 * x + 2 := by
    rcases hdvd with h | h
    · exact le_trans (Nat.le_of_dvd (by omega) h) (by omega)
    · exact le_trans (Nat.le_of_dvd (by omega) h) (by omega)
  have heE : e ≤ Nat.log 2 (2 * x + 2) :=
    Nat.le_log_of_pow_le (by norm_num)
      (le_trans (Nat.pow_le_pow_left hp.two_le e) hpe_le)
  have hple : p ≤ 2 * x + 2 := le_trans (Nat.le_self_pow (by omega) p) hpe_le
  rw [Finset.mem_biUnion]
  exact ⟨(p, e), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hple⟩, hp⟩,
        Finset.mem_Icc.mpr ⟨he2, heE⟩⟩, hgt⟩,
    Finset.mem_filter.mpr ⟨hnI, hdvd⟩⟩

/-- Large-squarefull denominators: `p·x^{1/8} ≤ p^e` when `e ≥ 2` and `x^{1/4} < p^e`
    (both factors of `√(p^e)·√(p^e)` dominate: `√(p^e) ≥ p` and `√(p^e) > x^{1/8}`). -/
lemma corner_pair_ge {x p e : ℕ} (hp2 : 2 ≤ p) (he2 : 2 ≤ e)
    (hgt : (x : ℝ) ^ ((1 : ℝ) / 4) < ((p ^ e : ℕ) : ℝ)) :
    (p : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8) ≤ ((p ^ e : ℕ) : ℝ) := by
  have hpe0 : (0 : ℝ) < ((p ^ e : ℕ) : ℝ) := by
    have : 0 < p ^ e := pow_pos (by omega) e
    exact_mod_cast this
  have hsqle : ((p : ℝ)) ^ (2 : ℕ) ≤ ((p ^ e : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ p) he2
  have h1 : (p : ℝ) ≤ ((p ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
    calc (p : ℝ) = ((p : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_mul (by positivity),
            show ((2 : ℕ) : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num, Real.rpow_one]
      _ ≤ ((p ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) hsqle (by norm_num)
  have h2 : (x : ℝ) ^ ((1 : ℝ) / 8) ≤ ((p ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
    calc (x : ℝ) ^ ((1 : ℝ) / 8) = ((x : ℝ) ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_mul (Nat.cast_nonneg x)]
          norm_num
      _ ≤ ((p ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) hgt.le (by norm_num)
  calc (p : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8)
      ≤ ((p ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * ((p ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = ((p ^ e : ℕ) : ℝ) := by
        rw [← Real.rpow_add hpe0, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one]

/-- `L' ≥ 1` on any window with `x ≥ 1` (`L' = log(2x+2) ≥ log 4 = 2·log 2 ≥ 1`). -/
lemma one_le_Lwin {x : ℕ} (hx1 : 1 ≤ x) : 1 ≤ Lwin x := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have h44 : Real.log 4 ≤ Real.log (2 * (x : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  rw [Lwin]
  linarith [half_le_log_two]

/-- **The prime-reciprocal counter** `Σ_{p ≤ 2x+2} 1/p ≤ 16·L'` (termwise
    `1 ≤ 2·log p`, then the Mertens re-export and `log 4 ≤ 3`). -/
lemma sum_inv_prime_le (x : ℕ) (hx1 : 1 ≤ x) :
    ∑ p ∈ (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime, (1 : ℝ) / p ≤ 16 * Lwin x := by
  have hL1 := one_le_Lwin hx1
  have hstep : ∀ p ∈ (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime,
      (1 : ℝ) / p ≤ 2 * (Real.log p / p) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp2, _⟩, _⟩ := hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hlp : (1 : ℝ) / 2 ≤ Real.log p :=
      le_trans half_le_log_two (Real.log_le_log (by norm_num) (by exact_mod_cast hp2))
    calc (1 : ℝ) / p = 1 * (1 / p) := by ring
      _ ≤ (2 * Real.log p) * (1 / p) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 2 * (Real.log p / p) := by ring
  have hsub : (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime
      ⊆ (Finset.range (2 * x + 2 + 1)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  have hmert := mertens_log_div_prime_le (N := 2 * x + 2) (by omega)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have hcast : Real.log ((2 * x + 2 : ℕ) : ℝ) = Lwin x := by
    rw [Lwin]; push_cast; ring_nf
  calc ∑ p ∈ (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime, (1 : ℝ) / p
      ≤ ∑ p ∈ (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime, 2 * (Real.log p / p) :=
        Finset.sum_le_sum hstep
    _ = 2 * ∑ p ∈ (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime, Real.log p / p := by
        rw [Finset.mul_sum]
    _ ≤ 2 * ∑ p ∈ (Finset.range (2 * x + 2 + 1)).filter Nat.Prime, Real.log p / p := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (by norm_num)
        intro p hp _
        rw [Finset.mem_filter] at hp
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)) (by positivity)
    _ ≤ 2 * (Lwin x + (Real.log 4 + 4)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [← hcast]; exact hmert
    _ ≤ 16 * Lwin x := by linarith

/-- **The corner card bound.**  `#cornerSet ≤ 256·(x/x^{1/8})·L'²` (per-pair count
    `≤ (2(2x+2)/x^{1/8})·(1/p)`, `≤ 2L'` exponents, `Σ 1/p ≤ 16L'`). -/
lemma cornerSet_card_le (χ : DirichletCharacter ℂ q) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ((cornerSet χ z x).card : ℝ)
      ≤ 256 * ((x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 8)) * Lwin x ^ 2 := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz1R : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by
    refine le_trans ?_ hzx
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hz1R 3
    simpa using this
  have hx1 : 1 ≤ x := by exact_mod_cast hx1R
  have hx0R : (0 : ℝ) < (x : ℝ) := by linarith
  have hq0 : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hx0R _
  have hL0 : 0 ≤ Lwin x := Lwin_nonneg x
  have h1 : ((cornerSet χ z x).card : ℝ)
      ≤ ∑ pe ∈ cornerPairs x, (((Finset.Ioc x (2 * x)).filter
          (fun n => pe.1 ^ pe.2 ∣ n ∨ pe.1 ^ pe.2 ∣ (n + 2))).card : ℝ) := by
    have hA := Finset.card_le_card (cornerSet_subset_biUnion χ z x)
    have hB := Finset.card_biUnion_le (s := cornerPairs x)
      (t := fun pe => (Finset.Ioc x (2 * x)).filter
        (fun n => pe.1 ^ pe.2 ∣ n ∨ pe.1 ^ pe.2 ∣ (n + 2)))
    exact_mod_cast le_trans hA hB
  have h2 : ∀ pe ∈ cornerPairs x,
      (((Finset.Ioc x (2 * x)).filter
        (fun n => pe.1 ^ pe.2 ∣ n ∨ pe.1 ^ pe.2 ∣ (n + 2))).card : ℝ)
        ≤ 2 * (2 * (x : ℝ) + 2) / (x : ℝ) ^ ((1 : ℝ) / 8) * (1 / pe.1) := by
    intro pe hpe
    simp only [cornerPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpe
    obtain ⟨⟨⟨⟨hp2, _⟩, _⟩, he2, _⟩, hgt⟩ := hpe
    have hp0R : (0 : ℝ) < pe.1 := by exact_mod_cast (by omega : 0 < pe.1)
    have hdpos : 0 < pe.1 ^ pe.2 := pow_pos (by omega) pe.2
    have hge := corner_pair_ge (x := x) hp2 he2 hgt
    have hinv : 1 / ((pe.1 ^ pe.2 : ℕ) : ℝ) ≤ 1 / ((pe.1 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8)) :=
      one_div_le_one_div_of_le (mul_pos hp0R hq0) hge
    calc (((Finset.Ioc x (2 * x)).filter
          (fun n => pe.1 ^ pe.2 ∣ n ∨ pe.1 ^ pe.2 ∣ (n + 2))).card : ℝ)
        ≤ 2 * (2 * (x : ℝ) + 2) / ((pe.1 ^ pe.2 : ℕ) : ℝ) :=
          cJunk_pair_count x (pe.1 ^ pe.2) hdpos
      _ = 2 * (2 * (x : ℝ) + 2) * (1 / ((pe.1 ^ pe.2 : ℕ) : ℝ)) := by ring
      _ ≤ 2 * (2 * (x : ℝ) + 2) * (1 / ((pe.1 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8))) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * (2 * (x : ℝ) + 2) / (x : ℝ) ^ ((1 : ℝ) / 8) * (1 / pe.1) := by
          field_simp
  have h3 : ∑ pe ∈ cornerPairs x, (1 : ℝ) / pe.1 ≤ 2 * Lwin x * (16 * Lwin x) := by
    have hdrop : ∑ pe ∈ cornerPairs x, (1 : ℝ) / pe.1
        ≤ ∑ pe ∈ ((Finset.Icc 2 (2 * x + 2)).filter Nat.Prime)
            ×ˢ (Finset.Icc 2 (Nat.log 2 (2 * x + 2))), (1 : ℝ) / pe.1 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro pe hpe
        simp only [cornerPairs, Finset.mem_filter] at hpe
        exact hpe.1
      · intro pe _ _; positivity
    have hprod : ∑ pe ∈ ((Finset.Icc 2 (2 * x + 2)).filter Nat.Prime)
        ×ˢ (Finset.Icc 2 (Nat.log 2 (2 * x + 2))), (1 : ℝ) / pe.1
        = ∑ p ∈ (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime,
            ((Finset.Icc 2 (Nat.log 2 (2 * x + 2))).card : ℝ) * (1 / p) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun p _ => ?_
      trans (∑ _e ∈ Finset.Icc 2 (Nat.log 2 (2 * x + 2)), (1 : ℝ) / (p : ℝ))
      · exact Finset.sum_congr rfl fun e _ => rfl
      · rw [Finset.sum_const, nsmul_eq_mul]
    have hcardB : ((Finset.Icc 2 (Nat.log 2 (2 * x + 2))).card : ℝ) ≤ 2 * Lwin x := by
      have hc : (Finset.Icc 2 (Nat.log 2 (2 * x + 2))).card ≤ Nat.log 2 (2 * x + 2) := by
        rw [Nat.card_Icc]; omega
      exact le_trans (by exact_mod_cast hc) (natLog_le_two_Lwin x)
    have hs0 : 0 ≤ ∑ p ∈ (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime, (1 : ℝ) / p :=
      Finset.sum_nonneg fun p _ => by positivity
    calc ∑ pe ∈ cornerPairs x, (1 : ℝ) / pe.1
        ≤ ∑ pe ∈ ((Finset.Icc 2 (2 * x + 2)).filter Nat.Prime)
            ×ˢ (Finset.Icc 2 (Nat.log 2 (2 * x + 2))), (1 : ℝ) / pe.1 := hdrop
      _ = ((Finset.Icc 2 (Nat.log 2 (2 * x + 2))).card : ℝ)
            * ∑ p ∈ (Finset.Icc 2 (2 * x + 2)).filter Nat.Prime, (1 : ℝ) / p := by
          rw [hprod, Finset.mul_sum]
      _ ≤ 2 * Lwin x * (16 * Lwin x) :=
          mul_le_mul hcardB (sum_inv_prime_le x hx1) hs0 (by linarith)
  have h4 : ((cornerSet χ z x).card : ℝ)
      ≤ 2 * (2 * (x : ℝ) + 2) / (x : ℝ) ^ ((1 : ℝ) / 8)
          * ∑ pe ∈ cornerPairs x, (1 : ℝ) / pe.1 := by
    refine le_trans h1 ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum h2
  calc ((cornerSet χ z x).card : ℝ)
      ≤ 2 * (2 * (x : ℝ) + 2) / (x : ℝ) ^ ((1 : ℝ) / 8)
          * ∑ pe ∈ cornerPairs x, (1 : ℝ) / pe.1 := h4
    _ ≤ 2 * (2 * (x : ℝ) + 2) / (x : ℝ) ^ ((1 : ℝ) / 8)
          * (2 * Lwin x * (16 * Lwin x)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ 2 * (4 * (x : ℝ)) / (x : ℝ) ^ ((1 : ℝ) / 8) * (2 * Lwin x * (16 * Lwin x)) := by
        refine mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by linarith) hq0.le)
          (mul_nonneg (by linarith) (by linarith))
    _ = 256 * ((x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 8)) * Lwin x ^ 2 := by ring

/-- **`EL_corners_bound` — the corners budget** (freeze §S4 corners row): the frozen
    junkExpr `x^{9/10}` shape with `Cmain = 24576` (the spare `L'` absorbs into
    `x^{1/48}` via `log y ≤ 96·y^{1/96}`, and `1 − 1/8 + 1/48 = 43/48 ≤ 9/10`). -/
theorem EL_corners_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (_hz8 : (Lwin x) ^ 8 ≤ (z : ℝ)) (hzx : (z : ℝ) ^ 3 ≤ x) :
    cornersSum χ z x
      ≤ 24576 * Real.exp (2 * z0 z x) * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3 := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz1R : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hz100R : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by
    refine le_trans ?_ hzx
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hz1R 3
    simpa using this
  have hx0R : (0 : ℝ) < (x : ℝ) := by linarith
  have hzcube : (z : ℝ) ≤ (z : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (z : ℝ))
      (by linarith : (0 : ℝ) ≤ (z : ℝ) - 1)) (by linarith : (0 : ℝ) ≤ (z : ℝ) + 1)]
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (100 : ℝ) ^ 16 := by norm_num
    linarith
  have hL0 : 0 ≤ Lwin x := Lwin_nonneg x
  have hL96 : Lwin x ≤ 96 * (x : ℝ) ^ ((1 : ℝ) / 48) := by
    have hb : 2 * (x : ℝ) + 2 ≤ (x : ℝ) ^ (2 : ℕ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (x : ℝ) - 3)
        (by linarith : (0 : ℝ) ≤ (x : ℝ))]
    have h1 : Lwin x ≤ ((x : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 96) / ((1 : ℝ) / 96) := by
      rw [Lwin]
      exact le_trans (Real.log_le_log (by linarith) hb)
        (Real.log_le_rpow_div (by positivity) (by norm_num))
    have h2 : ((x : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 96) = (x : ℝ) ^ ((1 : ℝ) / 48) := by
      rw [← Real.rpow_natCast (x : ℝ) 2, ← Real.rpow_mul (by positivity)]
      norm_num
    calc Lwin x ≤ ((x : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 96) / ((1 : ℝ) / 96) := h1
      _ = 96 * (x : ℝ) ^ ((1 : ℝ) / 48) := by rw [h2]; ring
  have hsub : cornerSet χ z x ⊆ l2cWindow χ z x := fun n hn => by
    simp only [cornerSet, Finset.mem_filter] at hn; exact hn.1
  have hsum : cornersSum χ z x
      ≤ ((cornerSet χ z x).card : ℝ) * (Real.exp (2 * z0 z x) * Lwin x ^ 2) := by
    rw [cornersSum]
    have := Finset.sum_le_card_nsmul (cornerSet χ z x) _ _
      (fun n hn => left_summand_cap χ hsq hz2 (hsub hn))
    rwa [nsmul_eq_mul] at this
  have hM0 : (0 : ℝ) ≤ Real.exp (2 * z0 z x) * Lwin x ^ 2 :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg (Lwin_nonneg x) 2)
  have hxpow : (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 8) * (x : ℝ) ^ ((1 : ℝ) / 48)
      ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
    have h78 : (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 8) = (x : ℝ) ^ (1 - (1 : ℝ) / 8) := by
      rw [Real.rpow_sub hx0R, Real.rpow_one]
    rw [h78, ← Real.rpow_add hx0R]
    exact Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
  calc cornersSum χ z x
      ≤ ((cornerSet χ z x).card : ℝ) * (Real.exp (2 * z0 z x) * Lwin x ^ 2) := hsum
    _ ≤ (256 * ((x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 8)) * Lwin x ^ 2)
          * (Real.exp (2 * z0 z x) * Lwin x ^ 2) :=
        mul_le_mul_of_nonneg_right (cornerSet_card_le χ hz100 hzx) hM0
    _ = 256 * Real.exp (2 * z0 z x) * ((x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 8)) * Lwin x ^ 3
          * Lwin x := by ring
    _ ≤ 256 * Real.exp (2 * z0 z x) * ((x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 8)) * Lwin x ^ 3
          * (96 * (x : ℝ) ^ ((1 : ℝ) / 48)) := by
        refine mul_le_mul_of_nonneg_left hL96 ?_
        have hd0 : (0 : ℝ) ≤ (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 8) := by positivity
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hd0)
          (pow_nonneg hL0 3)
    _ = 24576 * Real.exp (2 * z0 z x)
          * ((x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 8) * (x : ℝ) ^ ((1 : ℝ) / 48))
          * Lwin x ^ 3 := by ring
    _ ≤ 24576 * Real.exp (2 * z0 z x) * (x : ℝ) ^ ((9 : ℝ) / 10) * Lwin x ^ 3 := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxpow (by positivity)) (pow_nonneg hL0 3)

end Salt.HB
