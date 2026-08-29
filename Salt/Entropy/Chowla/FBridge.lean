/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The F-function bridge (Tao arXiv:1509.05422v1 (2.12)/(3.14)), Chowla/entropy spine node W2-b

This file lands the bilinear "F-function" of Tao's Chowla/Elliott paper at the
Liouville model instantiation `a = 1, b = 0, h = 1, c_p = 1`.  Tao (3.14) reads
`F_p(x,y) := c_p · ∑_{j: j,j+ph ∈ [1,H]} 1_{ay+j ≡ pb (mod ap)} · x_{1,j}·x_{2,j+ph}`,
with `F = ∑_{p ∈ 𝒫_H} F_p`.  At the model values, and reading both factors from a
single window pattern `v : Fin H → ℤ` (`x_{1,j} = v_j`, `x_{2,j+p} = v_{j+p}`), the
indicator collapses to `1_{y ≡ -j (mod p)}`, i.e. at the residue coordinate
`r = residueProj p y = y mod p`, `1_{(j+1 : ZMod p) = -r}` (gate index = product base
index, matching Tao's 1-indexed `[1,H]` convention against the 1-indexed window value
`windowVal … j = λ(n+j+1)`).

## Contents

* `windowVal` — the junk-zero extension `ℕ → ℤ` of a window pattern `Fin H → ℤ`.
* `fBridgeG` — **the per-prime component `G_p(v) : ZMod p → ℝ`** (piece 1): the
  residue-gated double product over the window.
* `fBridgeF` — **the assembly `F(v) : ZMod P_H → ℝ`** (piece 1):
  `∑_{p} G_p(v) ∘ residueProj p` — defeq to the `∑_i G_i (proj_i ·)` shape that
  `hoeffding_residueProj` centers on.
* `card_filter_natCast_eq_le` — the residue-class count `|{j < H : j ≡ c (p)}| ≤ H/p+1`
  (injection `j ↦ j / p`), the deterministic-bound substrate (piece 2).
* `fBridgeG_abs_le` / `fBridgeG_mem_Icc` — **the deterministic box bound** (piece 2):
  `|G_p(v)(r)| ≤ H/p + 1` for a `‖·‖ ≤ 1` pattern; the `[lo, hi]` box feeding Hoeffding.

## Indexing convention

Tao's `j` runs over `[1,H]`; we use the `0`-indexed `Fin H` of `liouvilleWindow`
(`windowVal H v j = v j` for `j < H`, junk `0` outside).  Summing `j ∈ range H` and
letting `windowVal` zero out `j+p ≥ H` reproduces Tao's restricted range `j,j+p ∈ [1,H]`
verbatim (a harmless relabeling of the window).
-/
import Salt.Entropy.Chowla.Concentration
import Salt.Entropy.Chowla.WeakUniform
import Salt.Entropy.Chowla.Dilation
import Salt.Entropy.Chowla.Windows
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

variable (eps : ℚ) (H : ℕ)

/-- Each window prime is nonzero, so `ZMod ↑p` is a `Fintype` (needed to sum/integrate
over the residue coordinate). -/
instance neZero_primeWindow (p : primeWindow eps H) : NeZero (p : ℕ) :=
  ⟨(prime_of_mem_primeWindow p.2).pos.ne'⟩

/-! ## Window values (junk-zero extension) -/

/-- Window value with junk-zero outside `[0,H)`: `windowVal H v j = v j` for `j < H`,
else `0`.  Lets the double product `windowVal j · windowVal (j+p)` be a total function
of `j : ℕ` that automatically vanishes when either index leaves the window. -/
def windowVal (H : ℕ) (v : Fin H → ℤ) (j : ℕ) : ℤ := if h : j < H then v ⟨j, h⟩ else 0

/-- **The junk-zero, as a citable lemma: PER INDEX.**  `windowVal` vanishes at any
index outside `[0,H)`, with no hypothesis on `H` and no case split on the window's
size.  The definition above already says this, but only as a `dite`; W-F3's §1 needs
it as a NAMED fact, because the alternative is to re-derive it at each use site — and
one such re-derivation was taken from a local `have` sitting inside a branch labelled
`-- degenerate: H = 1`, which is evidence about that branch alone. -/
lemma windowVal_eq_zero_of_not_lt {H : ℕ} {v : Fin H → ℤ} {j : ℕ} (hj : ¬ j < H) :
    windowVal H v j = 0 := by
  unfold windowVal
  exact dif_neg hj

/-- **The product form, which is what the double sum actually meets.**  The pair
`windowVal j · windowVal (j+p)` vanishes as soon as EITHER index leaves the window —
per index, not per branch.  This is the statement W-F3's §1 re-derives; it is now
citable at `FBridge`, the definition's own file. -/
lemma windowVal_prod_eq_zero_of_not_lt {H : ℕ} {v : Fin H → ℤ} {j k : ℕ}
    (hjk : ¬ j < H ∨ ¬ k < H) :
    windowVal H v j * windowVal H v k = 0 := by
  rcases hjk with hj | hk
  · rw [windowVal_eq_zero_of_not_lt hj, zero_mul]
  · rw [windowVal_eq_zero_of_not_lt hk, mul_zero]

lemma windowVal_abs_le {H : ℕ} {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (j : ℕ) :
    |(windowVal H v j : ℝ)| ≤ 1 := by
  unfold windowVal
  split_ifs with h
  · exact_mod_cast hv ⟨j, h⟩
  · simp

lemma windowVal_prod_abs_le {H : ℕ} {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (j k : ℕ) :
    |(windowVal H v j : ℝ) * (windowVal H v k : ℝ)| ≤ 1 := by
  rw [abs_mul]
  calc |(windowVal H v j : ℝ)| * |(windowVal H v k : ℝ)|
      ≤ 1 * 1 :=
        mul_le_mul (windowVal_abs_le hv j) (windowVal_abs_le hv k) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The Liouville window satisfies the `‖·‖ ≤ 1` hypothesis (Liouville is `±1`-valued). -/
lemma abs_liouvilleWindow_le_one (H n : ℕ) (i : Fin H) : |liouvilleWindow H n i| ≤ 1 := by
  rw [liouvilleWindow_apply]
  rcases Finset.mem_insert.mp (liouville_mem_pm_one (m := n + (i : ℕ) + 1) (by omega)) with h | h
  · rw [h]; norm_num
  · rw [Finset.mem_singleton.mp h]; norm_num

/-! ## The F-function at the Liouville model (piece 1: definitions) -/

/-- **The per-prime component `G_p(v)` of Tao's F-function (3.14)** at the Liouville
model (`a=1,b=0,h=1,c_p=1`).  For a residue value `r : ZMod p`, the residue-gated
double product `∑_{j} 1_{(j+1 : ZMod p) = -r} · v_j · v_{j+p}` over the window. -/
noncomputable def fBridgeG (v : Fin H → ℤ) (p : primeWindow eps H) : ZMod (p : ℕ) → ℝ :=
  fun r => ∑ j ∈ Finset.range H,
    if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then
      (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ) else 0

/-- **The assembly `F(v) : ZMod P_H → ℝ`** (Tao (2.12)): `∑_{p ∈ 𝒫_H} G_p(v) ∘ residueProj p`.
Definitionally the `∑_i G_i (proj_i ·)` shape centered by `hoeffding_residueProj`. -/
noncomputable def fBridgeF (v : Fin H → ℤ) : ZMod (PH eps H) → ℝ :=
  fun y => ∑ p : primeWindow eps H, fBridgeG eps H v p (residueProj eps H p y)

/-! ## Deterministic bounds (piece 2) -/

/-- The residue-class count: at most `H/p + 1` naturals `j < H` reduce to a fixed
`c : ZMod p` (injection `j ↦ j / p` into `range (H/p+1)`). -/
lemma card_filter_natCast_eq_le {p : ℕ} (c : ZMod p) :
    ((Finset.range H).filter (fun j : ℕ => (j : ZMod p) = c)).card ≤ H / p + 1 := by
  classical
  have hmem : ∀ j ∈ (Finset.range H).filter (fun j : ℕ => (j : ZMod p) = c),
      j / p ∈ Finset.range (H / p + 1) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hj.1.le)
  have hinj : Set.InjOn (fun j : ℕ => j / p)
      ((Finset.range H).filter (fun j : ℕ => (j : ZMod p) = c) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at ha hb
    have heq : (a : ZMod p) = (b : ZMod p) := by rw [ha.2, hb.2]
    have hmod : a % p = b % p := (ZMod.natCast_eq_natCast_iff a b p).mp heq
    have hdiv : a / p = b / p := hab
    calc a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
      _ = p * (b / p) + b % p := by rw [hdiv, hmod]
      _ = b := Nat.div_add_mod b p
  calc ((Finset.range H).filter (fun j : ℕ => (j : ZMod p) = c)).card
      ≤ (Finset.range (H / p + 1)).card :=
        Finset.card_le_card_of_injOn (fun j : ℕ => j / p) hmem hinj
    _ = H / p + 1 := Finset.card_range _

/-- **The deterministic box bound** (piece 2): for a `‖·‖ ≤ 1` window pattern `v`,
`|G_p(v)(r)| ≤ H/p + 1` for every residue value `r`.  Each nonzero term of the
residue-gated sum has modulus `≤ 1`, and the residue class `j ≡ -r (p)` meets the
window `[0,H)` in at most `H/p + 1` points. -/
lemma fBridgeG_abs_le {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (p : primeWindow eps H)
    (r : ZMod (p : ℕ)) :
    |fBridgeG eps H v p r| ≤ (H : ℝ) / (p : ℝ) + 1 := by
  classical
  unfold fBridgeG
  calc |∑ j ∈ Finset.range H, if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ) else 0|
      ≤ ∑ j ∈ Finset.range H, |if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range H, if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs with h
        · exact windowVal_prod_abs_le hv j (j + (p : ℕ))
        · simp
    _ = (((Finset.range H).filter
          (fun j : ℕ => ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r)).card : ℝ) := by
        rw [Finset.sum_boole]
    _ ≤ (H : ℝ) / (p : ℝ) + 1 := by
        have hset : (Finset.range H).filter (fun j : ℕ => ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r)
            = (Finset.range H).filter (fun j : ℕ => (j : ZMod (p : ℕ)) = -r - 1) := by
          apply Finset.filter_congr
          intro j _
          rw [Nat.cast_add, Nat.cast_one, eq_sub_iff_add_eq]
        rw [hset]
        have hcard := card_filter_natCast_eq_le H (-r - 1)
        have hcast : (((Finset.range H).filter
            (fun j : ℕ => (j : ZMod (p : ℕ)) = -r - 1)).card : ℝ)
            ≤ ((H / (p : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
        have hdiv : ((H / (p : ℕ) : ℕ) : ℝ) ≤ (H : ℝ) / (p : ℝ) := Nat.cast_div_le
        push_cast at hcast
        linarith

/-- The `[lo, hi]` box form of the deterministic bound: `G_p(v)(r) ∈ [-(H/p+1), H/p+1]`. -/
lemma fBridgeG_mem_Icc {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (p : primeWindow eps H)
    (r : ZMod (p : ℕ)) :
    fBridgeG eps H v p r ∈ Set.Icc (-((H : ℝ) / (p : ℝ) + 1)) ((H : ℝ) / (p : ℝ) + 1) :=
  Set.mem_Icc.mpr (abs_le.mp (fBridgeG_abs_le eps H hv p r))

/-! ## The residue-sum identity (piece 3 substrate) -/

/-- **Summing `G_p(v)` over all residues collapses the indicator** (piece 3 substrate):
`∑_{r ∈ ZMod p} G_p(v)(r) = ∑_j v_j·v_{j+p}` — for each `j` exactly one residue `r = -j`
fires the gate.  This is the numerator of the per-coordinate expectation. -/
lemma fBridgeG_sum_over_residues {v : Fin H → ℤ} (p : primeWindow eps H) :
    ∑ r : ZMod (p : ℕ), fBridgeG eps H v p r
      = ∑ j ∈ Finset.range H, (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ) := by
  classical
  unfold fBridgeG
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hcond : ∀ r : ZMod (p : ℕ),
      (((j + 1 : ℕ) : ZMod (p : ℕ)) = -r) ↔ (r = -((j + 1 : ℕ) : ZMod (p : ℕ))) := by
    intro r; constructor <;> (intro h; rw [h, neg_neg])
  calc ∑ r : ZMod (p : ℕ), (if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ) else 0)
      = ∑ r : ZMod (p : ℕ), (if r = -((j + 1 : ℕ) : ZMod (p : ℕ)) then
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun r _ => ?_); rw [if_congr (hcond r) rfl rfl]
    _ = (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ) := by
        rw [Finset.sum_ite_eq' Finset.univ (-((j + 1 : ℕ) : ZMod (p : ℕ)))]; simp

/-! ## The variance proxy (piece 4, exponent substrate) -/

/-- Per-prime Hoeffding half-width, simplified: the box `[-(H/p+1), H/p+1]` gives
`(‖hi - lo‖₊ / 2)² = (H/p + 1)²` (real cast). -/
lemma fBridge_varTerm (p : primeWindow eps H) :
    (((‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)
      = ((H : ℝ) / (p : ℝ) + 1) ^ 2 := by
  have hz : ((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1) = 2 * ((H : ℝ) / (p : ℝ) + 1) := by
    ring
  rw [hz, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((H : ℝ) / (p : ℝ) + 1))]
  ring

/-- The window bound `p > ε²H/2` (over ℝ), read from the prime window membership. -/
lemma window_lb (p : primeWindow eps H) :
    (eps : ℝ) ^ 2 * (H : ℝ) / 2 < (p : ℝ) := by
  have h := (mem_primeWindow.mp p.2).2.2
  have : ((eps ^ 2 * (H : ℚ) / 2 : ℚ) : ℝ) < ((p : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at this
  linarith

/-- **The variance-proxy bound** (piece 4).  The Hoeffding denominator sum is bounded
by the explicit `(ε²H + 1)·(2/ε² + 1)²`: each window prime `p > ε²H/2` gives
`H/p + 1 < 2/ε² + 1`, and `|𝒫_H| ≤ ε²H + 1`. -/
lemma fBridge_var_le (heps : 0 < eps) :
    ((∑ p : primeWindow eps H,
        (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)
      ≤ ((eps : ℝ) ^ 2 * (H : ℝ) + 1) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by
  have heps2 : (0 : ℝ) < (eps : ℝ) ^ 2 := by positivity
  have hB0 : (0 : ℝ) ≤ (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by positivity
  rw [NNReal.coe_sum]
  -- per-term: (H/p+1)^2 ≤ (2/eps²+1)^2
  have hterm : ∀ p : primeWindow eps H,
      (((‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)
        ≤ (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by
    intro p
    rw [fBridge_varTerm eps H p]
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primeWindow p.2).pos
    have hle : (H : ℝ) / (p : ℝ) ≤ 2 / (eps : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hp0 heps2]
      nlinarith [window_lb eps H p]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc ∑ p : primeWindow eps H,
        (((‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)
      ≤ ∑ _p : primeWindow eps H, (2 / (eps : ℝ) ^ 2 + 1) ^ 2 :=
        Finset.sum_le_sum (fun p _ => hterm p)
    _ = ((primeWindow eps H).card : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ ((eps : ℝ) ^ 2 * (H : ℝ) + 1) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hB0
        have hcard := primeWindow_card_le eps H
        have hfloor : ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
          have h0 : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
          calc ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℝ)
              = ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℚ) : ℝ) := by norm_cast
            _ ≤ ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) := by exact_mod_cast Nat.floor_le h0
            _ = (eps : ℝ) ^ 2 * (H : ℝ) := by push_cast; ring
        have : ((primeWindow eps H).card : ℝ) ≤ (⌊eps ^ 2 * (H : ℚ)⌋₊ : ℝ) + 1 := by
          exact_mod_cast hcard
        linarith

/-! ## The concentration corollary (piece 4) -/

/-- **The raw concentration bound** (piece 4a): the direct instantiation of
`hoeffding_residueProj` at `G = fBridgeG eps H v` with the deterministic box.  For
every pattern `v` (`‖·‖ ≤ 1`) and threshold `δ ≥ 0`, `F(v)` concentrates around its
mean with the Hoeffding tail whose denominator is `2·∑_p (‖hi_p - lo_p‖/2)²`. -/
theorem fBridge_concentration_raw {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF eps H v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG eps H v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 / (2 * ((∑ p : primeWindow eps H,
          (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) :=
  hoeffding_residueProj eps H (fBridgeG eps H v) (fun i x => fBridgeG_mem_Icc eps H hv i x) hδ

/-- **The usable concentration bound** (piece 4b): the honest explicit exponent.  For
`ε > 0`, a nonempty window, pattern `v` (`‖·‖ ≤ 1`) and threshold `δ ≥ 0`,
`P_y(|F(v,y) − E_y F| ≥ δ) ≤ 2·exp(−δ² / (2·(ε²H+1)·(2/ε²+1)²))`.
For the calibrated threshold `δ = ε²H/log H` this is `2·exp(−Θ(ε⁶ H / log²H))` (see the
module note); the variance-proxy bound `fBridge_var_le` supplies `∑_p B_p² ≤ (ε²H+1)(2/ε²+1)²`
and Hoeffding-tail monotonicity carries it to the explicit denominator. -/
theorem fBridge_concentration {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF eps H v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG eps H v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 /
          (2 * (((eps : ℝ) ^ 2 * (H : ℝ) + 1) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2))) := by
  refine le_trans (fBridge_concentration_raw eps H hv hδ) ?_
  have hSpos : 0 < ((∑ p : primeWindow eps H,
      (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_sum]
    haveI : Nonempty (primeWindow eps H) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    refine Finset.sum_pos (fun p _ => ?_) Finset.univ_nonempty
    rw [fBridge_varTerm eps H p]; positivity
  have hSle := fBridge_var_le eps H heps
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  rw [neg_div, neg_div, neg_le_neg_iff,
      div_le_div_iff₀ (by positivity) (mul_pos (by norm_num) hSpos)]
  nlinarith [sq_nonneg δ, hSle, hSpos]

/-! ## The mean identity (piece 3) -/

/-- **Each residue fiber has `P_H/p` points** (piece 3 substrate).  `residueProj p` is a
surjective additive-group hom between finite groups, so all its fibers are equinumerous
(`AddMonoidHom.card_fiber_eq_of_mem_range`); the `p` equal fibers partition `ZMod P_H`, so
each has `P_H/p` points. -/
lemma residueProj_fiber_card (p : primeWindow eps H) (r : ZMod (p : ℕ)) :
    (Finset.univ.filter (fun ω : ZMod (PH eps H) => residueProj eps H p ω = r)).card
      = PH eps H / (p : ℕ) := by
  classical
  have hsurj : Function.Surjective (residueProj eps H p) :=
    ZMod.castHom_surjective (dvd_PH eps H p)
  have hrange : ∀ r' : ZMod (p : ℕ), r' ∈ Set.range (residueProj eps H p) := fun r' => hsurj r'
  set k := (Finset.univ.filter (fun ω : ZMod (PH eps H) => residueProj eps H p ω = r)).card with hk
  have heq : ∀ r' : ZMod (p : ℕ),
      (Finset.univ.filter (fun ω : ZMod (PH eps H) => residueProj eps H p ω = r')).card = k := by
    intro r'
    have h := AddMonoidHom.card_fiber_eq_of_mem_range (residueProj eps H p).toAddMonoidHom
      (hrange r') (hrange r)
    rw [hk]; simpa using h
  have hfw : (Finset.univ : Finset (ZMod (PH eps H))).card
      = ∑ r' : ZMod (p : ℕ),
          (Finset.univ.filter (fun ω => residueProj eps H p ω = r')).card :=
    Finset.card_eq_sum_card_fiberwise (fun ω _ => Finset.mem_univ _)
  rw [Finset.card_univ, ZMod.card] at hfw
  have hsum : PH eps H = (p : ℕ) * k := by
    rw [hfw]
    simp only [heq, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  rw [hsum, Nat.mul_div_cancel_left k (prime_of_mem_primeWindow p.2).pos]

/-- **The mean identity** (piece 3): under the model uniform measure, the per-prime
component's expectation is the per-coordinate diagonal
`E_y[G_p(v)(y mod p)] = (1/p)·∑_j v_j·v_{j+p}`.  Each residue class equidistributes
(fiber `= P_H/p`), and summing `G_p` over residues collapses the gate to `∑_j v_j v_{j+p}`. -/
lemma fBridgeG_mean {v : Fin H → ℤ} (p : primeWindow eps H) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
        fBridgeG eps H v p (residueProj eps H p ω)]
      = (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ) := by
  classical
  set μ := uniformOn (Set.univ : Set (ZMod (PH eps H))) with hμ
  haveI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  have hmass : ∀ ω : ZMod (PH eps H), μ.real {ω} = ((PH eps H : ℝ))⁻¹ := by
    intro ω
    have hs : μ {ω} = ((PH eps H : ℝ≥0∞))⁻¹ := by
      rw [hμ, uniformOn_univ, Measure.count_singleton, ZMod.card]; simp
    rw [measureReal_def, hs, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [integral_fintype Integrable.of_finite]
  simp only [hmass, smul_eq_mul]
  rw [← Finset.mul_sum]
  have hfib : ∑ ω : ZMod (PH eps H), fBridgeG eps H v p (residueProj eps H p ω)
      = ∑ r : ZMod (p : ℕ), (PH eps H / (p : ℕ)) • fBridgeG eps H v p r := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (ZMod (p : ℕ))))
        (fun ω _ => Finset.mem_univ (residueProj eps H p ω))
        (fun ω => fBridgeG eps H v p (residueProj eps H p ω))]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_congr rfl (fun ω hω =>
      show fBridgeG eps H v p (residueProj eps H p ω) = fBridgeG eps H v p r by
        rw [(Finset.mem_filter.mp hω).2]), Finset.sum_const, residueProj_fiber_card]
  rw [hfib]
  simp only [nsmul_eq_mul]
  rw [← Finset.mul_sum, fBridgeG_sum_over_residues]
  have hpp0 : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (prime_of_mem_primeWindow p.2).pos.ne'
  have harith : (PH eps H : ℝ)⁻¹ * ((PH eps H / (p : ℕ) : ℕ) : ℝ) = 1 / (p : ℝ) := by
    rw [Nat.cast_div (dvd_PH eps H p) hpp0]
    have hp0 : (PH eps H : ℝ) ≠ 0 := by exact_mod_cast (PH_pos eps H).ne'
    field_simp
  rw [← mul_assoc, harith]

/-! ## The sharp concentration corollary (W2-b′, log-Chowla spine upgrade) -/

/-- **The sharp variance-proxy bound** (W2-b′, the single spot).  Replacing the trivial
window count `card ≤ ε²H + 1` used by `fBridge_var_le` with the Chebyshev/PNT-grade count
`card ≤ C₀·ε²H/log H` (hypothesis `hcard`, the output shape of node W3-c-pnt) sharpens the
Hoeffding denominator sum `∑_p (H/p+1)²` to `C₀·(ε²H/log H)·(2/ε²+1)²` — one power of
`log H` lighter than `(ε²H+1)·(2/ε²+1)²`.  The per-prime bound `(H/p+1)² ≤ (2/ε²+1)²`
(from `p > ε²H/2`) is reused verbatim; only the final cardinality factor changes. -/
lemma fBridge_var_le_sharp (heps : 0 < eps) {C₀ : ℝ}
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) :
    ((∑ p : primeWindow eps H,
        (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)
      ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
          * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by
  have heps2 : (0 : ℝ) < (eps : ℝ) ^ 2 := by positivity
  have hB0 : (0 : ℝ) ≤ (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by positivity
  rw [NNReal.coe_sum]
  have hterm : ∀ p : primeWindow eps H,
      (((‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)
        ≤ (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by
    intro p
    rw [fBridge_varTerm eps H p]
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primeWindow p.2).pos
    have hle : (H : ℝ) / (p : ℝ) ≤ 2 / (eps : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hp0 heps2]
      nlinarith [window_lb eps H p]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc ∑ p : primeWindow eps H,
        (((‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)
      ≤ ∑ _p : primeWindow eps H, (2 / (eps : ℝ) ^ 2 + 1) ^ 2 :=
        Finset.sum_le_sum (fun p _ => hterm p)
    _ = ((primeWindow eps H).card : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard hB0

/-- **The sharp usable concentration bound** (W2-b′): the Tao-grade exponent.  With the
PNT-grade window count `hcard : |𝒫_H| ≤ C₀·ε²H/log H` (node W3-c-pnt's output shape) and
`1 ≤ log H`, the F-bridge concentrates as
`P_y(|F(v,y) − E_y F| ≥ δ) ≤ 2·exp(−δ²·log H / (2 C₀ ε²H (2/ε²+1)²))`.  At the calibrated
threshold `δ = ε²H/log H` the exponent equals `ε²H / (2 C₀ log H (2/ε²+1)²)`, which is
`≥ ε⁶H/(18·C₀·log H)` for `0 < ε ≤ 1` (absolute `c = 18`, via `(2/ε²+1)² ≤ 9/ε⁴`): ONE
power of `log H`, not the `log²H` of `fBridge_concentration`.  This is the grade the tower
telescope can fund (`Σ 1/(n log n)` diverges, `Σ 1/(n log²n)` converges). -/
theorem fBridge_concentration_sharp {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ)) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF eps H v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG eps H v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 * Real.log (H : ℝ) /
          (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2)) := by
  refine le_trans (fBridge_concentration_raw eps H hv hδ) ?_
  set D := 2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 with hDdef
  set S := ((∑ p : primeWindow eps H,
      (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) with hSdef
  have hepsne : (eps : ℝ) ≠ 0 := by exact_mod_cast heps.ne'
  have hlogpos : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlog
  have hlogne : Real.log (H : ℝ) ≠ 0 := hlogpos.ne'
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    rcases Nat.eq_zero_or_pos H with h | h
    · exfalso; rw [h, Nat.cast_zero, Real.log_zero] at hlog; linarith
    · exact_mod_cast h
  have hSpos : 0 < S := by
    rw [hSdef, NNReal.coe_sum]
    haveI : Nonempty (primeWindow eps H) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    refine Finset.sum_pos (fun p _ => ?_) Finset.univ_nonempty
    rw [fBridge_varTerm eps H p]; positivity
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hSle : S ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
      * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by
    rw [hSdef]; exact fBridge_var_le_sharp eps H heps hcard
  have hkey : 2 * S * Real.log (H : ℝ) ≤ D := by
    have hmul : 2 * S * Real.log (H : ℝ)
        ≤ 2 * (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
            * (2 / (eps : ℝ) ^ 2 + 1) ^ 2) * Real.log (H : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hlogpos.le
      exact mul_le_mul_of_nonneg_left hSle (by norm_num)
    refine hmul.trans_eq ?_
    rw [hDdef]; field_simp
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  rw [div_le_div_iff₀ (mul_pos (by norm_num) hSpos) hDpos]
  nlinarith [sq_nonneg δ, hkey]

/-- **The sharp decoupled-mean corollary** (W2-b′, mirroring `fBridge_concentration_decoupled`).
Substituting the decoupled `y`-mean `∑_p (1/p) ∑_j v_j v_{j+p}` (via `fBridgeG_mean`) into
`fBridge_concentration_sharp`: `F` deviates from the two-point correlation by `≥ δ` with
probability `≤ 2·exp(−δ²·log H / (2 C₀ ε²H (2/ε²+1)²))`, the one-log Tao grade. -/
theorem fBridge_concentration_decoupled_sharp
    {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ)) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF eps H v ω - ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
            ∑ j ∈ Finset.range H,
              (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ)|}
      ≤ 2 * Real.exp (-δ ^ 2 * Real.log (H : ℝ) /
          (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2)) := by
  have hmean : (∑ p : primeWindow eps H,
        (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
          fBridgeG eps H v p (residueProj eps H p ω)])
      = ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ) :=
    Finset.sum_congr rfl (fun p _ => fBridgeG_mean eps H p)
  have h := fBridge_concentration_sharp eps H hv heps hne hδ hC₀ hcard hlog
  rw [hmean] at h
  exact h

/-! ## The shift-`h` family (W-F3 wave A: definitions + the offset-agnostic bounds)

Tao's (3.14) carries a shift parameter `h`: the second factor is `x_{2,j+ph}`.  `fBridgeG` /
`fBridgeF` above are that object frozen at `h = 1` (the module header and `fBridgeG`'s own
docstring name `h = 1` among the model values).  The definitions below reopen exactly that
parameter; the `h = 1` originals stay byte-frozen and are recovered by `fBridgeG_h_one` /
`fBridgeF_h_one`.

⚠️ **WHICH `1` IS THE SHIFT — the trap this port had to walk past.**  `fBridgeG`'s gate reads
`((j + 1 : ℕ) : ZMod p) = -r`, and the `1` in it is NOT the shift parameter: it is the
1-INDEXING OFFSET of the window (`windowVal H (liouvilleWindow H n) j = λ(n+j+1)`, so Tao's
1-indexed `j` is our `j + 1`).  Tao's indicator `1_{ay+j ≡ pb (mod ap)}` contains no `h` at
all; at `a = 1, b = 0` it is `p ∣ y + j`, a condition on the FIRST factor's argument only.
The corpus proves this in the kernel: `fBridgeF_liouville_apply` (`Prop26.lean:87`) evaluates
the gate to `p ∣ n + j + 1`, and it must stay there, because the whole point of the gate is to
feed multiplicativity — with `n+j+1 = p·m` one gets `λ(p m)·λ(p m + p h) = λ(m)·λ(m + h)`,
the shift-`h` correlation.  Gating on `p ∣ n + j + h` instead would leave `λ(n+j+1)` with no
factor of `p` and kill the reduction.

So **the gate below is `(j + 1)`, unchanged, and ONLY the second factor's index carries `h`.**
The two spellings coincide at `h = 1`, so NO `h = 1` compat lemma can tell them apart —
the same tripwire shape recorded for the twist in `ShiftFork`.

**Scope.**  Only the DEFINITIONS and the deterministic `|windowVal| ≤ 1` triangle bounds are
ported here, because only those are offset-agnostic: every term of the gated sum has modulus
`≤ 1` whatever `h` is, and the gate does not mention `h`, so `card_filter_natCast_eq_le`
applies at `-r - 1` verbatim.  The concentration/entropy cone (`fBridgeG_mean`, `badSet`,
`outer_combine` and the sharp Hoeffding corollaries) is NOT offset-agnostic and is
deliberately untouched. -/

/-- **The per-prime component at shift `h`** — Tao's `F_p` (3.14) with the offset multiplier
reopened: `G_{p,h}(v)(r) = ∑_j 1_{(j+1 : ZMod p) = -r} · v_j · v_{j+p·h}`.  The gate is the
`h`-free divisibility condition on the base index (see the section note above); `fBridgeG` is
the `h = 1` member (`fBridgeG_h_one`). -/
noncomputable def fBridgeG_h (h : ℕ) (v : Fin H → ℤ) (p : primeWindow eps H) :
    ZMod (p : ℕ) → ℝ :=
  fun r => ∑ j ∈ Finset.range H,
    if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then
      (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0

/-- **The assembly at shift `h`**: `∑_{p ∈ 𝒫_H} G_{p,h}(v) ∘ residueProj p`.  Same shape as
`fBridgeF`, so the `∑_i G_i (proj_i ·)` form `hoeffding_residueProj` centers on survives. -/
noncomputable def fBridgeF_h (h : ℕ) (v : Fin H → ℤ) : ZMod (PH eps H) → ℝ :=
  fun y => ∑ p : primeWindow eps H, fBridgeG_h eps H h v p (residueProj eps H p y)

/-- **The `h = 1` compat for `G`.**  NOT `rfl`-grade: `(p : ℕ) * 1` whnf-reduces to `0 + p`,
which is stuck for a variable `p` (`Nat.mul` recurses on its SECOND argument and `Nat.add` on
its second too), so the window index needs `Nat.mul_one` to line up.  The gate is `h`-free,
so only the product index moves — and that is also why this lemma CANNOT certify the gate's
spelling (see the section note). -/
theorem fBridgeG_h_one (v : Fin H → ℤ) (p : primeWindow eps H) :
    fBridgeG_h eps H 1 v p = fBridgeG eps H v p := by
  funext r
  unfold fBridgeG_h fBridgeG
  exact Finset.sum_congr rfl (fun j _ => by rw [Nat.mul_one])

/-- **The `h = 1` compat for `F`.**  Termwise from `fBridgeG_h_one`. -/
theorem fBridgeF_h_one (v : Fin H → ℤ) : fBridgeF_h eps H 1 v = fBridgeF eps H v := by
  funext y
  unfold fBridgeF_h fBridgeF
  exact Finset.sum_congr rfl (fun p _ => by rw [fBridgeG_h_one])

/-- **The deterministic box bound at shift `h`** — the offset-agnostic port of
`fBridgeG_abs_le`: `|G_{p,h}(v)(r)| ≤ H/p + 1` for a `‖·‖ ≤ 1` pattern, for EVERY `h`.
Each surviving term still has modulus `≤ 1` (`windowVal_prod_abs_le` reads no offset), and
the gate is the same single residue class `j ≡ -r - 1 (p)` as at `h = 1`, meeting the window
`[0,H)` in at most `H/p + 1` points.  The `h = 1` proof script survives verbatim. -/
lemma fBridgeG_h_abs_le (h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (p : primeWindow eps H)
    (r : ZMod (p : ℕ)) :
    |fBridgeG_h eps H h v p r| ≤ (H : ℝ) / (p : ℝ) + 1 := by
  classical
  unfold fBridgeG_h
  calc |∑ j ∈ Finset.range H, if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0|
      ≤ ∑ j ∈ Finset.range H, |if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range H, if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs with hj
        · exact windowVal_prod_abs_le hv j (j + (p : ℕ) * h)
        · simp
    _ = (((Finset.range H).filter
          (fun j : ℕ => ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r)).card : ℝ) := by
        rw [Finset.sum_boole]
    _ ≤ (H : ℝ) / (p : ℝ) + 1 := by
        have hset : (Finset.range H).filter (fun j : ℕ => ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r)
            = (Finset.range H).filter (fun j : ℕ => (j : ZMod (p : ℕ)) = -r - 1) := by
          apply Finset.filter_congr
          intro j _
          rw [Nat.cast_add, Nat.cast_one, eq_sub_iff_add_eq]
        rw [hset]
        have hcard := card_filter_natCast_eq_le H (-r - 1)
        have hcast : (((Finset.range H).filter
            (fun j : ℕ => (j : ZMod (p : ℕ)) = -r - 1)).card : ℝ)
            ≤ ((H / (p : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
        have hdiv : ((H / (p : ℕ) : ℕ) : ℝ) ≤ (H : ℝ) / (p : ℝ) := Nat.cast_div_le
        push_cast at hcast
        linarith

/-- The `[lo, hi]` box form at shift `h`: `G_{p,h}(v)(r) ∈ [-(H/p+1), H/p+1]`. -/
lemma fBridgeG_h_mem_Icc (h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (p : primeWindow eps H)
    (r : ZMod (p : ℕ)) :
    fBridgeG_h eps H h v p r ∈ Set.Icc (-((H : ℝ) / (p : ℝ) + 1)) ((H : ℝ) / (p : ℝ) + 1) :=
  Set.mem_Icc.mpr (abs_le.mp (fBridgeG_h_abs_le eps H h hv p r))

/-! ## The mean and concentration cone at shift `h` (W-F3 wave B, nodes B-2/B-3)

Wave A stopped at the deterministic box and said so ("no `fBridgeG_h_mean`, no
`fBridgeG_h_sum_over_residues`, no `fBridge_concentration*` at `h`").  This section crosses
that boundary for the mean/concentration half.

WHAT IS AND IS NOT OFFSET-SENSITIVE, measured rather than assumed.  The Hoeffding substrate
is entirely `h`-free: `residueProj_fiber_card` never mentions the pattern `v`, and
`fBridge_varTerm` / `window_lb` / `fBridge_var_le` / `fBridge_var_le_sharp` are statements
about the window primes and the box endpoints only.  All four are REUSED VERBATIM below —
they need no `_h` port.  What does carry the offset is exactly the two places the product
index is written out: `fBridgeG_sum_over_residues` (the mean's numerator) and the decoupled
spellings of the mean.  Every proof script transfers unchanged, because the gate is `h`-free
and `windowVal_prod_abs_le` is offset-blind.

⚠️ SITE 2 OF THE THREE SYNCHRONISED SITES.  `fBridge_h_concentration_decoupled` and
`fBridge_h_concentration_decoupled_sharp` (and `fBridgeF_h_mean` in `Decoupled`) spell the
deviation/mean offset independently of `badSet_h`.  They use wave A's fixed target spelling
`windowVal H v (j + (p : ℕ) * h)` verbatim.  Site 3 — `outer_combine`'s own conclusion — is
still at `j + (p : ℕ)` and is node B-4's obligation, not this one's.

THE `h = 1` RECOVERIES, MEASURED WITH NEGATIVE CONTROLS.  These are theorems, not
definitions, so there is no compat EQUATION to state; the obligation is that the `h = 1`
instance recovers the frozen original.  It does, and it is never `rfl`: each recovery needs
exactly TWO rewrites, but WHICH two depends on the spelling the statement carries.
`fBridgeG_h_sum_over_residues` / `fBridgeG_h_mean` need `fBridgeG_h_one` + `Nat.mul_one`;
`fBridgeF_h_mean` and the decoupled concentrations need `fBridgeF_h_one` + `Nat.mul_one`;
the UN-decoupled `fBridge_h_concentration*` carry no product index at all and instead need
`fBridgeF_h_one` + `fBridgeG_h_one`, with `Nat.mul_one` doing nothing.  Each drop was run:
omitting `Nat.mul_one` leaves `j + ↑p * 1` against `j + ↑p`; omitting the bridge lemma leaves
`fBridgeG_h eps H 1 v p` (resp. `fBridgeF_h eps H 1 v`) against the frozen name. -/

/-- **The residue-sum identity at shift `h`** (mean substrate).  `∑_{r ∈ ZMod p} G_{p,h}(v)(r)
= ∑_j v_j·v_{j+p·h}` — for each `j` exactly one residue `r = -j` fires the gate, and the gate
does not mention `h`, so the `h = 1` collapse argument applies verbatim; only the value being
summed carries the offset.  `fBridgeG_sum_over_residues` is the `h = 1` member. -/
lemma fBridgeG_h_sum_over_residues (h : ℕ) {v : Fin H → ℤ} (p : primeWindow eps H) :
    ∑ r : ZMod (p : ℕ), fBridgeG_h eps H h v p r
      = ∑ j ∈ Finset.range H,
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) := by
  classical
  unfold fBridgeG_h
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hcond : ∀ r : ZMod (p : ℕ),
      (((j + 1 : ℕ) : ZMod (p : ℕ)) = -r) ↔ (r = -((j + 1 : ℕ) : ZMod (p : ℕ))) := by
    intro r; constructor <;> (intro hh; rw [hh, neg_neg])
  calc ∑ r : ZMod (p : ℕ), (if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0)
      = ∑ r : ZMod (p : ℕ), (if r = -((j + 1 : ℕ) : ZMod (p : ℕ)) then
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun r _ => ?_); rw [if_congr (hcond r) rfl rfl]
    _ = (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) := by
        rw [Finset.sum_ite_eq' Finset.univ (-((j + 1 : ℕ) : ZMod (p : ℕ)))]; simp

/-- **The mean identity at shift `h`**: `E_y[G_{p,h}(v)(y mod p)] = (1/p)·∑_j v_j·v_{j+p·h}`.
Same argument as `fBridgeG_mean` — each residue class equidistributes
(`residueProj_fiber_card`, which never sees `v` and is reused verbatim), and summing over
residues collapses the gate via `fBridgeG_h_sum_over_residues`. -/
lemma fBridgeG_h_mean (h : ℕ) {v : Fin H → ℤ} (p : primeWindow eps H) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
        fBridgeG_h eps H h v p (residueProj eps H p ω)]
      = (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) := by
  classical
  set μ := uniformOn (Set.univ : Set (ZMod (PH eps H))) with hμ
  haveI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  have hmass : ∀ ω : ZMod (PH eps H), μ.real {ω} = ((PH eps H : ℝ))⁻¹ := by
    intro ω
    have hs : μ {ω} = ((PH eps H : ℝ≥0∞))⁻¹ := by
      rw [hμ, uniformOn_univ, Measure.count_singleton, ZMod.card]; simp
    rw [measureReal_def, hs, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [integral_fintype Integrable.of_finite]
  simp only [hmass, smul_eq_mul]
  rw [← Finset.mul_sum]
  have hfib : ∑ ω : ZMod (PH eps H), fBridgeG_h eps H h v p (residueProj eps H p ω)
      = ∑ r : ZMod (p : ℕ), (PH eps H / (p : ℕ)) • fBridgeG_h eps H h v p r := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (ZMod (p : ℕ))))
        (fun ω _ => Finset.mem_univ (residueProj eps H p ω))
        (fun ω => fBridgeG_h eps H h v p (residueProj eps H p ω))]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_congr rfl (fun ω hω =>
      show fBridgeG_h eps H h v p (residueProj eps H p ω) = fBridgeG_h eps H h v p r by
        rw [(Finset.mem_filter.mp hω).2]), Finset.sum_const, residueProj_fiber_card]
  rw [hfib]
  simp only [nsmul_eq_mul]
  rw [← Finset.mul_sum, fBridgeG_h_sum_over_residues]
  have hpp0 : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (prime_of_mem_primeWindow p.2).pos.ne'
  have harith : (PH eps H : ℝ)⁻¹ * ((PH eps H / (p : ℕ) : ℕ) : ℝ) = 1 / (p : ℝ) := by
    rw [Nat.cast_div (dvd_PH eps H p) hpp0]
    have hp0 : (PH eps H : ℝ) ≠ 0 := by exact_mod_cast (PH_pos eps H).ne'
    field_simp
  rw [← mul_assoc, harith]

/-- **The raw concentration bound at shift `h`**: `hoeffding_residueProj` instantiated at
`G = fBridgeG_h eps H h v` with the SAME deterministic box, which `fBridgeG_h_mem_Icc`
(wave A) already supplies at every `h`.  `fBridgeF_h` is defeq to the `∑_i G_i (proj_i ·)`
shape Hoeffding centers on, so the `h = 1` proof term transfers with the name changed. -/
theorem fBridge_h_concentration_raw (h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_h eps H h v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG_h eps H h v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 / (2 * ((∑ p : primeWindow eps H,
          (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) :=
  hoeffding_residueProj eps H (fBridgeG_h eps H h v)
    (fun i x => fBridgeG_h_mem_Icc eps H h hv i x) hδ

/-- **The usable concentration bound at shift `h`**: the explicit exponent
`2·exp(−δ² / (2·(ε²H+1)·(2/ε²+1)²))`, unchanged from `h = 1`.  The variance proxy is a
statement about the window primes and the box endpoints alone, so `fBridge_var_le` is reused
verbatim; only the bridge's name moves. -/
theorem fBridge_h_concentration (h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_h eps H h v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG_h eps H h v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 /
          (2 * (((eps : ℝ) ^ 2 * (H : ℝ) + 1) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2))) := by
  refine le_trans (fBridge_h_concentration_raw eps H h hv hδ) ?_
  have hSpos : 0 < ((∑ p : primeWindow eps H,
      (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_sum]
    haveI : Nonempty (primeWindow eps H) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    refine Finset.sum_pos (fun p _ => ?_) Finset.univ_nonempty
    rw [fBridge_varTerm eps H p]; positivity
  have hSle := fBridge_var_le eps H heps
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  rw [neg_div, neg_div, neg_le_neg_iff,
      div_le_div_iff₀ (by positivity) (mul_pos (by norm_num) hSpos)]
  nlinarith [sq_nonneg δ, hSle, hSpos]

/-- **The sharp concentration bound at shift `h`** (the W2-b′ one-log Tao grade, ported).
With the PNT-grade window count `hcard` and `1 ≤ log H`, `F_h` concentrates as
`2·exp(−δ²·log H / (2 C₀ ε²H (2/ε²+1)²))`.  `fBridge_var_le_sharp` is `v`- and `h`-free and
is reused verbatim; the exponent is IDENTICAL to the `h = 1` one, which is the point — the
shift costs nothing in the concentration grade. -/
theorem fBridge_h_concentration_sharp (h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ)) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_h eps H h v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG_h eps H h v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 * Real.log (H : ℝ) /
          (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2)) := by
  refine le_trans (fBridge_h_concentration_raw eps H h hv hδ) ?_
  set D := 2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 with hDdef
  set S := ((∑ p : primeWindow eps H,
      (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) with hSdef
  have hepsne : (eps : ℝ) ≠ 0 := by exact_mod_cast heps.ne'
  have hlogpos : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlog
  have hlogne : Real.log (H : ℝ) ≠ 0 := hlogpos.ne'
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    rcases Nat.eq_zero_or_pos H with hh | hh
    · exfalso; rw [hh, Nat.cast_zero, Real.log_zero] at hlog; linarith
    · exact_mod_cast hh
  have hSpos : 0 < S := by
    rw [hSdef, NNReal.coe_sum]
    haveI : Nonempty (primeWindow eps H) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    refine Finset.sum_pos (fun p _ => ?_) Finset.univ_nonempty
    rw [fBridge_varTerm eps H p]; positivity
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hSle : S ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
      * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by
    rw [hSdef]; exact fBridge_var_le_sharp eps H heps hcard
  have hkey : 2 * S * Real.log (H : ℝ) ≤ D := by
    have hmul : 2 * S * Real.log (H : ℝ)
        ≤ 2 * (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
            * (2 / (eps : ℝ) ^ 2 + 1) ^ 2) * Real.log (H : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hlogpos.le
      exact mul_le_mul_of_nonneg_left hSle (by norm_num)
    refine hmul.trans_eq ?_
    rw [hDdef]; field_simp
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  rw [div_le_div_iff₀ (mul_pos (by norm_num) hSpos) hDpos]
  nlinarith [sq_nonneg δ, hkey]

/-- **The sharp decoupled-mean corollary at shift `h`** — ⚠️ SITE 2 of the three synchronised
offset spellings.  Substituting the shifted decoupled `y`-mean
`∑_p (1/p) ∑_j v_j v_{j+p·h}` (via `fBridgeG_h_mean`) into `fBridge_h_concentration_sharp`.
The deviation set is written with wave A's fixed spelling `windowVal H v (j + (p : ℕ) * h)`,
byte-identical to `badSet_h`'s (site 1). -/
theorem fBridge_h_concentration_decoupled_sharp (h : ℕ)
    {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ)) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_h eps H h v ω - ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
            ∑ j ∈ Finset.range H,
              (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ)|}
      ≤ 2 * Real.exp (-δ ^ 2 * Real.log (H : ℝ) /
          (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2)) := by
  have hmean : (∑ p : primeWindow eps H,
        (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
          fBridgeG_h eps H h v p (residueProj eps H p ω)])
      = ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) :=
    Finset.sum_congr rfl (fun p _ => fBridgeG_h_mean eps H h p)
  have hq := fBridge_h_concentration_sharp eps H h hv heps hne hδ hC₀ hcard hlog
  rw [hmean] at hq
  exact hq

end Salt.Entropy.Chowla
