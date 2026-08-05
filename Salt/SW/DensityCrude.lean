/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.EFSharpMult

/-!
# THE FULCRUM CAMPAIGN, node N2 — **the crude zero-density input**

Heath-Brown 1983 spends a zero-density theorem at exactly one site: p.209, inside the proof of
his Lemma 7, where the explicit formula's zero sum is cut at `σ = 4/5` and the surviving zeros
are split at height `|ρ| = q²`. Above that height he quotes Jutila [11, Theorem 1],

    N(σ, T, χ) ≪ (qT)^{(5/2)(1−σ)}        (4/5 ≤ σ ≤ 1),                       (4.9)

to conclude that the `|ρ| ≥ q²` zeros contribute `≪ q^{−1/2}` (4.10); below that height the
Deuring–Heilbronn repulsion supplies `β ≤ σ₀ ≤ 1 − AL^{−1}log η` and the contribution is
`≪ Lη^{−A}`. The road's own tolerance analysis (⟦N0 CLEAR⟧) rules that **any** density exponent
`D ≤ 83` closes the budget — Jutila's `5/2` carries ≈ 33× more than is needed.

## The route taken, said plainly

⟦N0 CLEAR⟧ also ruled that the campaign's explicit formula is truncated at **polylog height**
`T = efHeight q = (log q + 2)⁴`, not at `q²` (`T = q²` is independently not viable: the band top
collapses to `q^{−0.059}`). At polylog height the *trivial* count already beats the density
shape, because N1's landed half-box supply (`LFunction_halfbox_zero_count`, counted with
multiplicity through `efMultTotal_halfbox_le`) gives `≈ 133·log(q(|t₀|+2))` zeros per unit
window, hence `≪ T log(qT)` in the whole box — and `T log(qT)` is **polylog in q** here.

So this node's "density theorem" is a **COUNT**, not a zero-detection argument. That is stated
out loud rather than hidden: `efMultTotal_box_le` batches the landed window count over
`⌈T⌉` unit windows (fibred by `round ∘ Im`), and `zeroCountM_density_crude` then dresses it in
the road's literal shape `N(σ,T,χ) ≤ (qT)^{83(1−σ)}` on `4/5 ≤ σ ≤ 16/17` — with **no constant
and no log factor**, at the minted threshold `q ≥ 8`, `T ≥ 2`. The excluded near-1 strip
`16/17 < σ ≤ 1` is exactly where the count is *constant in σ* while `(qT)^{83(1−σ)} → 1`; there
the road does not use a density at all — the Deuring–Heilbronn repulsion (the TAU-EXT artillery)
takes over, and the shape it feeds is the **spend** below.

## The spend — the actual consumer shape (the exit)

HB never consumes `N(σ,T,χ)` as a statement; he consumes the zero sum weighted by `y^{σ−1}`
against `y ≥ x ≥ q^{250}`. The dyadic-in-`σ` decomposition that a genuine density theorem would
need **collapses** here, because our count is `σ`-independent: `∑_ρ m_ρ y^{Re ρ−1}` is bounded
by (total multiplicity)·`y^{β−1}` at the sup `β = max Re ρ`, and *that* is the exponentially
small factor (the repulsion input), not the count. Hence

* `zeroSum_rpow_le` — `∑_{ρ∈Z} m_ρ·y^{Re ρ−1} ≤ efMultTotal χ Z · y^{β−1}`;
* `efZeroSumM_norm_le` — `‖efZeroSumM χ Z y‖ ≤ efMultTotal χ Z · (y^β / a)` for `a ≤ Re ρ ≤ β`;
* `efZeroSumM_spend_le` / **`efZeroSumM_spend_at_efHeight`** — the same with the count folded in
  at the campaign box, `‖∑_ρ m_ρ y^ρ/ρ‖ ≤ 4110·(log q + 2)⁵·y^β`.

`efZeroSumM_spend_at_efHeight` is N2's deliverable to N3/N4: the EF's zero sum
(`psi_sharp_at_efHeightM`'s only non-error term) is priced by **one** polylog constant times
`y^β`, with `β` the single number the repulsion side must supply.

## Constants minted here

`137` (a numeral for the landed window constant `7/log(39/37) ≈ 132.97`, via `log(39/37) ≥ 2/39`);
`2055 = 137·3·5` (the campaign box's polylog count `2055·(log q + 2)⁵`); `4110 = 2·2055` (the
spend, after `1/σ ≤ 2` on `σ ≥ 1/2`); `D = 83` and the thresholds `q ≥ 8`, `T ≥ 2`, `σ ≤ 16/17`
for the density shape.
-/

open Complex DirichletCharacter Filter Set Metric Function

namespace Salt.SW

/-! ## 1. The window constant as a numeral -/

/-- `log(39/37) ≥ 2/39` — from `log x ≤ x − 1` applied at `x = 37/39`. -/
lemma log_39_37_lower : (2 : ℝ) / 39 ≤ Real.log (39 / 37) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 37 / 39 by norm_num)
  have hlog : Real.log ((37 : ℝ) / 39) = -Real.log (39 / 37) := by
    rw [← Real.log_inv]; norm_num
  have h2 : (37 : ℝ) / 39 - 1 = -(2 / 39) := by norm_num
  rw [hlog, h2] at h
  linarith

/-- **The window constant, as a numeral.** N1's half-box count carries the exact constant
`7/log(39/37) ≈ 132.97`; `137` is the numeral this node batches with (`137·(2/39) > 7`). -/
lemma windowConst_le_137 : 7 / Real.log (39 / 37) ≤ 137 := by
  have hpos : (0 : ℝ) < Real.log (39 / 37) := lt_of_lt_of_le (by norm_num) log_39_37_lower
  rw [div_le_iff₀ hpos]
  linarith [log_39_37_lower]

/-! ## 2. The batching — from N1's unit window to the whole box -/

/-- **THE BOX COUNT (N2's counting half).** For a primitive `χ` mod `q ≥ 2`, any finite set `Z`
of zeros of `L(·,χ)` inside the box `{1/2 ≤ Re ρ ≤ 1, |Im ρ| ≤ T}` has total multiplicity

    ∑_{ρ ∈ Z} m_ρ ≤ (2T+3)·(7/log(39/37))·log(q(T+3)).

Route: fibre `Z` by `j = round (Im ρ) ∈ [−⌈T⌉, ⌈T⌉]`; each fibre lies in the unit window at
`t₀ = j` (since `|Im ρ − round (Im ρ)| ≤ 1/2`), hence inside `closedBall (2+ij) (37/20)`
(`halfbox_subset_closedBall`), where N1's `efMultTotal_halfbox_le` prices it — with
multiplicity, because the landed count counts the analytic divisor. There are at most
`2⌈T⌉+1 ≤ 2T+3` fibres. -/
theorem efMultTotal_box_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {Z : Finset ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hZ0 : ∀ ρ ∈ Z, LFunction χ ρ = 0)
    (hZre : ∀ ρ ∈ Z, 1 / 2 ≤ ρ.re ∧ ρ.re ≤ 1)
    (hZim : ∀ ρ ∈ Z, |ρ.im| ≤ T) :
    efMultTotal χ Z ≤ (2 * T + 3) * ((7 / Real.log (39 / 37)) * Real.log ((q : ℝ) * (T + 3))) := by
  classical
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  set n : ℕ := ⌈T⌉₊ with hn
  have hTn : T ≤ (n : ℝ) := Nat.le_ceil T
  have hnT : (n : ℝ) < T + 1 := Nat.ceil_lt_add_one hT
  set J : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ) with hJ
  set C : ℝ := (7 / Real.log (39 / 37)) * Real.log ((q : ℝ) * (T + 3)) with hC
  have hlogpos : (0 : ℝ) < Real.log (39 / 37) := lt_of_lt_of_le (by norm_num) log_39_37_lower
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hCnn : 0 ≤ C := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) * (T + 3) := by nlinarith
    have := Real.log_nonneg h1
    positivity
  -- the fibre map lands in `J`
  have hmaps : ∀ ρ ∈ Z, round ρ.im ∈ J := by
    intro ρ hρ
    have h1 := abs_sub_round ρ.im
    have h2 := hZim ρ hρ
    have h1' := abs_le.mp h1
    have h2' := abs_le.mp h2
    rw [hJ, Finset.mem_Icc]
    constructor
    · have h5 : ((-(n : ℤ) - 1 : ℤ) : ℝ) < ((round ρ.im : ℤ) : ℝ) := by push_cast; linarith
      have h6 : (-(n : ℤ) - 1 : ℤ) < round ρ.im := by exact_mod_cast h5
      omega
    · have h5 : ((round ρ.im : ℤ) : ℝ) < (((n : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
      have h6 : round ρ.im < (n : ℤ) + 1 := by exact_mod_cast h5
      omega
  -- each fibre is priced by N1's window count
  have hfib : ∀ j ∈ J, efMultTotal χ {ρ ∈ Z | round ρ.im = j} ≤ C := by
    intro j hj
    have hball : ∀ ρ ∈ {ρ ∈ Z | round ρ.im = j},
        ρ ∈ Metric.closedBall (2 + ((j : ℝ) : ℂ) * I) (37 / 20) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρZ, hrj⟩ := hρ
      refine halfbox_subset_closedBall (j : ℝ) ⟨(hZre ρ hρZ).1, (hZre ρ hρZ).2, ?_⟩
      rw [← hrj]
      exact le_trans (abs_sub_round ρ.im) (by norm_num)
    have h := efMultTotal_halfbox_le χ hχ hq (j : ℝ) hball
      (fun ρ hρ => hZ0 ρ (Finset.mem_filter.mp hρ).1)
    refine h.trans ?_
    have hjn := Finset.mem_Icc.mp hj
    have hjabs : |(j : ℝ)| ≤ (n : ℝ) := by
      rw [abs_le]
      constructor
      · have : ((-(n : ℤ) : ℤ) : ℝ) ≤ ((j : ℤ) : ℝ) := by exact_mod_cast hjn.1
        push_cast at this; linarith
      · have : ((j : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast hjn.2
        push_cast at this; linarith
    have hle : (q : ℝ) * (|(j : ℝ)| + 2) ≤ (q : ℝ) * (T + 3) := by nlinarith
    have hposj : (0 : ℝ) < (q : ℝ) * (|(j : ℝ)| + 2) := by positivity
    rw [hC]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hposj hle) (by positivity)
  -- assemble
  have hsum : efMultTotal χ Z = ∑ j ∈ J, efMultTotal χ {ρ ∈ Z | round ρ.im = j} := by
    simp only [efMultTotal]
    exact (Finset.sum_fiberwise_of_maps_to hmaps (fun ρ => (zeroMult χ ρ : ℝ))).symm
  have hcard : ((J.card : ℤ) : ℝ) = 2 * (n : ℝ) + 1 := by
    have h : ((J.card : ℤ)) = (n : ℤ) + 1 - (-(n : ℤ)) := by
      rw [hJ]; exact Int.card_Icc_of_le _ _ (by omega)
    rw [h]; push_cast; ring
  have hcardR : (J.card : ℝ) ≤ 2 * T + 3 := by
    have : (J.card : ℝ) = 2 * (n : ℝ) + 1 := by exact_mod_cast hcard
    rw [this]; linarith
  calc efMultTotal χ Z = ∑ j ∈ J, efMultTotal χ {ρ ∈ Z | round ρ.im = j} := hsum
    _ ≤ ∑ _j ∈ J, C := Finset.sum_le_sum hfib
    _ = (J.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * T + 3) * C := mul_le_mul_of_nonneg_right hcardR hCnn

/-! ## 2b. A3 — THE HARMONIC BATCHING `∑ m_ρ/‖ρ‖` -/

/-- The real-valued partial harmonic sum, as mathlib's `harmonic`. -/
lemma sum_range_inv_succ_eq_harmonic (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1) = (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      push_cast
      ring

/-- **A3 — THE HARMONIC BATCHING (N4b W0-iii).** The `1/‖ρ‖`-weighted zero mass of the box
`{1/2 ≤ Re ρ ≤ 1, |Im ρ| ≤ T}` is a `log(qT)·log T`, not a `T·log(qT)`:

    ∑_{ρ ∈ Z} m_ρ/‖ρ‖ ≤ 137·log(q(T+3))·(8 + 4·log(T+1)).

Route — the same fibring as `efMultTotal_box_le` (`j = round (Im ρ)`, each fibre priced at
`≈ 133·log(q(T+3))` by N1's landed unit-window count), but the fibre's *weight* is now read off
its height: `‖ρ‖ ≥ max(|j|,1)/2`, because `‖ρ‖ ≥ |Im ρ| ≥ |j| − 1/2` and `‖ρ‖ ≥ Re ρ ≥ 1/2`.
Summing `2/max(|j|,1)` over `|j| ≤ ⌈T⌉` is twice a harmonic sum, and mathlib's
`harmonic_le_one_add_log` closes it. **No new analytic input**: this is the landed window count
plus `∑_{k≤n} 1/k ≤ 1 + log n`. -/
theorem efMultHarmonic_box_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {Z : Finset ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hZ0 : ∀ ρ ∈ Z, LFunction χ ρ = 0)
    (hZre : ∀ ρ ∈ Z, 1 / 2 ≤ ρ.re ∧ ρ.re ≤ 1)
    (hZim : ∀ ρ ∈ Z, |ρ.im| ≤ T) :
    ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) / ‖ρ‖
      ≤ 137 * Real.log ((q : ℝ) * (T + 3)) * (8 + 4 * Real.log (T + 1)) := by
  classical
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set n : ℕ := ⌈T⌉₊ with hn
  have hTn : T ≤ (n : ℝ) := Nat.le_ceil T
  have hnT : (n : ℝ) < T + 1 := Nat.ceil_lt_add_one hT
  set J : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ) with hJ
  set C : ℝ := (7 / Real.log (39 / 37)) * Real.log ((q : ℝ) * (T + 3)) with hC
  have hlogpos : (0 : ℝ) < Real.log (39 / 37) := lt_of_lt_of_le (by norm_num) log_39_37_lower
  have hlognn : 0 ≤ Real.log ((q : ℝ) * (T + 3)) := by
    refine Real.log_nonneg ?_; nlinarith
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  set w : ℤ → ℝ := fun j => 2 / max |(j : ℝ)| 1 with hw
  have hmax1 : ∀ j : ℤ, (1 : ℝ) ≤ max |(j : ℝ)| 1 := fun j => le_max_right _ _
  have hwnn : ∀ j : ℤ, 0 ≤ w j := fun j => by
    rw [hw]; exact div_nonneg (by norm_num) (le_trans zero_le_one (hmax1 j))
  -- the fibre map lands in `J` (`efMultTotal_box_le`'s `hmaps`, verbatim)
  have hmaps : ∀ ρ ∈ Z, round ρ.im ∈ J := by
    intro ρ hρ
    have h1' := abs_le.mp (abs_sub_round ρ.im)
    have h2' := abs_le.mp (hZim ρ hρ)
    rw [hJ, Finset.mem_Icc]
    constructor
    · have h5 : ((-(n : ℤ) - 1 : ℤ) : ℝ) < ((round ρ.im : ℤ) : ℝ) := by push_cast; linarith
      have h6 : (-(n : ℤ) - 1 : ℤ) < round ρ.im := by exact_mod_cast h5
      omega
    · have h5 : ((round ρ.im : ℤ) : ℝ) < (((n : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
      have h6 : round ρ.im < (n : ℤ) + 1 := by exact_mod_cast h5
      omega
  -- each fibre's *mass* is N1's window count (`efMultTotal_box_le`'s `hfib`, verbatim)
  have hfibmass : ∀ j ∈ J, efMultTotal χ {ρ ∈ Z | round ρ.im = j} ≤ C := by
    intro j hj
    have hball : ∀ ρ ∈ {ρ ∈ Z | round ρ.im = j},
        ρ ∈ Metric.closedBall (2 + ((j : ℝ) : ℂ) * I) (37 / 20) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρZ, hrj⟩ := hρ
      refine halfbox_subset_closedBall (j : ℝ) ⟨(hZre ρ hρZ).1, (hZre ρ hρZ).2, ?_⟩
      rw [← hrj]
      exact le_trans (abs_sub_round ρ.im) (by norm_num)
    refine (efMultTotal_halfbox_le χ hχ hq (j : ℝ) hball
      (fun ρ hρ => hZ0 ρ (Finset.mem_filter.mp hρ).1)).trans ?_
    have hjn := Finset.mem_Icc.mp hj
    have hjabs : |(j : ℝ)| ≤ (n : ℝ) := by
      rw [abs_le]
      constructor
      · have : ((-(n : ℤ) : ℤ) : ℝ) ≤ ((j : ℤ) : ℝ) := by exact_mod_cast hjn.1
        push_cast at this; linarith
      · have : ((j : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast hjn.2
        push_cast at this; linarith
    have hle : (q : ℝ) * (|(j : ℝ)| + 2) ≤ (q : ℝ) * (T + 3) := by nlinarith
    rw [hC]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hle) (by positivity)
  -- the fibre's *weight*: `‖ρ‖ ≥ max(|j|,1)/2`
  have hfib : ∀ j ∈ J,
      ∑ ρ ∈ {ρ ∈ Z | round ρ.im = j}, (zeroMult χ ρ : ℝ) / ‖ρ‖ ≤ w j * C := by
    intro j hj
    have hterm : ∀ ρ ∈ {ρ ∈ Z | round ρ.im = j},
        (zeroMult χ ρ : ℝ) / ‖ρ‖ ≤ w j * (zeroMult χ ρ : ℝ) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρZ, hrj⟩ := hρ
      have hre : ρ.re ≤ ‖ρ‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm ρ)
      have him : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
      have hhalf : (1 : ℝ) / 2 ≤ ‖ρ‖ := le_trans (hZre ρ hρZ).1 hre
      have hround : |ρ.im - (j : ℝ)| ≤ 1 / 2 := by
        rw [← hrj]; exact abs_sub_round ρ.im
      have hjim : |(j : ℝ)| ≤ |ρ.im| + 1 / 2 := by
        have := abs_sub_abs_le_abs_sub ((j : ℝ)) ρ.im
        have habs : |(j : ℝ) - ρ.im| = |ρ.im - (j : ℝ)| := abs_sub_comm _ _
        rw [habs] at this
        linarith
      have hlow : max |(j : ℝ)| 1 / 2 ≤ ‖ρ‖ := by
        rw [div_le_iff₀ (by norm_num)]
        exact max_le (by linarith) (by linarith)
      have hpos : (0 : ℝ) < ‖ρ‖ := by linarith
      have hinv : 1 / ‖ρ‖ ≤ w j := by
        simp only [hw]
        have h2 : (2 : ℝ) / max |(j : ℝ)| 1 = 1 / (max |(j : ℝ)| 1 / 2) := by
          rw [div_div_eq_mul_div, one_mul]
        rw [h2]
        exact one_div_le_one_div_of_le (by linarith [hmax1 j]) hlow
      calc (zeroMult χ ρ : ℝ) / ‖ρ‖ = (zeroMult χ ρ : ℝ) * (1 / ‖ρ‖) := by ring
        _ ≤ (zeroMult χ ρ : ℝ) * w j := mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = w j * (zeroMult χ ρ : ℝ) := by ring
    calc ∑ ρ ∈ {ρ ∈ Z | round ρ.im = j}, (zeroMult χ ρ : ℝ) / ‖ρ‖
        ≤ ∑ ρ ∈ {ρ ∈ Z | round ρ.im = j}, w j * (zeroMult χ ρ : ℝ) := Finset.sum_le_sum hterm
      _ = w j * efMultTotal χ {ρ ∈ Z | round ρ.im = j} := by rw [efMultTotal, Finset.mul_sum]
      _ ≤ w j * C := mul_le_mul_of_nonneg_left (hfibmass j hj) (hwnn j)
  -- the weight sum: twice a harmonic sum
  set A : Finset ℤ := (Finset.range (n + 1)).image (fun k : ℕ => (k : ℤ)) with hA
  set B : Finset ℤ := (Finset.range (n + 1)).image (fun k : ℕ => -(k : ℤ)) with hB
  have hJsub : J ⊆ A ∪ B := by
    intro j hj
    rw [hJ, Finset.mem_Icc] at hj
    rcases le_or_gt 0 j with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨j.natAbs, Finset.mem_range.mpr (by omega), by omega⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨j.natAbs, Finset.mem_range.mpr (by omega), by omega⟩)
  have hrange : ∑ k ∈ Finset.range (n + 1), (2 : ℝ) / max ((k : ℕ) : ℝ) 1
      = 2 + 2 * (harmonic n : ℝ) := by
    rw [Finset.sum_range_succ' (fun k : ℕ => (2 : ℝ) / max ((k : ℕ) : ℝ) 1) n]
    have hstep : ∀ i ∈ Finset.range n,
        (2 : ℝ) / max (((i + 1 : ℕ)) : ℝ) 1 = 2 * (1 / ((i : ℝ) + 1)) := by
      intro i _
      have hc : (((i + 1 : ℕ)) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
      have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      rw [hc, max_eq_left (by linarith)]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, sum_range_inv_succ_eq_harmonic]
    norm_num
    ring
  have hAsum : ∑ j ∈ A, w j = ∑ k ∈ Finset.range (n + 1), (2 : ℝ) / max ((k : ℕ) : ℝ) 1 := by
    rw [hA, Finset.sum_image (by intro x _ y _ h; simpa using h)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hw]
    norm_num
  have hBsum : ∑ j ∈ B, w j = ∑ k ∈ Finset.range (n + 1), (2 : ℝ) / max ((k : ℕ) : ℝ) 1 := by
    rw [hB, Finset.sum_image (by intro x _ y _ h; simpa using h)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hw]
    norm_num
  have hwsum : ∑ j ∈ J, w j ≤ 4 + 4 * (harmonic n : ℝ) := by
    have h1 : ∑ j ∈ J, w j ≤ ∑ j ∈ A ∪ B, w j :=
      Finset.sum_le_sum_of_subset_of_nonneg hJsub (fun i _ _ => hwnn i)
    have h2 : ∑ j ∈ A ∪ B, w j + ∑ j ∈ A ∩ B, w j = ∑ j ∈ A, w j + ∑ j ∈ B, w j :=
      Finset.sum_union_inter
    have h3 : 0 ≤ ∑ j ∈ A ∩ B, w j := Finset.sum_nonneg (fun j _ => hwnn j)
    rw [hAsum, hBsum, hrange] at h2
    linarith
  -- the harmonic bound, and the height comparison
  have hharm : (harmonic n : ℝ) ≤ 1 + Real.log (T + 1) := by
    refine (harmonic_le_one_add_log n).trans ?_
    have hlogn : Real.log (n : ℝ) ≤ Real.log (T + 1) := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0]
        simpa using Real.log_nonneg (by linarith)
      · exact Real.log_le_log (by exact_mod_cast h0) hnT.le
    linarith
  have hsum : ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) / ‖ρ‖
      = ∑ j ∈ J, ∑ ρ ∈ {ρ ∈ Z | round ρ.im = j}, (zeroMult χ ρ : ℝ) / ‖ρ‖ :=
    (Finset.sum_fiberwise_of_maps_to hmaps (fun ρ => (zeroMult χ ρ : ℝ) / ‖ρ‖)).symm
  have hlogT : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
  calc ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) / ‖ρ‖
      = ∑ j ∈ J, ∑ ρ ∈ {ρ ∈ Z | round ρ.im = j}, (zeroMult χ ρ : ℝ) / ‖ρ‖ := hsum
    _ ≤ ∑ j ∈ J, w j * C := Finset.sum_le_sum hfib
    _ = (∑ j ∈ J, w j) * C := by rw [Finset.sum_mul]
    _ ≤ (4 + 4 * (harmonic n : ℝ)) * C := mul_le_mul_of_nonneg_right hwsum hCnn
    _ ≤ (8 + 4 * Real.log (T + 1)) * C := by
        refine mul_le_mul_of_nonneg_right (by linarith) hCnn
    _ ≤ (8 + 4 * Real.log (T + 1)) * (137 * Real.log ((q : ℝ) * (T + 3))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [hC]
        exact mul_le_mul_of_nonneg_right windowConst_le_137 hlognn
    _ = 137 * Real.log ((q : ℝ) * (T + 3)) * (8 + 4 * Real.log (T + 1)) := by ring

/-! ## 3. `N(σ,T,χ)` and the crude density -/

/-- **`zeroCountM χ σ T` — HB/Jutila's `N(σ,T,χ)`**: the zeros of `L(·,χ)` in the box
`σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T`, counted **with multiplicity** (HB's `Σ′` is multiplicity-counting,
and N1's re-base carries the same weight). The enumeration is N1's `boxZeros`. -/
noncomputable def zeroCountM {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ℝ :=
  efMultTotal χ (boxZeros χ σ 1 T)

/-- **The count, at the numeral `137`.** `N(σ,T,χ) ≤ 137·(2T+3)·log(q(T+3))` for every
`σ ≥ 1/2` — note the bound is **constant in `σ`**: this is a count, not a detection argument. -/
theorem zeroCountM_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) :
    zeroCountM χ σ T ≤ 137 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3)) := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hlognn : 0 ≤ Real.log ((q : ℝ) * (T + 3)) := by
    refine Real.log_nonneg ?_
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hbox := efMultTotal_box_le χ hχ hq (Z := boxZeros χ σ 1 T) hT
    (fun ρ hρ => ((mem_boxZeros hχ1).mp hρ).1)
    (fun ρ hρ => ⟨le_trans hσ ((mem_boxZeros hχ1).mp hρ).2.1, ((mem_boxZeros hχ1).mp hρ).2.2.1⟩)
    (fun ρ hρ => ((mem_boxZeros hχ1).mp hρ).2.2.2)
  refine le_trans hbox ?_
  have hw := windowConst_le_137
  have h2T : (0 : ℝ) ≤ 2 * T + 3 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hw hlognn]

/-- **THE ROAD'S SHAPE, at `D = 83` — with no constant and no log factor.**

    N(σ, T, χ) ≤ (qT)^{83(1−σ)}     for  4/5 ≤ σ ≤ 16/17,  T ≥ 2,  q ≥ 8.

This is HB (4.9) at an exponent 33× coarser than Jutila's `5/2`, which ⟦N0 CLEAR⟧ ruled
sufficient (`D < 249.8` is the road's tolerance at the polylog height `t = 9.7e-4`; `D ≤ 83`
carries ≈ 3× slack). The proof is the *count*: `83(1−σ) ≥ 83/17 > 4`, and

    137·(2T+3)·log(q(T+3)) ≤ 137·(4T)·(q·3T) = 1644·q·T² ≤ q⁴T⁴ ≤ (qT)^{83(1−σ)}

because `q³T² ≥ 8³·2² = 2048 ≥ 1644`. The two thresholds `q ≥ 8`, `T ≥ 2` are exactly what that
last inequality needs; the road runs at `q` astronomically larger. -/
theorem zeroCountM_density_crude {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 8 ≤ q) {σ T : ℝ} (hσ1 : 4 / 5 ≤ σ) (hσ2 : σ ≤ 16 / 17)
    (hT : 2 ≤ T) :
    zeroCountM χ σ T ≤ ((q : ℝ) * T) ^ (83 * (1 - σ)) := by
  have hq8 : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hQ1 : (1 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hexp : (4 : ℝ) ≤ 83 * (1 - σ) := by linarith
  have hrpow : ((q : ℝ) * T) ^ (4 : ℝ) ≤ ((q : ℝ) * T) ^ (83 * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 hexp
  have hnat : ((q : ℝ) * T) ^ (4 : ℝ) = ((q : ℝ) * T) ^ (4 : ℕ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hcount := zeroCountM_le χ hχ (by omega : 2 ≤ q) (by linarith : (1 : ℝ) / 2 ≤ σ) hT0
  -- the arithmetic: count ≤ (qT)^4
  have hlog : Real.log ((q : ℝ) * (T + 3)) ≤ (q : ℝ) * (T + 3) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (q : ℝ) * (T + 3) by nlinarith)
    linarith
  have hlognn : 0 ≤ Real.log ((q : ℝ) * (T + 3)) := by
    refine Real.log_nonneg ?_; nlinarith
  have hstep1 : 137 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3))
      ≤ 137 * (4 * T) * ((q : ℝ) * (3 * T)) := by
    have ha : 137 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3))
        ≤ 137 * (4 * T) * Real.log ((q : ℝ) * (T + 3)) := by nlinarith
    have hb : 137 * (4 * T) * Real.log ((q : ℝ) * (T + 3))
        ≤ 137 * (4 * T) * ((q : ℝ) * (3 * T)) := by nlinarith
    linarith
  have hstep2 : 137 * (4 * T) * ((q : ℝ) * (3 * T)) = 1644 * ((q : ℝ) * T ^ 2) := by ring
  have hkey : (1644 : ℝ) ≤ (q : ℝ) ^ 3 * T ^ 2 := by
    have h1 : (512 : ℝ) ≤ (q : ℝ) ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hq8 3
      norm_num at h; linarith
    have h2 : (4 : ℝ) ≤ T ^ 2 := by nlinarith
    have h3 : (512 : ℝ) * 4 ≤ (q : ℝ) ^ 3 * T ^ 2 :=
      mul_le_mul h1 h2 (by norm_num) (by positivity)
    linarith
  have hstep3 : 1644 * ((q : ℝ) * T ^ 2) ≤ ((q : ℝ) * T) ^ (4 : ℕ) := by
    have hfac : ((q : ℝ) * T) ^ (4 : ℕ) - 1644 * ((q : ℝ) * T ^ 2)
        = (q : ℝ) * T ^ 2 * ((q : ℝ) ^ 3 * T ^ 2 - 1644) := by ring
    nlinarith [mul_nonneg (mul_nonneg (le_of_lt (show (0:ℝ) < (q:ℝ) by linarith)) (sq_nonneg T))
      (by linarith : (0:ℝ) ≤ (q : ℝ) ^ 3 * T ^ 2 - 1644)]
  calc zeroCountM χ σ T ≤ 137 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3)) := hcount
    _ ≤ ((q : ℝ) * T) ^ (4 : ℕ) := by linarith
    _ = ((q : ℝ) * T) ^ (4 : ℝ) := hnat.symm
    _ ≤ ((q : ℝ) * T) ^ (83 * (1 - σ)) := hrpow

/-- **The road's shape on the WHOLE range `4/5 ≤ σ ≤ 1`**, at the price of the count as an
explicit factor. Honest reading: on the near-1 strip `16/17 < σ ≤ 1` the exponential factor
`(qT)^{83(1−σ)}` degenerates to `1` and this says exactly "`N ≤` the count" — which is the truth
of the matter at polylog height. The near-1 zeros are handled by repulsion, not density; the
shape they are consumed in is `efZeroSumM_spend_le` below. -/
theorem zeroCountM_density_log {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {σ T : ℝ} (hσ1 : 4 / 5 ≤ σ) (hσ2 : σ ≤ 1) (hT : 2 ≤ T) :
    zeroCountM χ σ T
      ≤ ((q : ℝ) * T) ^ (83 * (1 - σ)) * (137 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3))) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hQ1 : (1 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hexp : (0 : ℝ) ≤ 83 * (1 - σ) := by linarith
  have hone : (1 : ℝ) ≤ ((q : ℝ) * T) ^ (83 * (1 - σ)) := Real.one_le_rpow hQ1 hexp
  have hcount := zeroCountM_le χ hχ hq (by linarith : (1 : ℝ) / 2 ≤ σ) hT0
  have hlognn : 0 ≤ Real.log ((q : ℝ) * (T + 3)) := by
    refine Real.log_nonneg ?_; nlinarith
  have hnn : 0 ≤ 137 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3)) := by positivity
  nlinarith

/-- **The campaign box's count is POLYLOG.** At the ⟦N0 CLEAR⟧ ruled height
`T = efHeight q + 2 = (log q + 2)⁴ + 2` — the box `psi_sharp_at_efHeightM` enumerates — the total
multiplicity of the zeros is at most `2055·(log q + 2)⁵`. This is the number that prices *both*
the explicit formula's `efMultTotal·(y/T)` error term and the zero sum's spend. -/
theorem zeroCountM_efHeight_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    zeroCountM χ σ (efHeight q + 2) ≤ 2055 * (Real.log q + 2) ^ 5 := by
  set L : ℝ := Real.log q with hL
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := by omega
    exact_mod_cast this
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hL0 : 0 ≤ L := Real.log_nonneg hq1
  have hE : efHeight q = (L + 2) ^ 4 := rfl
  have h16 : (16 : ℝ) ≤ (L + 2) ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ L + 2) 4
    norm_num at h ⊢; linarith
  have hT0 : (0 : ℝ) ≤ efHeight q + 2 := by rw [hE]; linarith
  have hcount := zeroCountM_le χ hχ hq (σ := σ) (T := efHeight q + 2) hσ hT0
  refine le_trans hcount ?_
  rw [hE]
  -- the two polylog reductions
  have hA : 2 * ((L + 2) ^ 4 + 2) + 3 ≤ 3 * (L + 2) ^ 4 := by linarith
  have hlogsplit : Real.log ((q : ℝ) * ((L + 2) ^ 4 + 2 + 3))
      = L + Real.log ((L + 2) ^ 4 + 5) := by
    rw [show (L + 2) ^ 4 + 2 + 3 = (L + 2) ^ 4 + 5 by ring,
      Real.log_mul (by linarith) (by positivity), hL]
  have hlog2 : Real.log ((L + 2) ^ 4 + 5) ≤ Real.log (2 * (L + 2) ^ 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog3 : Real.log (2 * (L + 2) ^ 4) = Real.log 2 + 4 * Real.log (L + 2) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have hlog4 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlog5 : Real.log (L + 2) ≤ L + 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L + 2 by linarith); linarith
  have hB : Real.log ((q : ℝ) * ((L + 2) ^ 4 + 2 + 3)) ≤ 5 * (L + 2) := by
    rw [hlogsplit]; linarith
  have hBnn : 0 ≤ Real.log ((q : ℝ) * ((L + 2) ^ 4 + 2 + 3)) := by
    refine Real.log_nonneg ?_; nlinarith
  calc 137 * (2 * ((L + 2) ^ 4 + 2) + 3) * Real.log ((q : ℝ) * ((L + 2) ^ 4 + 2 + 3))
      ≤ 137 * (3 * (L + 2) ^ 4) * Real.log ((q : ℝ) * ((L + 2) ^ 4 + 2 + 3)) := by nlinarith
    _ ≤ 137 * (3 * (L + 2) ^ 4) * (5 * (L + 2)) := by
        nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ L + 2) 4]
    _ = 2055 * (L + 2) ^ 5 := by ring

/-! ## 4. THE SPEND — the shape N3/N4 consume -/

/-- **The dyadic spend, collapsed.** `∑_{ρ∈Z} m_ρ·y^{Re ρ−1} ≤ (∑ m_ρ)·y^{β−1}` for `y ≥ 1` and
`Re ρ ≤ β` on `Z`. A genuine density theorem would be consumed through a dyadic decomposition in
`σ` with the count re-read in each strip; here the count is `σ`-independent, so the dyadic sum
telescopes to this sup bound with no loss — the exponential saving lives entirely in `β < 1`
(the repulsion input), not in the count. -/
theorem zeroSum_rpow_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {Z : Finset ℂ}
    {y β : ℝ} (hy : 1 ≤ y) (hβ : ∀ ρ ∈ Z, ρ.re ≤ β) :
    ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ efMultTotal χ Z * y ^ (β - 1) := by
  rw [efMultTotal, Finset.sum_mul]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have h : y ^ (ρ.re - 1) ≤ y ^ (β - 1) :=
    Real.rpow_le_rpow_of_exponent_le hy (by linarith [hβ ρ hρ])
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **The zero sum of the explicit formula, priced.** For `y ≥ 1` and every `ρ ∈ Z` in the strip
`0 < a ≤ Re ρ ≤ β`,

    ‖∑_{ρ∈Z} m_ρ·y^ρ/ρ‖ ≤ (∑_{ρ∈Z} m_ρ)·y^β/a.

`|ρ| ≥ Re ρ ≥ a` is the only place the box's left edge is spent. -/
theorem efZeroSumM_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {Z : Finset ℂ}
    {y a β : ℝ} (hy : 1 ≤ y) (ha : 0 < a) (hlow : ∀ ρ ∈ Z, a ≤ ρ.re) (hβ : ∀ ρ ∈ Z, ρ.re ≤ β) :
    ‖efZeroSumM χ Z y‖ ≤ efMultTotal χ Z * (y ^ β / a) := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  rw [efZeroSumM, efMultTotal, Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ρ hρ => ?_)
  have hρa : a ≤ ‖ρ‖ :=
    le_trans (hlow ρ hρ) (le_trans (le_abs_self _) (Complex.abs_re_le_norm ρ))
  have hρ0 : (0 : ℝ) < ‖ρ‖ := lt_of_lt_of_le ha hρa
  rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_natCast]
  have h2 : y ^ ρ.re ≤ y ^ β := Real.rpow_le_rpow_of_exponent_le hy (hβ ρ hρ)
  have h3 : y ^ ρ.re / ‖ρ‖ ≤ y ^ β / a := by
    apply div_le_div₀ (by positivity) h2 ha hρa
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-- **THE A3-BATCHED SPEND (N4b W0-ii).** The same per-term estimate as `efZeroSumM_norm_le`,
stopped *before* the `1/‖ρ‖ ≤ 1/a` collapse:

    ‖∑_{ρ∈Z} m_ρ·y^ρ/ρ‖ ≤ y^β · ∑_{ρ∈Z} m_ρ/‖ρ‖.

Keeping the harmonic weight is what lets A3's batching (`efMultTotal_harmonic_box_le`) price the
sum at `log(qT)·log T` grade rather than at the left-edge-divided count `T·log(qT)/a` — the
difference between a `T`-sized and a `log T`-sized prefactor in the Range-B tail. No hypothesis
on `ρ ≠ 0` is needed: at `ρ = 0` both sides' terms are `0`. -/
theorem efZeroSumM_norm_le_harmonic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {Z : Finset ℂ} {y β : ℝ} (hy : 1 ≤ y) (hβ : ∀ ρ ∈ Z, ρ.re ≤ β) :
    ‖efZeroSumM χ Z y‖ ≤ y ^ β * ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) / ‖ρ‖ := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  rw [efZeroSumM, Finset.mul_sum]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ρ hρ => ?_)
  rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_natCast]
  have h2 : y ^ ρ.re ≤ y ^ β := Real.rpow_le_rpow_of_exponent_le hy (hβ ρ hρ)
  have hnn : (0 : ℝ) ≤ (zeroMult χ ρ : ℝ) / ‖ρ‖ :=
    div_nonneg (by positivity) (norm_nonneg ρ)
  calc (zeroMult χ ρ : ℝ) * (y ^ ρ.re / ‖ρ‖)
      = ((zeroMult χ ρ : ℝ) / ‖ρ‖) * y ^ ρ.re := by ring
    _ ≤ ((zeroMult χ ρ : ℝ) / ‖ρ‖) * y ^ β := mul_le_mul_of_nonneg_left h2 hnn
    _ = y ^ β * ((zeroMult χ ρ : ℝ) / ‖ρ‖) := by ring

/-- **THE ERASED SPEND (N4b W0-ii, the Range-B consumer).** After the exceptional zero's residue
is peeled off by `efZeroSumM_erase_split`, what is left is priced by the *whole* box's harmonic
weight — subset monotonicity, so the erased sum never has to be re-batched:

    ‖∑_{ρ ∈ Z∖{β₀}} m_ρ·y^ρ/ρ‖ ≤ y^β · ∑_{ρ ∈ Z} m_ρ/‖ρ‖. -/
theorem efZeroSumM_erase_norm_le_harmonic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {Z : Finset ℂ} (β₀ : ℂ) {y β : ℝ} (hy : 1 ≤ y) (hβ : ∀ ρ ∈ Z, ρ.re ≤ β) :
    ‖efZeroSumM χ (Z.erase β₀) y‖ ≤ y ^ β * ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) / ‖ρ‖ := by
  classical
  refine le_trans (efZeroSumM_norm_le_harmonic χ (Z := Z.erase β₀) hy
    (fun ρ hρ => hβ ρ (Finset.mem_of_mem_erase hρ))) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) β)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun i _ _ => div_nonneg (by positivity) (norm_nonneg i))

/-- **THE EXIT (general height).** The explicit formula's zero sum over the box
`{σ ≤ Re ρ ≤ 1, |Im ρ| ≤ T}` is bounded by the box count times `y^β`, where `β` bounds the
zeros' real parts (the repulsion input). At `σ ≥ 1/2` the `1/σ ≤ 2` is folded into the
constant. -/
theorem efZeroSumM_spend_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {σ T y β : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) (hy : 1 ≤ y)
    (hβ : ∀ ρ ∈ boxZeros χ σ 1 T, ρ.re ≤ β) :
    ‖efZeroSumM χ (boxZeros χ σ 1 T) y‖
      ≤ 274 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3)) * y ^ β := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  have hyβ : (0 : ℝ) < y ^ β := Real.rpow_pos_of_pos hy0 β
  have hnorm := efZeroSumM_norm_le χ (Z := boxZeros χ σ 1 T) (y := y) (a := σ) (β := β) hy hσ0
    (fun ρ hρ => ((mem_boxZeros hχ1).mp hρ).2.1) hβ
  have hcount : efMultTotal χ (boxZeros χ σ 1 T)
      ≤ 137 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3)) := zeroCountM_le χ hχ hq hσ hT
  have hcnn : 0 ≤ efMultTotal χ (boxZeros χ σ 1 T) := efMultTotal_nonneg _ _
  have hinv : y ^ β / σ ≤ 2 * y ^ β := by
    rw [div_le_iff₀ hσ0]; nlinarith
  calc ‖efZeroSumM χ (boxZeros χ σ 1 T) y‖
      ≤ efMultTotal χ (boxZeros χ σ 1 T) * (y ^ β / σ) := hnorm
    _ ≤ efMultTotal χ (boxZeros χ σ 1 T) * (2 * y ^ β) := mul_le_mul_of_nonneg_left hinv hcnn
    _ ≤ (137 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3))) * (2 * y ^ β) := by
        exact mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 274 * (2 * T + 3) * Real.log ((q : ℝ) * (T + 3)) * y ^ β := by ring

/-- **THE EXIT — N2's deliverable to N3/N4.** At the ⟦N0 CLEAR⟧ ruled height
`T = efHeight q + 2`, the explicit formula's zero sum (`psi_sharp_at_efHeightM`'s only non-error
term) is bounded by **one polylog constant times `y^β`**:

    ‖∑_{ρ ∈ boxZeros} m_ρ·y^ρ/ρ‖ ≤ 4110·(log q + 2)⁵·y^β,

where `β` is any bound on the real parts of the box's zeros. That single number `β` is the entire
interface to the repulsion side: at `β ≤ 1 − A·L^{−1}log η` and `y ≥ q^{250}` the factor `y^β`
is `y·η^{−250A}`, which is what HB's (4.11) needs. No density-in-`σ` refinement is consumed. -/
theorem efZeroSumM_spend_at_efHeight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {σ y β : ℝ} (hσ : 1 / 2 ≤ σ) (hy : 1 ≤ y)
    (hβ : ∀ ρ ∈ boxZeros χ σ 1 (efHeight q + 2), ρ.re ≤ β) :
    ‖efZeroSumM χ (boxZeros χ σ 1 (efHeight q + 2)) y‖
      ≤ 4110 * (Real.log q + 2) ^ 5 * y ^ β := by
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  have hyβ : (0 : ℝ) < y ^ β := Real.rpow_pos_of_pos hy0 β
  have hq1 : 1 ≤ q := by omega
  have hT0 : (0 : ℝ) ≤ efHeight q + 2 := by linarith [efHeight_pos hq1]
  have hnorm := efZeroSumM_norm_le χ (Z := boxZeros χ σ 1 (efHeight q + 2)) (y := y) (a := σ)
    (β := β) hy hσ0 (fun ρ hρ => ((mem_boxZeros hχ1).mp hρ).2.1) hβ
  have hcount : efMultTotal χ (boxZeros χ σ 1 (efHeight q + 2))
      ≤ 2055 * (Real.log q + 2) ^ 5 := zeroCountM_efHeight_le χ hχ hq hσ
  have hcnn : 0 ≤ efMultTotal χ (boxZeros χ σ 1 (efHeight q + 2)) := efMultTotal_nonneg _ _
  have hinv : y ^ β / σ ≤ 2 * y ^ β := by
    rw [div_le_iff₀ hσ0]; nlinarith
  calc ‖efZeroSumM χ (boxZeros χ σ 1 (efHeight q + 2)) y‖
      ≤ efMultTotal χ (boxZeros χ σ 1 (efHeight q + 2)) * (y ^ β / σ) := hnorm
    _ ≤ efMultTotal χ (boxZeros χ σ 1 (efHeight q + 2)) * (2 * y ^ β) :=
        mul_le_mul_of_nonneg_left hinv hcnn
    _ ≤ (2055 * (Real.log q + 2) ^ 5) * (2 * y ^ β) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 4110 * (Real.log q + 2) ^ 5 * y ^ β := by ring

end Salt.SW
