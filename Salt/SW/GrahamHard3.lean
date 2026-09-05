/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.GrahamHard2

/-!
# ARM B part B2, wave **W6b-H2** — the KEYSTONE'S HARD HALF

placeholder
-/

namespace Salt.SW

open ArithmeticFunction

/-- `J_z(a, b; Y) := Σ_{k ≤ Y, (k, ab) = 1} μ(k)²·log(ak/z)·log(bk/z)` — H4's innermost sum
with its two side conditions `z < ak`, `z < bk` removed (H7a puts them back as a difference
of two `J`s). -/
noncomputable def sqfLogPair (z a b Y : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 Y).filter (fun k => Nat.Coprime k (a * b)),
    (moebius k : ℝ) ^ 2 * Real.log (((a * k : ℕ) : ℝ) / z) * Real.log (((b * k : ℕ) : ℝ) / z)

/-- The A-kernel at scale `Q`: ΣA's inner double sum,
`Σ_{a,b ≤ Q, (a,b)=1} (μ(a)/κ(a))(μ(b)/κ(b))·((log(Q/b) − 1)(log(Q/a) − 1) + 1)`;
it tends to `c₀` (H7c). -/
noncomputable def aKernel (Q : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ b ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => Nat.Coprime a b),
    (moebius a : ℝ) / kappa a * ((moebius b : ℝ) / kappa b)
      * ((Real.log (Q / b) - 1) * (Real.log (Q / a) - 1) + 1)

/-- The B-kernel at level `z`, scale `Q`: the lower-limit main terms (ΣB + ΣC),
`Σ_{a,b ≤ Q, (a,b)=1} μ(a)μ(b)·(ab/κ(ab))·(z/min(a,b))·((log(a/min) − 1)(log(b/min) − 1) + 1)`;
it is `O(zQ/log²2Q)` (H7d). -/
noncomputable def bKernel (z : ℕ) (Q : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ b ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => Nat.Coprime a b),
    (moebius a : ℝ) * (moebius b : ℝ) * (((a * b : ℕ) : ℝ) / kappa (a * b))
      * ((z : ℝ) / ((min a b : ℕ) : ℝ))
      * ((Real.log ((a : ℝ) / ((min a b : ℕ) : ℝ)) - 1)
          * (Real.log ((b : ℝ) / ((min a b : ℕ) : ℝ)) - 1) + 1)

/-! ## I. THE EXACT REDUCTIONS -/

/-- `κ` is multiplicative on coprime pairs: `κ(ab) = κ(a)κ(b)` — the prime-factor sets are
disjoint and their union is `(ab).primeFactors`. (`GrahamHard2.lean` carries this as a
private helper of T7; a `private` cannot be consumed across files, so it lands here PUBLIC.)

The must-FAIL control: WITHOUT `Coprime`, `kappa (a*b) = kappa a * kappa b` is FALSE at
`(2, 2)` — `κ(4) = 4·(3/2) = 6` against `κ(2)² = 3² = 9`. -/
theorem kappa_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    kappa (a * b) = kappa a * kappa b := by
  rw [kappa, kappa, kappa, Nat.Coprime.primeFactors_mul hab,
    Finset.prod_union (Nat.Coprime.disjoint_primeFactors hab)]
  push_cast
  ring

/-- **H7e-0 (K36).** `σ_{−1/4}(ab) ≤ σ_{−1/4}(a)·σ_{−1/4}(b)` for ALL `a, b` — no coprimality.
`Nat.divisors_mul` (hypothesis-free) writes `(ab).divisors` as the pointwise product
`a.divisors * b.divisors`, i.e. an image of `a.divisors ×ˢ b.divisors`; the image sum of a
nonnegative function is at most the sum over the product, and `(e₁e₂)^{−1/4} =
e₁^{−1/4}·e₂^{−1/4}`.

The must-FAIL control: `≥` in place of `≤` is FALSE at `(2, 2)` —
`σ(4) = 1 + 2^{−1/4} + 4^{−1/4} = 2.548` against `σ(2)² = (1 + 2^{−1/4})² = 3.389`. -/
theorem sigmaQ_mul_le (a b : ℕ) : sigmaQ (a * b) ≤ sigmaQ a * sigmaQ b := by
  classical
  have hprod : sigmaQ a * sigmaQ b
      = ∑ p ∈ a.divisors ×ˢ b.divisors, (((p.1 * p.2 : ℕ) : ℝ)) ^ (-(1/4 : ℝ)) := by
    rw [sigmaQ, sigmaQ, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun e1 _ => Finset.sum_congr rfl fun e2 _ => ?_
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  rw [sigmaQ, Nat.divisors_mul, Finset.mul_def, hprod]
  exact Finset.sum_image_le_of_nonneg fun u _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- **H7a (the lower limit as a difference).** H4's innermost filter carries the two side
conditions `z < ak`, `z < bk`; for `a, b ≥ 1` they are jointly `z / min(a,b) < k`
(`Nat.div_lt_iff_lt_mul`, and ℕ-division is antitone in the divisor), so the filtered sum is
`J(M) − J(min(M, z/min(a,b)))`.

⚠ **The `min` is where An's display is implicit** and it is load-bearing. The must-FAIL
control (K40): without it — i.e. `J(M) − J(z / min a b)` — the row is FALSE whenever
`z/min(a,b) > M`. At `(z, a, b, M) = (10, 1, 1, 3)` the left side is `0` (no `k ≤ 3` with
`10 < k`), the with-`min` right side is `0`, and the without-`min` right side is
`−0.868613`. (52,000-point grid: 0 counterexamples with the `min`, 8,512 without.) -/
theorem sum_filter_side_eq_sqfLogPair_sub (z a b M : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∑ k ∈ (Finset.Icc 1 M).filter (fun k => Nat.Coprime k (a * b) ∧ z < a * k ∧ z < b * k),
        (moebius k : ℝ) ^ 2 * Real.log (((a * k : ℕ) : ℝ) / z)
          * Real.log (((b * k : ℕ) : ℝ) / z)
      = sqfLogPair z a b M - sqfLogPair z a b (min M (z / min a b)) := by
  classical
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  have hA : ∀ k : ℕ, (z < a * k ↔ z / a < k) := fun k => by
    rw [Nat.div_lt_iff_lt_mul ha0, Nat.mul_comm k a]
  have hB : ∀ k : ℕ, (z < b * k ↔ z / b < k) := fun k => by
    rw [Nat.div_lt_iff_lt_mul hb0, Nat.mul_comm k b]
  have hkey : ∀ k : ℕ, ((z < a * k ∧ z < b * k) ↔ z / min a b < k) := by
    intro k
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, ← hA k]
      exact ⟨fun h => h.1,
        fun h => ⟨h, lt_of_lt_of_le h (Nat.mul_le_mul hab (le_refl k))⟩⟩
    · rw [min_eq_right hab, ← hB k]
      exact ⟨fun h => h.2,
        fun h => ⟨lt_of_lt_of_le h (Nat.mul_le_mul hab (le_refl k)), h⟩⟩
  have hsub : (Finset.Icc 1 (min M (z / min a b))).filter (fun k => Nat.Coprime k (a * b))
      ⊆ (Finset.Icc 1 M).filter (fun k => Nat.Coprime k (a * b)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    exact ⟨⟨hk.1.1, le_trans hk.1.2 (min_le_left _ _)⟩, hk.2⟩
  have hset : (Finset.Icc 1 M).filter (fun k => Nat.Coprime k (a * b) ∧ z < a * k ∧ z < b * k)
      = (Finset.Icc 1 M).filter (fun k => Nat.Coprime k (a * b))
        \ (Finset.Icc 1 (min M (z / min a b))).filter (fun k => Nat.Coprime k (a * b)) := by
    ext k
    constructor
    · intro hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨h1, h2⟩, hp, hzz⟩ := hk
      have hlt := (hkey k).mp hzz
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_Icc]
      refine ⟨⟨⟨h1, h2⟩, hp⟩, ?_⟩
      rintro ⟨⟨-, hle⟩, -⟩
      exact absurd (le_trans hle (min_le_right _ _)) (not_le.mpr hlt)
    · intro hk
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_Icc] at hk
      obtain ⟨⟨⟨h1, h2⟩, hp⟩, hnot⟩ := hk
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨h1, h2⟩, hp, (hkey k).mpr ?_⟩
      by_contra hcon
      exact hnot ⟨⟨h1, le_min h2 (not_lt.mp hcon)⟩, hp⟩
  rw [hset, sqfLogPair, sqfLogPair, eq_sub_iff_add_eq]
  exact Finset.sum_sdiff hsub

/-- Inside the box `max(a,b)·g·z ≤ U` the lower limit is the smaller one:
`(z/min)·g·a·b = ((z/min)·min)·(g·max) ≤ z·g·max ≤ U`. -/
private lemma boxIn {z g a b U : ℕ} (hg : 1 ≤ g) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : max a b * (g * z) ≤ U) : z / min a b ≤ U / (g * a * b) := by
  have hgab : 0 < g * a * b := Nat.mul_pos (Nat.mul_pos hg ha) hb
  have hab : a * b = min a b * max a b := by
    rcases le_total a b with h' | h'
    · rw [min_eq_left h', max_eq_right h']
    · rw [min_eq_right h', max_eq_left h', Nat.mul_comm]
  have hgab2 : g * a * b = min a b * (g * max a b) := by
    calc g * a * b = g * (a * b) := by ring
      _ = g * (min a b * max a b) := by rw [hab]
      _ = min a b * (g * max a b) := by ring
  rw [Nat.le_div_iff_mul_le hgab]
  calc z / min a b * (g * a * b)
      = z / min a b * min a b * (g * max a b) := by rw [hgab2]; ring
    _ ≤ z * (g * max a b) :=
        Nat.mul_le_mul (Nat.div_mul_le_self z (min a b)) (le_refl (g * max a b))
    _ = max a b * (g * z) := by ring
    _ ≤ U := h

/-- Outside the box (`U < max(a,b)·g·z`) the upper limit is the smaller one, so the term is
`J(M) − J(M) = 0`. -/
private lemma boxOut {z g a b U : ℕ} (_hg : 1 ≤ g) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : U < max a b * (g * z)) : U / (g * a * b) ≤ z / min a b := by
  have hm : 0 < min a b := lt_min ha hb
  have hab : a * b = min a b * max a b := by
    rcases le_total a b with h' | h'
    · rw [min_eq_left h', max_eq_right h']
    · rw [min_eq_right h', max_eq_left h', Nat.mul_comm]
  have hgab2 : g * a * b = min a b * (g * max a b) := by
    calc g * a * b = g * (a * b) := by ring
      _ = g * (min a b * max a b) := by rw [hab]
      _ = min a b * (g * max a b) := by ring
  rw [Nat.le_div_iff_mul_le hm]
  have h2 : g * max a b * (U / (g * a * b) * min a b) < g * max a b * z := by
    calc g * max a b * (U / (g * a * b) * min a b)
        = U / (g * a * b) * (g * a * b) := by rw [hgab2]; ring
      _ ≤ U := Nat.div_mul_le_self _ _
      _ < max a b * (g * z) := h
      _ = g * max a b * z := by ring
  exact le_of_lt (Nat.lt_of_mul_lt_mul_left h2)

/-- The `b`-level of H7a''s box: outside `b ≤ U/(gz)` every term vanishes. -/
private lemma boxSumB (z g a U : ℕ) (hg : 1 ≤ g) (ha : 1 ≤ a) (hz : 1 ≤ z)
    (haU : a * (g * z) ≤ U) :
    ∑ b ∈ (Finset.Icc 1 U).filter (fun b => Nat.Coprime a b),
        (moebius a : ℝ) * (moebius b : ℝ)
          * (sqfLogPair z a b (U / (g * a * b))
              - sqfLogPair z a b (min (U / (g * a * b)) (z / min a b)))
      = ∑ b ∈ (Finset.Icc 1 (U / (g * z))).filter (fun b => Nat.Coprime a b),
          (moebius a : ℝ) * (moebius b : ℝ)
            * (sqfLogPair z a b (U / (g * a * b)) - sqfLogPair z a b (z / min a b)) := by
  classical
  have hgz : 0 < g * z := Nat.mul_pos hg hz
  have hsub : (Finset.Icc 1 (U / (g * z))).filter (fun b => Nat.Coprime a b)
      ⊆ (Finset.Icc 1 U).filter (fun b => Nat.Coprime a b) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb ⊢
    exact ⟨⟨hb.1.1, le_trans hb.1.2 (Nat.div_le_self _ _)⟩, hb.2⟩
  rw [← Finset.sum_subset hsub ?_]
  · refine Finset.sum_congr rfl fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    have hb1 : 1 ≤ b := hb.1.1
    have hbU : b * (g * z) ≤ U := (Nat.le_div_iff_mul_le hgz).mp hb.1.2
    have hbox : max a b * (g * z) ≤ U := by
      rcases le_total a b with h | h
      · rw [max_eq_right h]; exact hbU
      · rw [max_eq_left h]; exact haU
    rw [min_eq_right (boxIn hg ha hb1 hbox)]
  · intro b hb hnot
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    have hb1 : 1 ≤ b := hb.1.1
    have hout : ¬ b ≤ U / (g * z) := by
      intro hle
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb1, hle⟩, hb.2⟩)
    rw [Nat.le_div_iff_mul_le hgz] at hout
    have hbig : U < max a b * (g * z) :=
      lt_of_lt_of_le (not_le.mp hout) (Nat.mul_le_mul (le_max_right a b) (le_refl (g * z)))
    rw [min_eq_left (boxOut hg ha hb1 hbig)]
    ring

/-- The `a`-level of H7a''s box: outside `a ≤ U/(gz)` the whole `b`-sum vanishes. -/
private lemma boxSumA (z g U : ℕ) (hg : 1 ≤ g) (hz : 1 ≤ z) :
    ∑ a ∈ Finset.Icc 1 U, ∑ b ∈ (Finset.Icc 1 U).filter (fun b => Nat.Coprime a b),
        (moebius a : ℝ) * (moebius b : ℝ)
          * (sqfLogPair z a b (U / (g * a * b))
              - sqfLogPair z a b (min (U / (g * a * b)) (z / min a b)))
      = ∑ a ∈ Finset.Icc 1 (U / (g * z)),
          ∑ b ∈ (Finset.Icc 1 (U / (g * z))).filter (fun b => Nat.Coprime a b),
            (moebius a : ℝ) * (moebius b : ℝ)
              * (sqfLogPair z a b (U / (g * a * b)) - sqfLogPair z a b (z / min a b)) := by
  classical
  have hgz : 0 < g * z := Nat.mul_pos hg hz
  have hsub : Finset.Icc 1 (U / (g * z)) ⊆ Finset.Icc 1 U := by
    intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    exact ⟨ha.1, le_trans ha.2 (Nat.div_le_self _ _)⟩
  rw [← Finset.sum_subset hsub ?_]
  · refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_Icc] at ha
    exact boxSumB z g a U hg ha.1 hz ((Nat.le_div_iff_mul_le hgz).mp ha.2)
  · intro a ha hnot
    simp only [Finset.mem_Icc] at ha
    have ha1 : 1 ≤ a := ha.1
    have hout : ¬ a ≤ U / (g * z) := fun hle => hnot (Finset.mem_Icc.mpr ⟨ha1, hle⟩)
    rw [Nat.le_div_iff_mul_le hgz] at hout
    refine Finset.sum_eq_zero fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    have hb1 : 1 ≤ b := hb.1.1
    have hbig : U < max a b * (g * z) :=
      lt_of_lt_of_le (not_le.mp hout) (Nat.mul_le_mul (le_max_left a b) (le_refl (g * z)))
    rw [min_eq_left (boxOut hg ha1 hb1 hbig)]
    ring

/-- **H7a' (the box).** H4's triple sum over `Icc 1 ⌊u⌋₊` equals the sum over the box
`g ≤ ⌊u⌋₊/z`, `a, b ≤ ⌊u⌋₊/(gz)` of `μ(a)μ(b)·(J(M) − J(L))` — an EXACT identity, with `M =
⌊u⌋₊/(gab)` and `L = z/min(a,b)` in ℕ-division. Inside the box `L ≤ M`, outside it `M ≤ L`
and the term is `J(M) − J(M) = 0`.

⚠ **The box is NON-STRICT, and that is the whole content.** Its boundary terms
(`max(a,b) = ⌊u⌋₊/(gz)`) lie INSIDE and are generally NONZERO — 20 of 190 at the six receipt
points; e.g. at `(z,u) = (2,12)`, `g = 4`, `(a,b) = (1,1)` the term is `+0.164402`. The
must-FAIL control is the STRICT box (`a, b ≤ ⌊u⌋₊/(gz) − 1`), which drops them and is
measurably wrong: `6.920931 ≠ 7.085333` at `(2,12)`, `15.061778 ≠ 15.322721` at `(3,20)`,
`32.219799 ≠ 32.551306` at `(7,49)`.

Receipt: `Σ_{n≤u} T_z(n)²` = this box formula = H4's landed right-hand side, to `1e−13`, at
`(z,u) = (2,12), (3,20), (5,60), (10,150), (7,49), (12,144)` —
`7.085333 / 15.322721 / 64.706581 / 186.179978 / 32.551306 / 154.510577` — and at `(2,30)`,
`(3,40)` beyond `u = z²` (`39.161825 / 45.797006`); the binder `u ≤ z²` is NOT needed. -/
theorem sum_tailT_sq_eq_box {z : ℕ} (hz : 1 ≤ z) {u : ℝ} (hu : 1 ≤ u) :
    ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, tailT z n ^ 2
      = ∑ g ∈ Finset.Icc 1 (⌊u⌋₊ / z), ∑ a ∈ Finset.Icc 1 (⌊u⌋₊ / (g * z)),
          ∑ b ∈ (Finset.Icc 1 (⌊u⌋₊ / (g * z))).filter (fun b => Nat.Coprime a b),
            (moebius a : ℝ) * (moebius b : ℝ)
              * (sqfLogPair z a b (⌊u⌋₊ / (g * a * b)) - sqfLogPair z a b (z / min a b)) := by
  classical
  have hz0 : 0 < z := hz
  have hstep1 : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, tailT z n ^ 2
      = ∑ g ∈ Finset.Icc 1 ⌊u⌋₊, ∑ a ∈ Finset.Icc 1 ⌊u⌋₊,
          ∑ b ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun b => Nat.Coprime a b),
            (moebius a : ℝ) * (moebius b : ℝ)
              * (sqfLogPair z a b (⌊u⌋₊ / (g * a * b))
                  - sqfLogPair z a b (min (⌊u⌋₊ / (g * a * b)) (z / min a b))) := by
    rw [sum_tailT_sq_eq hz hu]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun a ha => ?_
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    rw [sum_filter_side_eq_sqfLogPair_sub z a b _ ha.1 hb.1.1]
  rw [hstep1]
  have hsub : Finset.Icc 1 (⌊u⌋₊ / z) ⊆ Finset.Icc 1 ⌊u⌋₊ := by
    intro g hg
    simp only [Finset.mem_Icc] at hg ⊢
    exact ⟨hg.1, le_trans hg.2 (Nat.div_le_self _ _)⟩
  rw [← Finset.sum_subset hsub ?_]
  · refine Finset.sum_congr rfl fun g hg => ?_
    simp only [Finset.mem_Icc] at hg
    exact boxSumA z g ⌊u⌋₊ hg.1 hz
  · intro g hg hnot
    simp only [Finset.mem_Icc] at hg
    have hg1 : 1 ≤ g := hg.1
    have hout : ¬ g ≤ ⌊u⌋₊ / z := fun hle => hnot (Finset.mem_Icc.mpr ⟨hg1, hle⟩)
    rw [Nat.le_div_iff_mul_le hz0] at hout
    refine Finset.sum_eq_zero fun a ha => ?_
    refine Finset.sum_eq_zero fun b hb => ?_
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    have ha1 : 1 ≤ a := ha.1
    have hb1 : 1 ≤ b := hb.1.1
    have hbig : ⌊u⌋₊ < max a b * (g * z) := by
      refine lt_of_lt_of_le (not_le.mp hout) ?_
      calc g * z = 1 * (g * z) := by ring
        _ ≤ max a b * (g * z) :=
            Nat.mul_le_mul (le_trans ha1 (le_max_left a b)) (le_refl (g * z))
    rw [min_eq_left (boxOut hg1 ha1 hb1 hbig)]
    ring

/-! ## The re-derived private helpers

`GrahamHard2.lean` carries these as `private` lemmas, which cannot be consumed across a
module boundary; each is re-derived here by its landed recipe. -/

private lemma one_le_prod_one_add (r : ℕ) :
    (1 : ℝ) ≤ ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)) := by
  calc (1 : ℝ) = ∏ _p ∈ r.primeFactors, (1 : ℝ) := by rw [Finset.prod_const_one]
    _ ≤ ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)) := by
        refine Finset.prod_le_prod (fun i _ => by norm_num) (fun i _ => ?_)
        have : (0 : ℝ) ≤ 1 / (i : ℝ) := by positivity
        linarith

private lemma le_kappa (r : ℕ) : (r : ℝ) ≤ kappa r := by
  rw [kappa]
  nlinarith [one_le_prod_one_add r, (Nat.cast_nonneg r : (0 : ℝ) ≤ (r : ℝ))]

private lemma kappa_pos (r : ℕ) (hr : 1 ≤ r) : (0 : ℝ) < kappa r := by
  have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  linarith [le_kappa r]

private lemma div_kappa_le_one (r : ℕ) (hr : 1 ≤ r) : (r : ℝ) / kappa r ≤ 1 := by
  rw [div_le_one (kappa_pos r hr)]
  exact le_kappa r

private lemma inv_kappa_le_inv (r : ℕ) (hr : 1 ≤ r) : 1 / kappa r ≤ 1 / (r : ℝ) := by
  have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  exact one_div_le_one_div_of_le (by linarith) (le_kappa r)

/-- `|ρ₀| ≤ 2`: the series is dominated termwise by `1/n²`, whose sum is `π²/6 < 2`. -/
private lemma abs_rho0_le_two : |rho0| ≤ 2 := by
  have hb : ∀ n : ℕ, ‖(moebius n : ℝ) / (n : ℝ) ^ 2‖ ≤ 1 / (n : ℝ) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
      exact (div_le_div_iff_of_pos_right (by positivity)).mpr hmu
  have h := tsum_of_norm_bounded hasSum_zeta_two hb
  rw [Real.norm_eq_abs] at h
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hbound : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith
  have hr : rho0 = ∑' n : ℕ, (moebius n : ℝ) / (n : ℝ) ^ 2 := rfl
  rw [hr]
  linarith

private lemma sum_inv_le_one_add_log (m : ℕ) :
    ∑ f ∈ Finset.Icc 1 m, ((f : ℝ))⁻¹ ≤ 1 + Real.log m := by
  have h := harmonic_le_one_add_log m
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-- `1 + log Q ≤ (1/log 2)·log(2Q)` for `Q ≥ 1` — the bridge that turns every
`(1 + log Q)` numerator into a `log(2Q)` the denominators can absorb. -/
private lemma one_add_log_le_inv_log_two_mul (Q : ℝ) (hQ : 1 ≤ Q) :
    1 + Real.log Q ≤ (1 / Real.log 2) * Real.log (2 * Q) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  rw [Real.log_mul (by norm_num) (ne_of_gt hQ0), one_div, inv_mul_eq_div, le_div_iff₀ hlog2]
  nlinarith [mul_nonneg hlogQ (by linarith : (0 : ℝ) ≤ 1 - Real.log 2)]

/-! ## II. THE EVALUATION (H5c instantiated) -/

/-- **H7b (An's evaluation of the inner sum).** `J_z(a, b; ⌊Y⌋) = ρ₀·(ab/κ(ab))·Y·
((log(aY/z) − 1)(log(bY/z) − 1) + 1) + O(√Y·σ(ab)·(1 + |log(aY/z)|)(1 + |log(bY/z)|))`.

This is H5c (`sqf_coprime_sum_log_mul_log_eq`) at `r = ab`, `M = Y`, `α = log(a/z)`,
`β = log(b/z)`: `log(ak/z) = log k + α`, so H5c's one-variable pair `(1 + |log M + α|)
(1 + |log M + β|)` reads as the frozen weight. H5c carries a REAL `M` with `⌊M⌋₊` in the
range, so there is no floor error anywhere.

⚠ `1 ≤ z` is LOAD-BEARING: at `z = 0` Lean's `log 0 = 0` makes the main term
`2ρ₀(ab/κ(ab))Y`, which outgrows `C√Y·σ(ab)`.

The must-FAIL control, with the density `(ab/κ(ab))` inverted to `(κ(ab)/(ab))` at
`(z, a, b) = (10, 2, 3)`: the ratio to the weight is `0.921 / 4.481 / 17.16 / 60.55` at
`Y = 10², 10³, 10⁴, 10⁵` — unbounded (it grows like `√Y`). RECORDED WITH ITS SLOW GROWTH
rather than as a clean kill: the weaker mutation dropping the main term's `+ 1` gives
`0.059 / 0.062 / 0.128 / 0.242`, which grows only like `√Y/log²Y` and is a kill
asymptotically alone. Frozen receipt: `|J − main|/weight` over `z ∈ {2, 10, 100}`, six
pairs `(a,b)`, `Y ∈ {1, 2.5, 10, 10², 10³, 10⁴}` (108 points) is worst `0.8271`
at `(2, 1, 1, 2.5)`. -/
theorem abs_sqfLogPair_sub_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 1 ≤ z → ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ∀ Y : ℝ, 1 ≤ Y →
    |sqfLogPair z a b ⌊Y⌋₊
        - rho0 * (((a * b : ℕ) : ℝ) / kappa (a * b)) * Y
            * ((Real.log ((a : ℝ) * Y / z) - 1) * (Real.log ((b : ℝ) * Y / z) - 1) + 1)|
      ≤ C * Y ^ (1/2 : ℝ) * sigmaQ (a * b)
          * (1 + |Real.log ((a : ℝ) * Y / z)|) * (1 + |Real.log ((b : ℝ) * Y / z)|) := by
  classical
  obtain ⟨C, hC, h5c⟩ := sqf_coprime_sum_log_mul_log_eq
  refine ⟨C, hC, fun z hz a b ha hb Y hY => ?_⟩
  have hz0 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hY0 : (0 : ℝ) < Y := by linarith
  have hab1 : 1 ≤ a * b :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have key := h5c (a * b) hab1 Y hY (Real.log ((a : ℝ) / z)) (Real.log ((b : ℝ) / z))
  have hLHS : sqfLogPair z a b ⌊Y⌋₊
      = ∑ m ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun m => Nat.Coprime m (a * b)),
          (moebius m : ℝ) ^ 2 * (Real.log m + Real.log ((a : ℝ) / z))
            * (Real.log m + Real.log ((b : ℝ) / z)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1.1
    rw [Nat.cast_mul, Nat.cast_mul,
      show (a : ℝ) * (k : ℝ) / z = ((a : ℝ) / z) * (k : ℝ) by ring,
      show (b : ℝ) * (k : ℝ) / z = ((b : ℝ) / z) * (k : ℝ) by ring,
      Real.log_mul (by positivity) (ne_of_gt hk0),
      Real.log_mul (by positivity) (ne_of_gt hk0)]
    ring
  have hA : Real.log ((a : ℝ) * Y / z) = Real.log Y + Real.log ((a : ℝ) / z) := by
    rw [show (a : ℝ) * Y / z = ((a : ℝ) / z) * Y by ring,
      Real.log_mul (by positivity) (ne_of_gt hY0)]
    ring
  have hB : Real.log ((b : ℝ) * Y / z) = Real.log Y + Real.log ((b : ℝ) / z) := by
    rw [show (b : ℝ) * Y / z = ((b : ℝ) / z) * Y by ring,
      Real.log_mul (by positivity) (ne_of_gt hY0)]
    ring
  rw [hLHS, hA, hB,
    show Real.log Y + Real.log ((a : ℝ) / z) - 1
      = Real.log Y - 1 + Real.log ((a : ℝ) / z) from by ring,
    show Real.log Y + Real.log ((b : ℝ) / z) - 1
      = Real.log Y - 1 + Real.log ((b : ℝ) / z) from by ring]
  exact key

/-! ## III. ΣA -/

/-- `σ_{−1/4} ≥ 0`. -/
private lemma sigmaQ_nonneg (r : ℕ) : (0 : ℝ) ≤ sigmaQ r :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

private lemma abs_moebius_cast_le_one (n : ℕ) : |(moebius n : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

private lemma abs_sub_le_add' (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [sub_eq_add_neg]
  refine le_trans (abs_add_le _ _) (le_of_eq ?_)
  rw [abs_neg]

private lemma abs_add_sub_le (x y z : ℝ) : |x + y - z| ≤ |x - z| + |y| := by
  have h : x + y - z = x - z + y := by ring
  rw [h]
  exact abs_add_le _ _

private lemma log_rpow_four_eq (Q : ℝ) : Real.log (2 * Q) ^ (4 : ℝ) = Real.log (2 * Q) ^ 4 := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private lemma log_rpow_two_eq (Q : ℝ) : Real.log (2 * Q) ^ (2 : ℝ) = Real.log (2 * Q) ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The `a`-term of ΣA's error, bounded by `(3 + 2 log Q)·(C₁ + C₂)·σ(a)/(a·log(2Q)^4)`.
Off squarefree `a` the term is `0` (its factor is `μ(a)`), so H6e and H6f are consumed
only where their `Squarefree` hypothesis holds. The factor `|b₀| + |1 − b₀| ≤ 3 + 2 log Q`
is sharp at `Q = a = 1`, where it is exactly `3`. -/
private lemma aKernel_err_term_le {C1 C2 : ℝ} (hC1 : 0 < C1) (hC2 : 0 < C2)
    (h6e : ∀ t : ℕ, Squarefree t → ∀ Q : ℝ, 1 ≤ Q →
      |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
          (moebius n : ℝ) / kappa n * Real.log (Q / n) - c0 * kappa t / t|
        ≤ C1 * sigmaQ t / Real.log (2 * Q) ^ (4 : ℝ))
    (h6f : ∀ t : ℕ, Squarefree t → ∀ Q : ℝ, 1 ≤ Q →
      |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
          (moebius n : ℝ) / kappa n| ≤ C2 * sigmaQ t / Real.log (2 * Q) ^ (4 : ℝ))
    (Q : ℝ) (hQ : 1 ≤ Q) (a : ℕ) (ha1 : 1 ≤ a) (haQ : (a : ℝ) ≤ Q) :
    |(moebius a : ℝ) / kappa a
        * ((Real.log (Q / a) - 1)
            * ((∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                  (moebius n : ℝ) / kappa n * Real.log (Q / n)) - c0 * kappa a / a)
          + (1 - (Real.log (Q / a) - 1))
            * (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                  (moebius n : ℝ) / kappa n))|
      ≤ (3 + 2 * Real.log Q) * (C1 + C2) / Real.log (2 * Q) ^ 4 * (sigmaQ a / a) := by
  classical
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  have hka : (0 : ℝ) < kappa a := kappa_pos a ha1
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hL : (0 : ℝ) < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hL4 : (0 : ℝ) < Real.log (2 * Q) ^ 4 := by positivity
  have hlogQ : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hsig : (0 : ℝ) ≤ sigmaQ a := sigmaQ_nonneg a
  have hRHS : (0 : ℝ) ≤ (3 + 2 * Real.log Q) * (C1 + C2) / Real.log (2 * Q) ^ 4
      * (sigmaQ a / a) := by
    have h1 : (0 : ℝ) ≤ 3 + 2 * Real.log Q := by linarith
    have h2 : (0 : ℝ) ≤ (3 + 2 * Real.log Q) * (C1 + C2) := by nlinarith
    positivity
  by_cases hsq : Squarefree a
  · have e1 := h6e a hsq Q hQ
    have e2 := h6f a hsq Q hQ
    rw [log_rpow_four_eq] at e1 e2
    have hlogQa0 : (0 : ℝ) ≤ Real.log (Q / a) :=
      Real.log_nonneg ((one_le_div ha0).mpr haQ)
    have hloga : (0 : ℝ) ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast ha1)
    have hlogQa : Real.log (Q / a) ≤ Real.log Q := by
      rw [Real.log_div (ne_of_gt hQ0) (ne_of_gt ha0)]; linarith
    have hc1 : |Real.log (Q / a) - 1| ≤ 1 + Real.log Q := by
      rw [abs_le]; constructor <;> linarith
    have hc2 : |1 - (Real.log (Q / a) - 1)| ≤ 2 + Real.log Q := by
      rw [abs_le]; constructor <;> linarith
    have hkinv : |(moebius a : ℝ) / kappa a| ≤ 1 / (a : ℝ) := by
      rw [abs_div, abs_of_pos hka]
      calc |(moebius a : ℝ)| / kappa a ≤ 1 / kappa a := by
            gcongr
            exact abs_moebius_cast_le_one a
        _ ≤ 1 / (a : ℝ) := inv_kappa_le_inv a ha1
    have habs : |(Real.log (Q / a) - 1)
          * ((∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                (moebius n : ℝ) / kappa n * Real.log (Q / n)) - c0 * kappa a / a)
        + (1 - (Real.log (Q / a) - 1))
          * (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                (moebius n : ℝ) / kappa n)|
        ≤ (1 + Real.log Q) * (C1 * sigmaQ a / Real.log (2 * Q) ^ 4)
          + (2 + Real.log Q) * (C2 * sigmaQ a / Real.log (2 * Q) ^ 4) := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul hc1 e1 (abs_nonneg _) (by linarith))
        (mul_le_mul hc2 e2 (abs_nonneg _) (by linarith))
    rw [abs_mul]
    have hcoef : (1 + Real.log Q) * C1 + (2 + Real.log Q) * C2
        ≤ (3 + 2 * Real.log Q) * (C1 + C2) := by
      nlinarith [mul_nonneg hlogQ hC1.le, mul_nonneg hlogQ hC2.le]
    have hposf : (0 : ℝ) ≤ sigmaQ a / ((a : ℝ) * Real.log (2 * Q) ^ 4) := by positivity
    have hstep : |(moebius a : ℝ) / kappa a|
        * ((1 + Real.log Q) * (C1 * sigmaQ a / Real.log (2 * Q) ^ 4)
          + (2 + Real.log Q) * (C2 * sigmaQ a / Real.log (2 * Q) ^ 4))
        ≤ (3 + 2 * Real.log Q) * (C1 + C2) / Real.log (2 * Q) ^ 4 * (sigmaQ a / a) := by
      have hb : (0 : ℝ) ≤ (1 + Real.log Q) * (C1 * sigmaQ a / Real.log (2 * Q) ^ 4)
          + (2 + Real.log Q) * (C2 * sigmaQ a / Real.log (2 * Q) ^ 4) := by positivity
      refine le_trans (mul_le_mul_of_nonneg_right hkinv hb) ?_
      have heq1 : 1 / (a : ℝ) * ((1 + Real.log Q) * (C1 * sigmaQ a / Real.log (2 * Q) ^ 4)
          + (2 + Real.log Q) * (C2 * sigmaQ a / Real.log (2 * Q) ^ 4))
          = ((1 + Real.log Q) * C1 + (2 + Real.log Q) * C2)
            * (sigmaQ a / ((a : ℝ) * Real.log (2 * Q) ^ 4)) := by
        field_simp
      have heq2 : (3 + 2 * Real.log Q) * (C1 + C2) / Real.log (2 * Q) ^ 4 * (sigmaQ a / a)
          = ((3 + 2 * Real.log Q) * (C1 + C2))
            * (sigmaQ a / ((a : ℝ) * Real.log (2 * Q) ^ 4)) := by
        field_simp
      rw [heq1, heq2]
      exact mul_le_mul_of_nonneg_right hcoef hposf
    exact le_trans (mul_le_mul_of_nonneg_left habs (abs_nonneg _)) hstep
  · have hmu : (moebius a : ℝ) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; norm_num
    rw [hmu]
    simpa using hRHS

/-- **H7c (ΣA's kernel tends to `c₀`).** `|aKernel Q − c₀| ≤ C/(log 2Q)²`.

The `b`-sum at fixed `a`, with `b₀ := log(Q/a) − 1` CONSTANT in `b`, is
`b₀·[H6e at (a, Q)] + (1 − b₀)·[H6f at (a, Q)]`, both at `A = 4`; H6e's main term
`c₀·κ(a)/a` cancels the outer `1/κ(a)` into `c₀·μ(a)/a`, and the `a`-sum of the main part
is `c₀·(T(Q) − f(Q))`, closed by **C3** (`T = 1 + O((log 2Q)^{−2})`) and **H6b**
(`f = O((log 2Q)^{−2})`). The error sum runs `(3 + 2 log Q)·(log 2Q)^{−4}·Σ_{a≤Q} σ(a)/a`
against **H0e**, and `1 + log Q ≤ (1/log 2)·log 2Q` turns it into `(log 2Q)^{−2}`.

**`A = 4` at H6e/H6f is load-bearing** (K42): the `E₃` sum carries `(1 + log Q)²`, so
`A = 3` would leave a `1/log`.

⚠ The constant `c₀` here is the DEFINED `c0 = Σ' μ(n)²/(κ(n)φ(n))`. That it equals `ζ(2)`
(by the Euler product `∏ p²/(p² − 1)`) is a receipt and is never used; `ρ₀c₀ = 1` is true
and never used; the sign of neither is used.

The must-FAIL control, `c₀ → ρ₀`: `|aKernel Q − ρ₀|·(log 2Q)² = 26.7 / 59.2 / 102.4` at
`Q = 10², 10³, 10⁴` — unbounded. The frozen quantity `|aKernel Q − c₀|·(log 2Q)²` measures
`5.24 / 0.64 / 2.44 / 1.29 / 0.67 / 0.34 / 0.68 / 0.27` at
`Q = 10, 30, 10², 300, 10³, 3·10³, 10⁴, 3·10⁴` (bounded, tending to `0`;
`aKernel(3·10⁴) = 1.642738` against `c₀ = ζ(2) = 1.644934`). At the zero level `Q = 1`,
`aKernel 1 = 2` (the `a = b = 1` term) and `|2 − c₀| = 0.355 ≤ C/(log 2)²`. -/
theorem abs_aKernel_sub_c0_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q →
    |aKernel Q - c0| ≤ C / Real.log (2 * Q) ^ 2 := by
  classical
  obtain ⟨C1, hC1, h6e⟩ := coprime_sum_moebius_div_kappa_log_eq 4 (by norm_num)
  obtain ⟨C2, hC2, h6f⟩ := coprime_sum_moebius_div_kappa_le 4 (by norm_num)
  obtain ⟨C3, hC3, hc3⟩ := abs_sum_moebius_div_mul_log_div_sub_one_le 2 (by norm_num)
  obtain ⟨C4, hC4, h6b⟩ := abs_sum_moebius_div_le_inv_log_pow 2 (by norm_num)
  obtain ⟨C5, hC5, h0e⟩ := sum_sigmaQ_div_le
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : (1 : ℝ) ≤ c0 := one_le_c0
  have hc0pos : (0 : ℝ) < c0 := by linarith
  refine ⟨c0 * (C3 + C4) + 3 * (C1 + C2) * C5 / Real.log 2 ^ 2, ?_, fun Q hQ => ?_⟩
  · have h1 : 0 < c0 * (C3 + C4) := mul_pos hc0pos (by linarith)
    have h2 : 0 < 3 * (C1 + C2) * C5 / Real.log 2 ^ 2 := by positivity
    linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlogQ : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hL : (0 : ℝ) < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hL2 : (0 : ℝ) < Real.log (2 * Q) ^ 2 := by positivity
  have hL4 : (0 : ℝ) < Real.log (2 * Q) ^ 4 := by positivity
  have hNQ : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le hQ0.le
  -- the per-`a` identity: the `b`-sum split against H6e's main term
  have hterm : ∀ a ∈ Finset.Icc 1 ⌊Q⌋₊,
      (∑ b ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => Nat.Coprime a b),
        (moebius a : ℝ) / kappa a * ((moebius b : ℝ) / kappa b)
          * ((Real.log (Q / b) - 1) * (Real.log (Q / a) - 1) + 1))
      = c0 * ((moebius a : ℝ) / a * Real.log (Q / a) - (moebius a : ℝ) / a)
        + (moebius a : ℝ) / kappa a
          * ((Real.log (Q / a) - 1)
              * ((∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                    (moebius n : ℝ) / kappa n * Real.log (Q / n)) - c0 * kappa a / a)
            + (1 - (Real.log (Q / a) - 1))
              * (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                    (moebius n : ℝ) / kappa n)) := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    have ha1 : 1 ≤ a := ha.1
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
    have hka : (0 : ℝ) < kappa a := kappa_pos a ha1
    have hfil : (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => Nat.Coprime a b)
        = (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a) :=
      Finset.filter_congr fun x _ => Nat.coprime_comm
    rw [hfil]
    have expand : ∀ b : ℕ, (moebius a : ℝ) / kappa a * ((moebius b : ℝ) / kappa b)
          * ((Real.log (Q / b) - 1) * (Real.log (Q / a) - 1) + 1)
        = (moebius a : ℝ) / kappa a * (Real.log (Q / a) - 1)
            * ((moebius b : ℝ) / kappa b * Real.log (Q / b))
          + (moebius a : ℝ) / kappa a * (1 - (Real.log (Q / a) - 1))
            * ((moebius b : ℝ) / kappa b) := by
      intro b; ring
    rw [Finset.sum_congr rfl (fun b _ => expand b), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    field_simp
    ring
  have haK : aKernel Q
      = c0 * ((∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a * Real.log (Q / a))
              - ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a)
        + ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / kappa a
            * ((Real.log (Q / a) - 1)
                * ((∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                      (moebius n : ℝ) / kappa n * Real.log (Q / n)) - c0 * kappa a / a)
              + (1 - (Real.log (Q / a) - 1))
                * (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                      (moebius n : ℝ) / kappa n)) := by
    rw [aKernel, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib]
  -- the main term
  have hmainT := hc3 Q hQ
  have hmainf := h6b Q hQ
  rw [log_rpow_two_eq] at hmainT hmainf
  have hmain : |c0 * ((∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a * Real.log (Q / a))
              - ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a) - c0|
      ≤ c0 * (C3 + C4) / Real.log (2 * Q) ^ 2 := by
    have hrw : c0 * ((∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a * Real.log (Q / a))
              - ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a) - c0
        = c0 * (((∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a * Real.log (Q / a)) - 1)
              - ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a) := by ring
    rw [hrw, abs_mul, abs_of_pos hc0pos]
    have hsub : |((∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a * Real.log (Q / a)) - 1)
          - ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a|
        ≤ (C3 + C4) / Real.log (2 * Q) ^ 2 := by
      refine le_trans (abs_sub_le_add' _ _) ?_
      rw [add_div]
      exact add_le_add hmainT hmainf
    calc c0 * |((∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a * Real.log (Q / a)) - 1)
            - ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / a|
        ≤ c0 * ((C3 + C4) / Real.log (2 * Q) ^ 2) :=
          mul_le_mul_of_nonneg_left hsub hc0pos.le
      _ = c0 * (C3 + C4) / Real.log (2 * Q) ^ 2 := by ring
  -- the error term
  have herr : |∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius a : ℝ) / kappa a
            * ((Real.log (Q / a) - 1)
                * ((∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                      (moebius n : ℝ) / kappa n * Real.log (Q / n)) - c0 * kappa a / a)
              + (1 - (Real.log (Q / a) - 1))
                * (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                      (moebius n : ℝ) / kappa n))|
      ≤ 3 * (C1 + C2) * C5 / Real.log 2 ^ 2 / Real.log (2 * Q) ^ 2 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hbd : ∀ a ∈ Finset.Icc 1 ⌊Q⌋₊,
        |(moebius a : ℝ) / kappa a
            * ((Real.log (Q / a) - 1)
                * ((∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                      (moebius n : ℝ) / kappa n * Real.log (Q / n)) - c0 * kappa a / a)
              + (1 - (Real.log (Q / a) - 1))
                * (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n a),
                      (moebius n : ℝ) / kappa n))|
        ≤ (3 + 2 * Real.log Q) * (C1 + C2) / Real.log (2 * Q) ^ 4 * (sigmaQ a / a) := by
      intro a ha
      simp only [Finset.mem_Icc] at ha
      have haQ : (a : ℝ) ≤ Q := le_trans (by exact_mod_cast ha.2) hNQ
      exact aKernel_err_term_le hC1 hC2 h6e h6f Q hQ a ha.1 haQ
    refine le_trans (Finset.sum_le_sum hbd) ?_
    rw [← Finset.mul_sum]
    have hfac : (0 : ℝ) ≤ (3 + 2 * Real.log Q) * (C1 + C2) / Real.log (2 * Q) ^ 4 := by
      have h1 : (0 : ℝ) ≤ 3 + 2 * Real.log Q := by linarith
      have h2 : (0 : ℝ) ≤ (3 + 2 * Real.log Q) * (C1 + C2) := by nlinarith
      positivity
    refine le_trans (mul_le_mul_of_nonneg_left (h0e Q hQ) hfac) ?_
    -- `(3 + 2 log Q)(1 + log Q) ≤ 3 (log 2Q)²/log²2`
    have hbridge : 1 + Real.log Q ≤ (1 / Real.log 2) * Real.log (2 * Q) :=
      one_add_log_le_inv_log_two_mul Q hQ
    have hsqb : (1 + Real.log Q) ^ 2 ≤ Real.log (2 * Q) ^ 2 / Real.log 2 ^ 2 := by
      have h0 : (0 : ℝ) ≤ 1 + Real.log Q := by linarith
      have hms := mul_self_le_mul_self h0 hbridge
      calc (1 + Real.log Q) ^ 2 = (1 + Real.log Q) * (1 + Real.log Q) := by ring
        _ ≤ 1 / Real.log 2 * Real.log (2 * Q) * (1 / Real.log 2 * Real.log (2 * Q)) := hms
        _ = Real.log (2 * Q) ^ 2 / Real.log 2 ^ 2 := by field_simp
    have hA : (3 + 2 * Real.log Q) * (1 + Real.log Q)
        ≤ 3 * (Real.log (2 * Q) ^ 2 / Real.log 2 ^ 2) := by
      have h3 : (3 + 2 * Real.log Q) * (1 + Real.log Q) ≤ 3 * (1 + Real.log Q) ^ 2 := by
        nlinarith
      linarith [mul_le_mul_of_nonneg_left hsqb (by norm_num : (0 : ℝ) ≤ 3)]
    have hCC : (0 : ℝ) < (C1 + C2) * C5 := by
      have : (0 : ℝ) < C1 + C2 := by linarith
      exact mul_pos this hC5
    calc (3 + 2 * Real.log Q) * (C1 + C2) / Real.log (2 * Q) ^ 4 * (C5 * (1 + Real.log Q))
        = (3 + 2 * Real.log Q) * (1 + Real.log Q) * ((C1 + C2) * C5)
            / Real.log (2 * Q) ^ 4 := by ring
      _ ≤ 3 * (Real.log (2 * Q) ^ 2 / Real.log 2 ^ 2) * ((C1 + C2) * C5)
            / Real.log (2 * Q) ^ 4 :=
          (div_le_div_iff_of_pos_right hL4).mpr (mul_le_mul_of_nonneg_right hA hCC.le)
      _ = 3 * (C1 + C2) * C5 / Real.log 2 ^ 2 / Real.log (2 * Q) ^ 2 := by
          field_simp
  rw [haK]
  refine le_trans (abs_add_sub_le _ _ _) ?_
  refine le_trans (add_le_add hmain herr) (le_of_eq ?_)
  ring

/-- **H7c' (the `g`-sum of the A-kernel).** `Σ_{g ≤ X} (1/g)·|aKernel(X/g)| ≤ C(1 + log X)`:
`|aKernel(X/g)| ≤ c₀ + C/(log(2X/g))²` by H7c at `Q = X/g ≥ 1`, then
`Σ 1/g ≤ 1 + log X` (`harmonic_le_one_add_log`) and
`Σ 1/(g·log²(2X/g)) ≤ C₀` (**H0c**, `sum_inv_mul_log_sq_le`, on the nose).

⚠ `1 ≤ X` is LOAD-BEARING: at `X < 1/e` the right-hand side `1 + log X` is negative while
the left-hand side is `≥ 0`. H7's route never reaches this row below `X = u/z = 1`. -/
theorem sum_inv_mul_abs_aKernel_le : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    ∑ g ∈ Finset.Icc 1 ⌊X⌋₊, 1 / (g : ℝ) * |aKernel (X / g)| ≤ C * (1 + Real.log X) := by
  classical
  obtain ⟨Ca, hCa, ha⟩ := abs_aKernel_sub_c0_le
  obtain ⟨C0, hC0, h0c⟩ := sum_inv_mul_log_sq_le
  have hc0 : (1 : ℝ) ≤ c0 := one_le_c0
  have hc0pos : (0 : ℝ) < c0 := by linarith
  refine ⟨c0 + Ca * C0, by positivity, fun X hX => ?_⟩
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX
  have hNX : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
  have hN1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hterm : ∀ g ∈ Finset.Icc 1 ⌊X⌋₊, 1 / (g : ℝ) * |aKernel (X / g)|
      ≤ c0 * ((g : ℝ))⁻¹ + Ca * (1 / ((g : ℝ) * Real.log (2 * X / g) ^ 2)) := by
    intro g hg
    simp only [Finset.mem_Icc] at hg
    have hg1 : 1 ≤ g := hg.1
    have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg1
    have hgX : (g : ℝ) ≤ X := le_trans (by exact_mod_cast hg.2) hNX
    have hQ1 : (1 : ℝ) ≤ X / g := (one_le_div hg0).mpr hgX
    have hbd := ha (X / g) hQ1
    have h2 : (2 : ℝ) * (X / g) = 2 * X / g := by ring
    rw [h2] at hbd
    have hL : (0 : ℝ) < Real.log (2 * X / g) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hg0]
      linarith
    have habs : |aKernel (X / g)| ≤ c0 + Ca / Real.log (2 * X / g) ^ 2 := by
      have := abs_sub_abs_le_abs_sub (aKernel (X / g)) c0
      rw [abs_of_pos hc0pos] at this
      linarith
    have hnn : (0 : ℝ) ≤ 1 / (g : ℝ) := by positivity
    calc 1 / (g : ℝ) * |aKernel (X / g)|
        ≤ 1 / (g : ℝ) * (c0 + Ca / Real.log (2 * X / g) ^ 2) :=
          mul_le_mul_of_nonneg_left habs hnn
      _ = c0 * ((g : ℝ))⁻¹ + Ca * (1 / ((g : ℝ) * Real.log (2 * X / g) ^ 2)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ g ∈ Finset.Icc 1 ⌊X⌋₊, ((g : ℝ))⁻¹ ≤ 1 + Real.log X := by
    refine le_trans (sum_inv_le_one_add_log ⌊X⌋₊) ?_
    have : Real.log ((⌊X⌋₊ : ℕ) : ℝ) ≤ Real.log X :=
      Real.log_le_log (by exact_mod_cast hN1) hNX
    linarith
  have h2 : ∑ g ∈ Finset.Icc 1 ⌊X⌋₊, 1 / ((g : ℝ) * Real.log (2 * X / g) ^ 2) ≤ C0 :=
    h0c X hX
  calc c0 * ∑ g ∈ Finset.Icc 1 ⌊X⌋₊, ((g : ℝ))⁻¹
        + Ca * ∑ g ∈ Finset.Icc 1 ⌊X⌋₊, 1 / ((g : ℝ) * Real.log (2 * X / g) ^ 2)
      ≤ c0 * (1 + Real.log X) + Ca * C0 := by
        exact add_le_add (mul_le_mul_of_nonneg_left h1 hc0pos.le)
          (mul_le_mul_of_nonneg_left h2 hCa.le)
    _ ≤ (c0 + Ca * C0) * (1 + Real.log X) := by nlinarith [mul_pos hCa hC0]

/-! ## IV. ΣB + ΣC -/

/-- `log(2Q)² ≤ 128·Q^{1/4}` — the A4 helper `log_rpow_le_rpow_quarter` at `A = 2`,
`x = 2Q`, with the rpow/npow bridge `Real.rpow_two`. -/
private lemma log_sq_le_rpow_quarter (Q : ℝ) (hQ : 1 ≤ Q) :
    Real.log (2 * Q) ^ 2 ≤ 128 * Q ^ (1/4 : ℝ) := by
  have h2Q : (1 : ℝ) ≤ 2 * Q := by linarith
  have h := log_rpow_le_rpow_quarter 2 (by norm_num) h2Q
  rw [Real.rpow_two] at h
  have hc : ((4 : ℝ) * 2) ^ (2 : ℝ) = 64 := by rw [Real.rpow_two]; norm_num
  rw [hc, Real.mul_rpow (by norm_num) (by linarith)] at h
  have h2 : (2 : ℝ) ^ (1/4 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1/4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hQq : (0 : ℝ) ≤ Q ^ (1/4 : ℝ) := Real.rpow_nonneg (by linarith) _
  nlinarith

/-- `√Q·log(2Q)² ≤ 128·Q` — the same helper, folded to the shape H7d's two-range
`Σ σ(b)/log²(2b)` needs. -/
private lemma rpow_half_mul_log_sq_le (Q : ℝ) (hQ : 1 ≤ Q) :
    Q ^ (1/2 : ℝ) * Real.log (2 * Q) ^ 2 ≤ 128 * Q := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have h1 := log_sq_le_rpow_quarter Q hQ
  have hhalf : (0 : ℝ) ≤ Q ^ (1/2 : ℝ) := Real.rpow_nonneg hQ0.le _
  have hadd : Q ^ (1/2 : ℝ) * Q ^ (1/4 : ℝ) = Q ^ (3/4 : ℝ) := by
    rw [← Real.rpow_add hQ0]
    norm_num
  have hle : Q ^ (3/4 : ℝ) ≤ Q := by
    calc Q ^ (3/4 : ℝ) ≤ Q ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
      _ = Q := Real.rpow_one Q
  calc Q ^ (1/2 : ℝ) * Real.log (2 * Q) ^ 2
      ≤ Q ^ (1/2 : ℝ) * (128 * Q ^ (1/4 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h1 hhalf
    _ = 128 * (Q ^ (1/2 : ℝ) * Q ^ (1/4 : ℝ)) := by ring
    _ = 128 * Q ^ (3/4 : ℝ) := by rw [hadd]
    _ ≤ 128 * Q := by linarith

/-- **The two-range `σ`-sum of H7d.** `Σ_{b ≤ Q} σ(b)/log²(2b) ≤ C·Q/log²(2Q)`: on
`b ≤ √Q` use `log 2b ≥ log 2` and H0b at `R = √Q` (`Σσ ≤ 5√Q`, then `√Q ≤ 128Q/log²2Q`);
on `b > √Q` use `log 2b ≥ ½·log 2Q` and H0b at `R = Q`. -/
private lemma sum_sigmaQ_div_log_sq_le (Q : ℝ) (hQ : 1 ≤ Q) :
    ∑ b ∈ Finset.Icc 1 ⌊Q⌋₊, sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2
      ≤ (640 / Real.log 2 ^ 2 + 20) * Q / Real.log (2 * Q) ^ 2 := by
  classical
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (0 : ℝ) < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hR1 : (1 : ℝ) ≤ Q ^ (1/2 : ℝ) := by
    have h0 : Q ^ (0 : ℝ) ≤ Q ^ (1/2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
    rwa [Real.rpow_zero] at h0
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊Q⌋₊)
    (fun b => b ≤ ⌊Q ^ (1/2 : ℝ)⌋₊) (fun b => sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2)
  have hpart1 : ∑ b ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => b ≤ ⌊Q ^ (1/2 : ℝ)⌋₊),
      sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2 ≤ 5 * Q ^ (1/2 : ℝ) / Real.log 2 ^ 2 := by
    have hsub : (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => b ≤ ⌊Q ^ (1/2 : ℝ)⌋₊)
        ⊆ Finset.Icc 1 ⌊Q ^ (1/2 : ℝ)⌋₊ := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
      exact ⟨hx.1.1, hx.2⟩
    have hterm : ∀ b ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => b ≤ ⌊Q ^ (1/2 : ℝ)⌋₊),
        sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2 ≤ sigmaQ b / Real.log 2 ^ 2 := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_Icc] at hb
      have hb0 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.1.1
      have hlb : Real.log 2 ≤ Real.log (2 * (b : ℝ)) :=
        Real.log_le_log (by norm_num) (by linarith)
      exact div_le_div_of_nonneg_left (sigmaQ_nonneg b) (by positivity) (by nlinarith)
    calc ∑ b ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => b ≤ ⌊Q ^ (1/2 : ℝ)⌋₊),
          sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2
        ≤ ∑ b ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => b ≤ ⌊Q ^ (1/2 : ℝ)⌋₊),
            sigmaQ b / Real.log 2 ^ 2 := Finset.sum_le_sum hterm
      _ ≤ ∑ b ∈ Finset.Icc 1 ⌊Q ^ (1/2 : ℝ)⌋₊, sigmaQ b / Real.log 2 ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => div_nonneg (sigmaQ_nonneg i) (by positivity))
      _ = (∑ b ∈ Finset.Icc 1 ⌊Q ^ (1/2 : ℝ)⌋₊, sigmaQ b) / Real.log 2 ^ 2 := by
          rw [Finset.sum_div]
      _ ≤ 5 * Q ^ (1/2 : ℝ) / Real.log 2 ^ 2 :=
          (div_le_div_iff_of_pos_right (by positivity)).mpr
            (sum_sigmaQ_le (Q ^ (1/2 : ℝ)) hR1)
  have hpart2 : ∑ b ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => ¬ b ≤ ⌊Q ^ (1/2 : ℝ)⌋₊),
      sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2 ≤ 20 * Q / Real.log (2 * Q) ^ 2 := by
    have hterm : ∀ b ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => ¬ b ≤ ⌊Q ^ (1/2 : ℝ)⌋₊),
        sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2 ≤ 4 * sigmaQ b / Real.log (2 * Q) ^ 2 := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_Icc, not_le] at hb
      have hb0 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.1.1
      have hRb : Q ^ (1/2 : ℝ) < (b : ℝ) := by
        have h1 : Q ^ (1/2 : ℝ) < ((⌊Q ^ (1/2 : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        have h2 : ((⌊Q ^ (1/2 : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hb.2
        linarith
      have hlogR : Real.log (2 * Q ^ (1/2 : ℝ)) = Real.log 2 + (1/2) * Real.log Q := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hQ0]
      have hle : Real.log (2 * Q ^ (1/2 : ℝ)) ≤ Real.log (2 * (b : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      have hLQ : Real.log (2 * Q) = Real.log 2 + Real.log Q :=
        Real.log_mul (by norm_num) (ne_of_gt hQ0)
      have hhalf : Real.log (2 * Q) / 2 ≤ Real.log (2 * (b : ℝ)) := by
        rw [hlogR] at hle
        rw [hLQ]
        linarith
      have hpos : (0 : ℝ) < Real.log (2 * Q) ^ 2 / 4 := by positivity
      have hsq : Real.log (2 * Q) ^ 2 / 4 ≤ Real.log (2 * (b : ℝ)) ^ 2 := by nlinarith
      calc sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2
          ≤ sigmaQ b / (Real.log (2 * Q) ^ 2 / 4) :=
            div_le_div_of_nonneg_left (sigmaQ_nonneg b) hpos hsq
        _ = 4 * sigmaQ b / Real.log (2 * Q) ^ 2 := by rw [div_div_eq_mul_div]; ring
    calc ∑ b ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => ¬ b ≤ ⌊Q ^ (1/2 : ℝ)⌋₊),
          sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2
        ≤ ∑ b ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun b => ¬ b ≤ ⌊Q ^ (1/2 : ℝ)⌋₊),
            4 * sigmaQ b / Real.log (2 * Q) ^ 2 := Finset.sum_le_sum hterm
      _ ≤ ∑ b ∈ Finset.Icc 1 ⌊Q⌋₊, 4 * sigmaQ b / Real.log (2 * Q) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => by
              have := sigmaQ_nonneg i
              positivity)
      _ = 4 * (∑ b ∈ Finset.Icc 1 ⌊Q⌋₊, sigmaQ b) / Real.log (2 * Q) ^ 2 := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
      _ ≤ 20 * Q / Real.log (2 * Q) ^ 2 := by
          refine (div_le_div_iff_of_pos_right (by positivity)).mpr ?_
          linarith [sum_sigmaQ_le Q hQ]
  have hfold : 5 * Q ^ (1/2 : ℝ) / Real.log 2 ^ 2
      ≤ 640 / Real.log 2 ^ 2 * Q / Real.log (2 * Q) ^ 2 := by
    have hkey := rpow_half_mul_log_sq_le Q hQ
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hcl : 640 / Real.log 2 ^ 2 * Q * Real.log 2 ^ 2 = 640 * Q := by field_simp
    rw [hcl]
    linarith [hkey]
  have hcomb : (640 / Real.log 2 ^ 2 + 20) * Q / Real.log (2 * Q) ^ 2
      = 640 / Real.log 2 ^ 2 * Q / Real.log (2 * Q) ^ 2 + 20 * Q / Real.log (2 * Q) ^ 2 := by
    ring
  rw [hcomb]
  linarith [hsplit, hpart1, hpart2, hfold]

/-- The symmetric-double-sum split: for `F` symmetric,
`Σ_a Σ_b F = 2·Σ_a Σ_{b ≥ a} F − Σ_a F(a,a)`. The `b < a` half is the `a < b` half by
`Finset.sum_comm` plus symmetry, so only ONE half is ever estimated. -/
private lemma sym_double_sum_split {N : ℕ} (F : ℕ → ℕ → ℝ) (hsym : ∀ a b, F a b = F b a) :
    ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, F a b
      = 2 * (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if a ≤ b then F a b else 0)
        - ∑ a ∈ Finset.Icc 1 N, F a a := by
  classical
  have h1 : ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, F a b
      = (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if a ≤ b then F a b else 0)
        + ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, if b < a then F a b else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases le_or_gt a b with h | h
    · rw [if_pos h, if_neg (not_lt.mpr h)]; ring
    · rw [if_neg (not_le.mpr h), if_pos h]; ring
  have h2 : ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, (if b < a then F a b else 0)
      = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, (if a < b then F a b else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsym b a]
  have h3 : ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, (if a ≤ b then F a b else 0)
      = (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, (if a < b then F a b else 0))
        + ∑ a ∈ Finset.Icc 1 N, F a a := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hdi : ∑ b ∈ Finset.Icc 1 N, (if a = b then F a b else 0) = F a a := by
      rw [Finset.sum_ite_eq (Finset.Icc 1 N) a (fun b => F a b), if_pos ha]
    rw [← hdi, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy a b with h | h | h
    · rw [if_pos h.le, if_pos h, if_neg (ne_of_lt h)]; ring
    · subst h; rw [if_pos (le_refl a), if_neg (lt_irrefl a), if_pos rfl]; ring
    · rw [if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le),
        if_neg (fun hc => absurd hc (ne_of_gt h))]
      ring
  linarith [h1, h2, h3]

/-- **H7d (the B-kernel is `O(zQ/log²2Q)`).** The `a ≤ b` half, with `min = a` and
`log(a/a) = 0`, has summand `z·μ(b)(b/κ(b))·(μ(a)/κ(a))·(2 − log(b/a))`; the inner `a`-sum
is `2·[H6f at (b, b)] − [H6e at (b, b)] = −c₀·κ(b)/b + O(σ(b)/log²2b)`, and
**`(b/κ(b))·(c₀κ(b)/b) = c₀` — the κ-weight CANCELS EXACTLY**, leaving the BARE Möbius sum
`−c₀·Σ_{b ≤ Q} μ(b)`, which H6a at `A = 2` bounds. The `b < a` half is the same sum by
symmetry (`sym_double_sum_split`), and the diagonal `a = b` forces `a = b = 1` — one term
`2z`.

The must-FAIL control, `μ(a)μ(b) → μ(a)²μ(b)²` (the sign cancellation killed):
`B·(log 2Q)²/Q` (SIGNED) `= 9.1 / 3.3 / −35.5 / −125.5 / −321.3` at
`Q = 10, 30, 10², 300, 10³` — unbounded (negative because `2 − log(b/a) < 0` for
`b > e²a`). The frozen quantity is `0.41 / 3.49 / 0.28 / 2.30 / 0.27 / 0.51 / 0.74` at
`Q = 10 … 10⁴`.

**Two mutants were MEASURED and STRUCK, and are recorded here so they are not
re-proposed as controls.** (i) The exponent `2 → 3`: `1.50 / 2.03 / 7.32` at `10² … 10⁴` —
a bump that DECAYS, because the true size of `bKernel` is `≈ √Q` (the Möbius sum's
random-walk size, measured `|bKernel|/√Q = 0.10–1.14`), so `(log 2Q)³/√Q → 0` and the
exponent-3 row is TRUE. (ii) The bracket `2 − log → 2 + log`: `0.79 / 0.38 / 0.74` — it
PASSES, because the cancellation lives in `(b/κ(b))·(κ(b)/b)` and not in the bracket.

At the zero level `Q = 1`, `bKernel z 1 = 2z` (the single `a = b = 1` term), inside the
bound. -/
theorem abs_bKernel_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 1 ≤ z → ∀ Q : ℝ, 1 ≤ Q →
    |bKernel z Q| ≤ C * z * Q / Real.log (2 * Q) ^ 2 := by
  classical
  obtain ⟨C1, hC1, h6e⟩ := coprime_sum_moebius_div_kappa_log_eq 2 (by norm_num)
  obtain ⟨C2, hC2, h6f⟩ := coprime_sum_moebius_div_kappa_le 2 (by norm_num)
  obtain ⟨Ca, hCa, h6a⟩ := abs_sum_moebius_le_div_log_pow 2 (by norm_num)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : (1 : ℝ) ≤ c0 := one_le_c0
  have hc0pos : (0 : ℝ) < c0 := by linarith
  have hCWpos : (0 : ℝ) < 640 / Real.log 2 ^ 2 + 20 := by positivity
  refine ⟨2 * (c0 * Ca + (C1 + 2 * C2) * (640 / Real.log 2 ^ 2 + 20)) + 256, ?_,
    fun z hz Q hQ => ?_⟩
  · have h1 : 0 < c0 * Ca := mul_pos hc0pos hCa
    have h2 : 0 < (C1 + 2 * C2) * (640 / Real.log 2 ^ 2 + 20) :=
      mul_pos (by linarith) hCWpos
    linarith
  have hz0 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hL : (0 : ℝ) < Real.log (2 * Q) := Real.log_pos (by linarith)
  have hL2 : (0 : ℝ) < Real.log (2 * Q) ^ 2 := by positivity
  have hN1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
  set FF : ℕ → ℕ → ℝ := fun a b =>
    if Nat.Coprime a b then
      (moebius a : ℝ) * (moebius b : ℝ) * (((a * b : ℕ) : ℝ) / kappa (a * b))
        * ((z : ℝ) / ((min a b : ℕ) : ℝ))
        * ((Real.log ((a : ℝ) / ((min a b : ℕ) : ℝ)) - 1)
            * (Real.log ((b : ℝ) / ((min a b : ℕ) : ℝ)) - 1) + 1)
    else 0 with hFFdef
  have hsym : ∀ a b, FF a b = FF b a := by
    intro a b
    rw [hFFdef]
    dsimp only
    by_cases h : Nat.Coprime a b
    · rw [if_pos h, if_pos (Nat.coprime_comm.mp h), Nat.mul_comm b a, min_comm b a]
      ring
    · rw [if_neg h, if_neg (fun hc => h (Nat.coprime_comm.mp hc))]
  have hbk : bKernel z Q = ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ b ∈ Finset.Icc 1 ⌊Q⌋₊, FF a b := by
    rw [bKernel, hFFdef]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only
    rw [Finset.sum_filter]
  -- the diagonal: `Coprime a a` forces `a = 1`, and the single term is `2z`
  have hFF11 : FF 1 1 = 2 * (z : ℝ) := by
    rw [hFFdef]
    dsimp only
    rw [if_pos (Nat.coprime_one_left 1)]
    have hk1 : kappa 1 = 1 := by rw [kappa, Nat.primeFactors_one, Finset.prod_empty]; norm_num
    norm_num [hk1]
    ring
  have hDiag : ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, FF a a = 2 * (z : ℝ) := by
    rw [Finset.sum_eq_single 1 ?_ ?_, hFF11]
    · intro b _ hb1
      rw [hFFdef]
      dsimp only
      refine if_neg ?_
      intro hcop
      have hg : Nat.gcd b b = 1 := hcop
      rw [Nat.gcd_self] at hg
      exact hb1 hg
    · intro h
      exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, hN1⟩) h
  -- the `a ≤ b` half, summed with `a` inside
  have hhalf : ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ b ∈ Finset.Icc 1 ⌊Q⌋₊, (if a ≤ b then FF a b else 0)
      = ∑ b ∈ Finset.Icc 1 ⌊Q⌋₊,
          ((z : ℝ) * (moebius b : ℝ) * ((b : ℝ) / kappa b)
            * (2 * (∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                    (moebius n : ℝ) / kappa n)
              - ∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                    (moebius n : ℝ) / kappa n * Real.log ((b : ℝ) / n))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [Finset.mem_Icc] at hb
    have hb1 : 1 ≤ b := hb.1
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
    have hkb : (0 : ℝ) < kappa b := kappa_pos b hb1
    have hset : (Finset.Icc 1 ⌊Q⌋₊).filter (fun a => a ≤ b) = Finset.Icc 1 b := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hb.2⟩, h2⟩
    rw [← Finset.sum_filter, hset, hFFdef]
    dsimp only
    rw [← Finset.sum_filter]
    have hbody : ∀ a ∈ (Finset.Icc 1 b).filter (fun a => Nat.Coprime a b),
        (moebius a : ℝ) * (moebius b : ℝ) * (((a * b : ℕ) : ℝ) / kappa (a * b))
          * ((z : ℝ) / ((min a b : ℕ) : ℝ))
          * ((Real.log ((a : ℝ) / ((min a b : ℕ) : ℝ)) - 1)
              * (Real.log ((b : ℝ) / ((min a b : ℕ) : ℝ)) - 1) + 1)
        = (z : ℝ) * (moebius b : ℝ) * ((b : ℝ) / kappa b)
            * (2 * ((moebius a : ℝ) / kappa a)
              - (moebius a : ℝ) / kappa a * Real.log ((b : ℝ) / a)) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha
      obtain ⟨⟨ha1, hab⟩, hcop⟩ := ha
      have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
      have hka : (0 : ℝ) < kappa a := kappa_pos a ha1
      have hka' : kappa a ≠ 0 := ne_of_gt hka
      have hkb' : kappa b ≠ 0 := ne_of_gt hkb
      have ha0' : (a : ℝ) ≠ 0 := ne_of_gt ha0
      rw [min_eq_left hab, kappa_mul_of_coprime hcop, Nat.cast_mul,
        div_self ha0', Real.log_one]
      field_simp
      ring
    rw [Finset.sum_congr rfl hbody, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- the per-`b` bound of the bracket
  have hbbd : ∀ b ∈ Finset.Icc 1 ⌊Q⌋₊,
      |(moebius b : ℝ) * ((b : ℝ) / kappa b)
        * (2 * (∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                (moebius n : ℝ) / kappa n)
          - ((∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                (moebius n : ℝ) / kappa n * Real.log ((b : ℝ) / n)) - c0 * kappa b / b))|
      ≤ (C1 + 2 * C2) * sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2 := by
    intro b hb
    simp only [Finset.mem_Icc] at hb
    have hb1 : 1 ≤ b := hb.1
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
    have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    have hkb : (0 : ℝ) < kappa b := kappa_pos b hb1
    have hLb : (0 : ℝ) < Real.log (2 * (b : ℝ)) := Real.log_pos (by linarith)
    have hLb2 : (0 : ℝ) < Real.log (2 * (b : ℝ)) ^ 2 := by positivity
    have hsig : (0 : ℝ) ≤ sigmaQ b := sigmaQ_nonneg b
    have hRHS : (0 : ℝ) ≤ (C1 + 2 * C2) * sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2 := by
      have : (0 : ℝ) ≤ (C1 + 2 * C2) * sigmaQ b := by nlinarith
      positivity
    by_cases hsq : Squarefree b
    · have hfl : ⌊(b : ℝ)⌋₊ = b := Nat.floor_natCast b
      have e1 := h6e b hsq (b : ℝ) hbR
      have e2 := h6f b hsq (b : ℝ) hbR
      rw [hfl, log_rpow_two_eq] at e1 e2
      have hmu : |(moebius b : ℝ)| ≤ 1 := abs_moebius_cast_le_one b
      have hdk : |(moebius b : ℝ) * ((b : ℝ) / kappa b)| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b : ℝ) / kappa b)]
        calc |(moebius b : ℝ)| * ((b : ℝ) / kappa b) ≤ 1 * 1 :=
              mul_le_mul hmu (div_kappa_le_one b hb1) (by positivity) (by norm_num)
          _ = 1 := by norm_num
      rw [abs_mul]
      have hbr : |2 * (∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                (moebius n : ℝ) / kappa n)
          - ((∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                (moebius n : ℝ) / kappa n * Real.log ((b : ℝ) / n)) - c0 * kappa b / b)|
          ≤ (C1 + 2 * C2) * sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2 := by
        refine le_trans (abs_sub_le_add' _ _) ?_
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
        have : 2 * |∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
              (moebius n : ℝ) / kappa n|
            ≤ 2 * (C2 * sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2) := by linarith
        have hsum : C1 * sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2
            + 2 * (C2 * sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2)
            = (C1 + 2 * C2) * sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2 := by ring
        linarith
      calc |(moebius b : ℝ) * ((b : ℝ) / kappa b)|
            * |2 * (∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                    (moebius n : ℝ) / kappa n)
              - ((∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                    (moebius n : ℝ) / kappa n * Real.log ((b : ℝ) / n)) - c0 * kappa b / b)|
          ≤ 1 * ((C1 + 2 * C2) * sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2) :=
            mul_le_mul hdk hbr (abs_nonneg _) (by norm_num)
        _ = (C1 + 2 * C2) * sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2 := by ring
    · have hmu : (moebius b : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; norm_num
      rw [hmu]
      simpa using hRHS
  -- the identity that performs the κ-cancellation
  have hcancel : ∀ b ∈ Finset.Icc 1 ⌊Q⌋₊,
      (z : ℝ) * (moebius b : ℝ) * ((b : ℝ) / kappa b)
        * (2 * (∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                (moebius n : ℝ) / kappa n)
          - ∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                (moebius n : ℝ) / kappa n * Real.log ((b : ℝ) / n))
      = -((z : ℝ) * c0) * (moebius b : ℝ)
        + (z : ℝ) * ((moebius b : ℝ) * ((b : ℝ) / kappa b)
          * (2 * (∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                  (moebius n : ℝ) / kappa n)
            - ((∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                  (moebius n : ℝ) / kappa n * Real.log ((b : ℝ) / n)) - c0 * kappa b / b))) := by
    intro b hb
    simp only [Finset.mem_Icc] at hb
    have hb1 : 1 ≤ b := hb.1
    have hb0 : (b : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
      exact ne_of_gt this
    have hkb : kappa b ≠ 0 := ne_of_gt (kappa_pos b hb1)
    field_simp
    ring
  rw [hbk, sym_double_sum_split FF hsym, hDiag, hhalf,
    Finset.sum_congr rfl hcancel, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- assemble
  have hmoeb : |∑ b ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius b : ℝ)| ≤ Ca * Q / Real.log (2 * Q) ^ 2 := by
    have := h6a Q hQ
    rwa [log_rpow_two_eq] at this
  have herr : |∑ b ∈ Finset.Icc 1 ⌊Q⌋₊, ((moebius b : ℝ) * ((b : ℝ) / kappa b)
        * (2 * (∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                (moebius n : ℝ) / kappa n)
          - ((∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                (moebius n : ℝ) / kappa n * Real.log ((b : ℝ) / n)) - c0 * kappa b / b)))|
      ≤ (C1 + 2 * C2) * ((640 / Real.log 2 ^ 2 + 20) * Q / Real.log (2 * Q) ^ 2) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum hbbd) ?_
    have hrw : ∀ b : ℕ, (C1 + 2 * C2) * sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2
        = (C1 + 2 * C2) * (sigmaQ b / Real.log (2 * (b : ℝ)) ^ 2) := fun b => by ring
    rw [Finset.sum_congr rfl (fun b _ => hrw b), ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_sigmaQ_div_log_sq_le Q hQ) (by linarith)
  have hgoal : |2 * (-((z : ℝ) * c0) * (∑ b ∈ Finset.Icc 1 ⌊Q⌋₊, (moebius b : ℝ))
        + (z : ℝ) * ∑ b ∈ Finset.Icc 1 ⌊Q⌋₊, ((moebius b : ℝ) * ((b : ℝ) / kappa b)
            * (2 * (∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                    (moebius n : ℝ) / kappa n)
              - ((∑ n ∈ (Finset.Icc 1 b).filter (fun n => Nat.Coprime n b),
                    (moebius n : ℝ) / kappa n * Real.log ((b : ℝ) / n))
                - c0 * kappa b / b)))) - 2 * (z : ℝ)|
      ≤ 2 * ((z : ℝ) * c0 * (Ca * Q / Real.log (2 * Q) ^ 2)
          + (z : ℝ) * ((C1 + 2 * C2) * ((640 / Real.log 2 ^ 2 + 20) * Q
              / Real.log (2 * Q) ^ 2))) + 2 * (z : ℝ) := by
    refine le_trans (abs_sub_le_add' _ _) ?_
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)), abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)), abs_of_nonneg hz0.le]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (le_refl _)
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul, abs_neg, abs_mul, abs_of_nonneg hz0.le,
      abs_of_nonneg hc0pos.le]
    exact add_le_add (mul_le_mul_of_nonneg_left hmoeb (by positivity))
      (mul_le_mul_of_nonneg_left herr hz0.le)
  refine le_trans hgoal ?_
  have hbig : 2 * Real.log (2 * Q) ^ 2 ≤ 256 * Q := by
    have h1 := log_sq_le_rpow_quarter Q hQ
    have h2 : Q ^ (1/4 : ℝ) ≤ Q := by
      calc Q ^ (1/4 : ℝ) ≤ Q ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
        _ = Q := Real.rpow_one Q
    linarith
  rw [← sub_nonneg]
  have hexp : (2 * (c0 * Ca + (C1 + 2 * C2) * (640 / Real.log 2 ^ 2 + 20)) + 256)
        * (z : ℝ) * Q / Real.log (2 * Q) ^ 2
      - (2 * ((z : ℝ) * c0 * (Ca * Q / Real.log (2 * Q) ^ 2)
          + (z : ℝ) * ((C1 + 2 * C2) * ((640 / Real.log 2 ^ 2 + 20) * Q
              / Real.log (2 * Q) ^ 2))) + 2 * (z : ℝ))
      = (z : ℝ) * (256 * Q - 2 * Real.log (2 * Q) ^ 2) / Real.log (2 * Q) ^ 2 := by
    field_simp
    ring
  rw [hexp]
  have : (0 : ℝ) ≤ (z : ℝ) * (256 * Q - 2 * Real.log (2 * Q) ^ 2) := by nlinarith
  positivity

/-- **H7d' (the `g`-sum of the B-kernel).** `Σ_{g ≤ u/z} |bKernel z (u/(gz))| ≤ C·u`:
H7d at `Q = u/(gz) ≥ 1` gives `C·z·(u/(gz))/log²(2u/(gz)) = C·u/(g·log²(2X/g))` with
`X = u/z`, and **H0c** (`sum_inv_mul_log_sq_le` at `Q = X`) sums it to `C·C₀·u`. When
`u < z` the `g`-range is empty. -/
theorem sum_abs_bKernel_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 1 ≤ z → ∀ u : ℝ, 1 ≤ u →
    ∑ g ∈ Finset.Icc 1 ⌊u / z⌋₊, |bKernel z (u / (g * z))| ≤ C * u := by
  classical
  obtain ⟨Cb, hCb, hd⟩ := abs_bKernel_le
  obtain ⟨C0, hC0, h0c⟩ := sum_inv_mul_log_sq_le
  refine ⟨Cb * C0, mul_pos hCb hC0, fun z hz u hu => ?_⟩
  have hz0 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hu0 : (0 : ℝ) < u := by linarith
  rcases lt_or_ge (u / z) 1 with hlt | hge
  · have hfl : ⌊u / (z : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr hlt
    have hemp : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
      rw [Finset.Icc_eq_empty]
      omega
    rw [hfl, hemp, Finset.sum_empty]
    have : (0 : ℝ) < Cb * C0 * u := mul_pos (mul_pos hCb hC0) hu0
    linarith
  · have hX1 : (1 : ℝ) ≤ u / z := hge
    have hNX : ((⌊u / (z : ℝ)⌋₊ : ℕ) : ℝ) ≤ u / z := Nat.floor_le (by linarith)
    have hterm : ∀ g ∈ Finset.Icc 1 ⌊u / (z : ℝ)⌋₊,
        |bKernel z (u / (g * z))|
          ≤ Cb * u * (1 / ((g : ℝ) * Real.log (2 * (u / z) / g) ^ 2)) := by
      intro g hg
      simp only [Finset.mem_Icc] at hg
      have hg1 : 1 ≤ g := hg.1
      have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg1
      have hgX : (g : ℝ) ≤ u / z := le_trans (by exact_mod_cast hg.2) hNX
      have hQ1 : (1 : ℝ) ≤ u / ((g : ℝ) * z) := by
        rw [le_div_iff₀ (by positivity)]
        rw [le_div_iff₀ hz0] at hgX
        linarith
      have hbd := hd z hz (u / ((g : ℝ) * z)) hQ1
      have heq : Cb * (z : ℝ) * (u / ((g : ℝ) * z)) / Real.log (2 * (u / ((g : ℝ) * z))) ^ 2
          = Cb * u * (1 / ((g : ℝ) * Real.log (2 * (u / z) / g) ^ 2)) := by
        have h2 : (2 : ℝ) * (u / ((g : ℝ) * z)) = 2 * (u / z) / g := by
          field_simp
        rw [h2]
        field_simp
      rwa [heq] at hbd
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsum := h0c (u / z) hX1
    calc Cb * u * ∑ g ∈ Finset.Icc 1 ⌊u / (z : ℝ)⌋₊,
          1 / ((g : ℝ) * Real.log (2 * (u / z) / g) ^ 2)
        ≤ Cb * u * C0 := by
          refine mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Cb * C0 * u := by ring

/-! ## V. ΣD -/

theorem sum_rpow_neg_half_sigmaQ_one_add_log_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q →
    ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, (a : ℝ) ^ (-(1/2 : ℝ)) * sigmaQ a * (1 + Real.log (Q / a))
      ≤ C * Q ^ (1/2 : ℝ) := by
  sorry

theorem sum_sum_errUpper_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 1 ≤ z → ∀ g : ℕ, 1 ≤ g → ∀ u : ℝ,
    ((g * z : ℕ) : ℝ) ≤ u →
    ∑ a ∈ Finset.Icc 1 ⌊u / (g * z)⌋₊, ∑ b ∈ Finset.Icc 1 ⌊u / (g * z)⌋₊,
        (u / (g * a * b)) ^ (1/2 : ℝ) * sigmaQ (a * b)
          * (1 + |Real.log (u / (g * b * z))|) * (1 + |Real.log (u / (g * a * z))|)
      ≤ C * (u / g) ^ (1/2 : ℝ) * (u / (g * z)) := by
  sorry

theorem sum_sum_errLower_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 1 ≤ z → ∀ Q : ℝ, 1 ≤ Q →
    ∑ a ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ b ∈ Finset.Icc 1 ⌊Q⌋₊,
        ((z : ℝ) / ((min a b : ℕ) : ℝ)) ^ (1/2 : ℝ) * sigmaQ (a * b)
          * (1 + |Real.log ((a : ℝ) / ((min a b : ℕ) : ℝ))|)
          * (1 + |Real.log ((b : ℝ) / ((min a b : ℕ) : ℝ))|)
      ≤ C * (z : ℝ) ^ (1/2 : ℝ) * Q ^ (3/2 : ℝ) := by
  sorry

theorem sum_rpow_neg_three_half_le (X : ℕ) :
    ∑ g ∈ Finset.Icc 1 X, (g : ℝ) ^ (-(3/2 : ℝ)) ≤ 3 := by
  sorry

/-! ## VI. THE FROZEN TOP -/

theorem sum_tailT_sq_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z → ∀ u : ℝ, 1 ≤ u → u ≤ (z : ℝ) ^ 2 →
    ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, tailT z n ^ 2 ≤ C * u * Real.log z := by
  sorry

theorem grahamW_sum_le_full : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z → ∀ x : ℝ, (z : ℝ) ≤ x →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, grahamW z n ≤ C * x / Real.log z := by
  sorry

theorem sum_sq_sum_bvWeight_le_full : ∃ C : ℝ, 0 < C ∧ ∀ z₁ z₂ : ℕ, 2 ≤ z₁ → z₁ < z₂ →
    ∀ x : ℝ, (z₂ : ℝ) ≤ x →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2
      ≤ 2 * (Real.log z₁ + Real.log z₂) / Real.log ((z₂ : ℝ) / z₁) ^ 2 * (C * x) := by
  sorry

theorem sum_sq_sum_bvWeight_le_low : ∃ C : ℝ, 0 < C ∧ ∀ z₁ z₂ : ℕ, 2 ≤ z₁ → z₁ < z₂ →
    ∀ x : ℝ, 2 ≤ x → x ≤ z₂ →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2
      ≤ C * Real.log z₂ * (Real.log z₂ + x) / Real.log ((z₂ : ℝ) / z₁) ^ 2 := by
  sorry

end Salt.SW
