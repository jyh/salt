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

theorem abs_aKernel_sub_c0_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 1 ≤ Q →
    |aKernel Q - c0| ≤ C / Real.log (2 * Q) ^ 2 := by
  sorry

theorem sum_inv_mul_abs_aKernel_le : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    ∑ g ∈ Finset.Icc 1 ⌊X⌋₊, 1 / (g : ℝ) * |aKernel (X / g)| ≤ C * (1 + Real.log X) := by
  sorry

/-! ## IV. ΣB + ΣC -/

theorem abs_bKernel_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 1 ≤ z → ∀ Q : ℝ, 1 ≤ Q →
    |bKernel z Q| ≤ C * z * Q / Real.log (2 * Q) ^ 2 := by
  sorry

theorem sum_abs_bKernel_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 1 ≤ z → ∀ u : ℝ, 1 ≤ u →
    ∑ g ∈ Finset.Icc 1 ⌊u / z⌋₊, |bKernel z (u / (g * z))| ≤ C * u := by
  sorry

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
