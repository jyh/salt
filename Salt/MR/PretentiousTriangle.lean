/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Dist
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Norm

/-!
# MR wave-2 rung R1.1 — the pretentious triangle inequality (`PretentiousTriangle`)

The triangle inequality for the Granville–Soundararajan / Tao pretentious distance
`pretDist f g x = √(pretDistSq f g x)`, at full 1-bounded generality (each `‖·‖ ≤ 1`).

## Contents
* `pretentious_pointwise_triangle` — the per-prime metric fact
  `√(1 − Re(a·conj c)) ≤ √(1 − Re(a·conj b)) + √(1 − Re(b·conj c))` for 1-bounded `a b c : ℂ`.
* `pretDist` — `√(pretDistSq f g x)` and `pretDistSq_nonneg`.
* `pretDist_triangle` — `𝔻(f, h; x) ≤ 𝔻(f, g; x) + 𝔻(g, h; x)` (pointwise + ℓ² Minkowski).
* `dist_mul_half` — the squared-distance halving `(1/2)·𝔻(f,h)² − 𝔻(f,g)² ≤ 𝔻(g,h)²`
  (the reverse-triangle floor the R3.1 recentering consumes; the factor `1/2` is the "half").

## The pointwise lemma (reconstructed — NOT staged; see the module NOTES in the report)

The subtle `|b| < 1` case is dissolved by a 5-dimensional Hilbert embedding giving each of
`a, b, c` its OWN private "defect" coordinate `s = √(1 − |·|²)`:
`φ(a) = (a.re, a.im, sₐ, 0, 0)`, `φ(b) = (b.re, b.im, 0, s_b, 0)`, `φ(c) = (c.re, c.im, 0, 0, s_c)`.
Then `‖φ(a) − φ(c)‖² = 2(1 − Re(a·conj c))` exactly, so the pointwise triangle IS the Euclidean
triangle in `ℝ⁵` — its Cauchy–Schwarz core is the 10-term Gram sum-of-squares certified in
`sqrt_dist_triangle_real`.  (The prior executor's `ℝ³` sphere-lift shared a single defect
coordinate and so underestimated the `|b| < 1` case; the private-coordinate fix closes it.)
-/

namespace Salt.MR

open scoped BigOperators

/-- `‖a‖ ≤ 1` in coordinate form: `a.re² + a.im² ≤ 1`. -/
private lemma sq_re_add_sq_im_le {a : ℂ} (ha : ‖a‖ ≤ 1) : a.re ^ 2 + a.im ^ 2 ≤ 1 := by
  have h : a.re ^ 2 + a.im ^ 2 = ‖a‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h]; nlinarith [norm_nonneg a, ha]

/-- The sqrt-reduction upgrade: `(w − u − v)² ≤ 4uv` (with `u, v ≥ 0`) gives the sqrt
triangle inequality `√w ≤ √u + √v`.  Parameters kept opaque so `nlinarith` treats them as
atoms (avoids unfolding `Real.sqrt` under `set`). -/
private lemma sqrt_tri_abstract {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hQ : (w - u - v) ^ 2 ≤ 4 * u * v) : Real.sqrt w ≤ Real.sqrt u + Real.sqrt v := by
  have hkey : w ≤ (Real.sqrt u + Real.sqrt v) ^ 2 := by
    have hsu : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
    have hsv : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
    have huv : 0 ≤ u * v := mul_nonneg hu hv
    rcases le_or_gt (w - u - v) 0 with hle | hgt
    · nlinarith [Real.sqrt_nonneg u, Real.sqrt_nonneg v,
        mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)]
    · have h2 : Real.sqrt (4 * u * v) = 2 * Real.sqrt (u * v) := by
        rw [show (4 : ℝ) * u * v = 2 ^ 2 * (u * v) by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]
      have hle2 : w - u - v ≤ 2 * Real.sqrt (u * v) := by
        rw [← h2]
        calc w - u - v ≤ |w - u - v| := le_abs_self _
          _ = Real.sqrt ((w - u - v) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt (4 * u * v) := Real.sqrt_le_sqrt hQ
      have hmul : Real.sqrt u * Real.sqrt v = Real.sqrt (u * v) := (Real.sqrt_mul hu v).symm
      nlinarith [hmul, hsu, hsv, hle2]
  have hfin := Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_sq (by positivity)] at hfin

/-- The pure-real core of the pointwise triangle: the 5-dimensional Gram sum-of-squares.
With `u, v, w` the three `1 − ⟨·,·⟩` inner-product deficits of the coordinate pairs (each
`·₁² + ·₂² ≤ 1`), `(w − u − v)² ≤ 4uv` (Cauchy–Schwarz of the two edge vectors of the ℝ⁵
triangle), which `sqrt_tri_abstract` upgrades to the sqrt triangle inequality.  The defect
coordinates `sa, sb, sc = √(1 − |·|²)` are introduced opaquely (only their squares matter). -/
private lemma sqrt_dist_triangle_real (a1 a2 b1 b2 c1 c2 : ℝ)
    (ha : a1 ^ 2 + a2 ^ 2 ≤ 1) (hb : b1 ^ 2 + b2 ^ 2 ≤ 1) (hc : c1 ^ 2 + c2 ^ 2 ≤ 1) :
    Real.sqrt (1 - (a1 * c1 + a2 * c2))
      ≤ Real.sqrt (1 - (a1 * b1 + a2 * b2)) + Real.sqrt (1 - (b1 * c1 + b2 * c2)) := by
  obtain ⟨sa, hsa⟩ : ∃ s : ℝ, s ^ 2 = 1 - (a1 ^ 2 + a2 ^ 2) := ⟨_, Real.sq_sqrt (by linarith)⟩
  obtain ⟨sb, hsb⟩ : ∃ s : ℝ, s ^ 2 = 1 - (b1 ^ 2 + b2 ^ 2) := ⟨_, Real.sq_sqrt (by linarith)⟩
  obtain ⟨sc, hsc⟩ : ∃ s : ℝ, s ^ 2 = 1 - (c1 ^ 2 + c2 ^ 2) := ⟨_, Real.sq_sqrt (by linarith)⟩
  have hu : (0 : ℝ) ≤ 1 - (a1 * b1 + a2 * b2) := by
    nlinarith [sq_nonneg (a1 - b1), sq_nonneg (a2 - b2)]
  have hv : (0 : ℝ) ≤ 1 - (b1 * c1 + b2 * c2) := by
    nlinarith [sq_nonneg (b1 - c1), sq_nonneg (b2 - c2)]
  refine sqrt_tri_abstract hu hv ?_
  nlinarith [sq_nonneg ((a1 - b1) * (b2 - c2) - (a2 - b2) * (b1 - c1)),
    mul_nonneg (sq_nonneg sa) (sq_nonneg (b1 - c1)),
    mul_nonneg (sq_nonneg sa) (sq_nonneg (b2 - c2)),
    mul_nonneg (sq_nonneg sb) (sq_nonneg (a1 - c1)),
    mul_nonneg (sq_nonneg sb) (sq_nonneg (a2 - c2)),
    mul_nonneg (sq_nonneg sc) (sq_nonneg (a1 - b1)),
    mul_nonneg (sq_nonneg sc) (sq_nonneg (a2 - b2)),
    mul_nonneg (sq_nonneg sa) (sq_nonneg sb), mul_nonneg (sq_nonneg sa) (sq_nonneg sc),
    mul_nonneg (sq_nonneg sb) (sq_nonneg sc), hsa, hsb, hsc]

/-- **The pointwise pretentious triangle inequality.**  For 1-bounded `a b c : ℂ`,
`√(1 − Re(a·conj c)) ≤ √(1 − Re(a·conj b)) + √(1 − Re(b·conj c))`.  The per-prime metric
fact driving `pretDist_triangle`; the interesting content is the sub-unit case, dissolved by
the ℝ⁵ private-defect embedding (see the file header). -/
theorem pretentious_pointwise_triangle {a b c : ℂ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    Real.sqrt (1 - (a * (starRingEnd ℂ) c).re)
      ≤ Real.sqrt (1 - (a * (starRingEnd ℂ) b).re)
        + Real.sqrt (1 - (b * (starRingEnd ℂ) c).re) := by
  have e : ∀ z w : ℂ, (z * (starRingEnd ℂ) w).re = z.re * w.re + z.im * w.im := by
    intro z w; simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [e a c, e a b, e b c]
  exact sqrt_dist_triangle_real a.re a.im b.re b.im c.re c.im
    (sq_re_add_sq_im_le ha) (sq_re_add_sq_im_le hb) (sq_re_add_sq_im_le hc)

/-- Discrete ℓ² Minkowski (from Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq`):
`√(∑(α+β)²) ≤ √(∑α²) + √(∑β²)`. -/
private lemma sqrt_sum_add_sq_le {ι : Type*} (S : Finset ι) (α β : ι → ℝ) :
    Real.sqrt (∑ i ∈ S, (α i + β i) ^ 2)
      ≤ Real.sqrt (∑ i ∈ S, (α i) ^ 2) + Real.sqrt (∑ i ∈ S, (β i) ^ 2) := by
  set P := ∑ i ∈ S, (α i) ^ 2 with hP
  set Q := ∑ i ∈ S, (β i) ^ 2 with hQ
  have hPnn : 0 ≤ P := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hQnn : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcs : (∑ i ∈ S, α i * β i) ^ 2 ≤ P * Q := Finset.sum_mul_sq_le_sq_mul_sq S α β
  have hcs2 : ∑ i ∈ S, α i * β i ≤ Real.sqrt P * Real.sqrt Q := by
    calc ∑ i ∈ S, α i * β i ≤ Real.sqrt ((∑ i ∈ S, α i * β i) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
      _ ≤ Real.sqrt (P * Q) := Real.sqrt_le_sqrt hcs
      _ = Real.sqrt P * Real.sqrt Q := Real.sqrt_mul hPnn Q
  have hexp : ∑ i ∈ S, (α i + β i) ^ 2 = P + 2 * (∑ i ∈ S, α i * β i) + Q := by
    rw [hP, hQ, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hle : ∑ i ∈ S, (α i + β i) ^ 2 ≤ (Real.sqrt P + Real.sqrt Q) ^ 2 := by
    rw [hexp]; nlinarith [hcs2, Real.sq_sqrt hPnn, Real.sq_sqrt hQnn]
  calc Real.sqrt (∑ i ∈ S, (α i + β i) ^ 2)
        ≤ Real.sqrt ((Real.sqrt P + Real.sqrt Q) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt P + Real.sqrt Q := Real.sqrt_sq (by positivity)

/-- Dividing the pointwise triangle through by `√p`:
if `√A ≤ √B + √C` then `√(A/p) ≤ √(B/p) + √(C/p)` for `p > 0`. -/
private lemma sqrt_div_triangle {A B C p : ℝ} (hp : 0 < p)
    (h : Real.sqrt A ≤ Real.sqrt B + Real.sqrt C) :
    Real.sqrt (A / p) ≤ Real.sqrt (B / p) + Real.sqrt (C / p) := by
  have hpinv : (0 : ℝ) ≤ p⁻¹ := by positivity
  rw [div_eq_mul_inv A p, div_eq_mul_inv B p, div_eq_mul_inv C p,
      Real.sqrt_mul' A hpinv, Real.sqrt_mul' B hpinv, Real.sqrt_mul' C hpinv]
  nlinarith [mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg p⁻¹), Real.sqrt_nonneg p⁻¹]

/-! ## The pretentious distance and its triangle inequality -/

/-- **The pretentious distance** `𝔻(f, g; x) = √(pretDistSq f g x)`. -/
noncomputable def pretDist (f g : ℕ → ℂ) (x : ℝ) : ℝ := Real.sqrt (pretDistSq f g x)

/-- Each summand `1 − Re(a·conj b)` of `pretDistSq` is nonnegative for 1-bounded `a b`. -/
theorem pretDistSq_term_nonneg {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    0 ≤ 1 - (a * (starRingEnd ℂ) b).re := by
  have e : (a * (starRingEnd ℂ) b).re = a.re * b.re + a.im * b.im := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [e]
  nlinarith [sq_re_add_sq_im_le ha, sq_re_add_sq_im_le hb,
    sq_nonneg (a.re - b.re), sq_nonneg (a.im - b.im)]

/-- `pretDistSq` is nonnegative for 1-bounded arguments (a sum of nonnegative terms). -/
theorem pretDistSq_nonneg (f g : ℕ → ℂ) (x : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) : 0 ≤ pretDistSq f g x := by
  unfold pretDistSq
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
  exact div_nonneg (pretDistSq_term_nonneg (hf p) (hg p)) hppos.le

/-- **R1.1 — the pretentious triangle inequality.**  For 1-bounded `f g h : ℕ → ℂ`,
`𝔻(f, h; x) ≤ 𝔻(f, g; x) + 𝔻(g, h; x)`.  Proof: the per-prime `pretentious_pointwise_triangle`
divided through by `√p` (`sqrt_div_triangle`), then ℓ² Minkowski over the prime set
(`sqrt_sum_add_sq_le`, i.e. Cauchy–Schwarz). -/
theorem pretDist_triangle {f g h : ℕ → ℂ} (x : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (hh : ∀ n, ‖h n‖ ≤ 1) :
    pretDist f h x ≤ pretDist f g x + pretDist g h x := by
  unfold pretDist pretDistSq
  set S := (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime with hS
  have hppos : ∀ p ∈ S, (0 : ℝ) < p := by
    intro p hp; rw [hS, Finset.mem_filter] at hp; exact_mod_cast hp.2.pos
  set α := fun p : ℕ => Real.sqrt ((1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ)) with hα
  set β := fun p : ℕ => Real.sqrt ((1 - (g p * (starRingEnd ℂ) (h p)).re) / (p : ℝ)) with hβ
  have hαsq : ∀ p ∈ S, (α p) ^ 2 = (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ) :=
    fun p hp => Real.sq_sqrt (div_nonneg (pretDistSq_term_nonneg (hf p) (hg p)) (hppos p hp).le)
  have hβsq : ∀ p ∈ S, (β p) ^ 2 = (1 - (g p * (starRingEnd ℂ) (h p)).re) / (p : ℝ) :=
    fun p hp => Real.sq_sqrt (div_nonneg (pretDistSq_term_nonneg (hg p) (hh p)) (hppos p hp).le)
  have hpoint : ∀ p ∈ S,
      (1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ) ≤ (α p + β p) ^ 2 := by
    intro p hp
    have hsqrt_le : Real.sqrt ((1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ)) ≤ α p + β p :=
      sqrt_div_triangle (hppos p hp) (pretentious_pointwise_triangle (hf p) (hg p) (hh p))
    have h0 : 0 ≤ Real.sqrt ((1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ)) :=
      Real.sqrt_nonneg _
    have hsq : Real.sqrt ((1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ)) ^ 2
        = (1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ) :=
      Real.sq_sqrt (div_nonneg (pretDistSq_term_nonneg (hf p) (hh p)) (hppos p hp).le)
    calc (1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ)
        = Real.sqrt ((1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ)) ^ 2 := hsq.symm
      _ ≤ (α p + β p) ^ 2 := by
          apply sq_le_sq' _ hsqrt_le; linarith [le_trans h0 hsqrt_le]
  calc Real.sqrt (∑ p ∈ S, (1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ))
      ≤ Real.sqrt (∑ p ∈ S, (α p + β p) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum hpoint)
    _ ≤ Real.sqrt (∑ p ∈ S, (α p) ^ 2) + Real.sqrt (∑ p ∈ S, (β p) ^ 2) :=
        sqrt_sum_add_sq_le S α β
    _ = Real.sqrt (∑ p ∈ S, (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ))
          + Real.sqrt (∑ p ∈ S, (1 - (g p * (starRingEnd ℂ) (h p)).re) / (p : ℝ)) := by
        rw [Finset.sum_congr rfl hαsq, Finset.sum_congr rfl hβsq]

/-- **R1.1 — the squared-distance halving `dist_mul_half`.**  For 1-bounded `f g h`,
`(1/2)·𝔻(f,h;x)² − 𝔻(f,g;x)² ≤ 𝔻(g,h;x)²` — the reverse-triangle floor with the factor `1/2`
(from `(A−B)² ≥ ½A² − B²`) that the R3.1 recentering consumes: instantiated with `g` the
product `f·g_J` it yields `𝔻(f·g_J, ·)² ≥ ½·𝔻(f, ·)² − 𝔻(f, f·g_J)²`, halving a floor on
`𝔻(f, ·)²` into one on `𝔻(f·g_J, ·)²`.  Derived purely from `pretDist_triangle`. -/
theorem dist_mul_half {f g h : ℕ → ℂ} (x : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (hh : ∀ n, ‖h n‖ ≤ 1) :
    (1 / 2) * pretDistSq f h x - pretDistSq f g x ≤ pretDistSq g h x := by
  have htri := pretDist_triangle x hf hg hh
  have e_fh : pretDist f h x ^ 2 = pretDistSq f h x := Real.sq_sqrt (pretDistSq_nonneg f h x hf hh)
  have e_fg : pretDist f g x ^ 2 = pretDistSq f g x := Real.sq_sqrt (pretDistSq_nonneg f g x hf hg)
  have e_gh : pretDist g h x ^ 2 = pretDistSq g h x := Real.sq_sqrt (pretDistSq_nonneg g h x hg hh)
  have h0_fh : 0 ≤ pretDist f h x := Real.sqrt_nonneg _
  have h0_fg : 0 ≤ pretDist f g x := Real.sqrt_nonneg _
  have h0_gh : 0 ≤ pretDist g h x := Real.sqrt_nonneg _
  have hBDA : (0 : ℝ) ≤ pretDist f g x + pretDist g h x - pretDist f h x := by linarith [htri]
  rw [← e_fh, ← e_fg, ← e_gh]
  nlinarith [mul_nonneg h0_gh hBDA, mul_nonneg h0_fg hBDA, mul_nonneg h0_fh hBDA,
    sq_nonneg (pretDist f h x - 2 * pretDist f g x)]

end Salt.MR
