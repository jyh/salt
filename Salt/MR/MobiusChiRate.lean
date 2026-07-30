/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LambdaRateTwisted
import Salt.MR.VkTwistRegion
import Salt.MR.VkTwistRegionReal
import Salt.SW.MobiusRateClose

/-!
# ⟦O4 + O5⟧ — THE χ-TWISTED MÖBIUS RATE: the spine, the region discharge, the budget

The KMT port's centerpiece (`docs/exploration/port-freeze-0729.md` v2, obligation register
O1–O7): the `MobiusRateClose` route re-run at `L(s,χ)` in place of `ζ(s)`, uniformly over
the height range the ⟦D1⟧ amendment gates (`|t| ≤ y`, `Salt/MR/LambdaRateTwisted.lean`).

**STATUS, PLAINLY.**  This file lands the route's SPINE and its REGION DISCHARGE — the two
pieces that are genuinely new arithmetic — and it isolates the ONE remaining analytic stone,
with the arithmetic that shows the stone's output clears the o(1) budget.  It does NOT land
`MmuChiRate`.  §7 states the residue exactly and names the classical page that closes it.

## The route, and where each piece stands

The twist is a PURE SHIFT of an untwisted Dirichlet series:

  `∑_{n≥1} μ(n)·χ̄(n)n^{it}·n^{-s} = 1/L(s − it, χ⁻¹)`   (§2, LANDED HERE)

because `χ̄ = χ⁻¹` pointwise (`MulChar.star_apply'`) and `n^{it}n^{-s} = n^{-(s-it)}`.  So
the whole `1/ζ` apparatus transports with the single change `ζ(s) ⇝ L(s − it, χ⁻¹)`:

| step | `q = 1` landed name | twisted name | status |
|---|---|---|---|
| Dirichlet series | `LSeries_moebius_eq_zeta_inv` | `LSeries_muChiTw_eq_LFunction_inv` | §2 HERE |
| Riesz mean + Perron | `Salt.SW.mmu1_eq_integral` | `mmu1Chi_eq_integral` | §3 HERE |
| `c`-line inverse bd | `norm_zeta_inv_cline_le` | `norm_muChiTw_LSeries_cline_le` | §4 HERE |
| box non-vanishing | `zeta_zero_free_region` | `LFunction_no_zero_shifted_box` | §5 HERE |
| box EDGE bound | `zeta_inv_shallow` | — | **§7 RESIDUE** |
| contour shift | `Salt.SW.mmu1_contour_shift` | mechanical mirror | §7 |
| budget, de-smoothing | `mmu1_shift_decay` etc. | mechanical mirror | §7 (§6 arith) |

## THE ONE STONE (§7) — and why it is the only one

`Salt.SW.zeta_inv_shallow` (`‖ζ(σ+it)⁻¹‖ ≤ C·log⁷(|t|+2)` on the shallow half-plane
`σ ≥ 1 − c₄/log⁹(|t|+2)`) has NO `L(·,χ)` analogue in this corpus, at any width.  It is not
a corollary of the zero-free region: the region gives non-vanishing, the edge bound gives
SIZE, and the passage from one to the other is the classical Landau page (the
Borel–Carathéodory factorization plus a Jensen zero count — see §7 for the exact route and
the arithmetic that makes it work at VK width).  Everything else in the table is either
landed here or a line-for-line mirror of a landed ζ proof.

**The `q = 1` case is NOT exempt.**  At `t ≠ 0` the principal-character row reads
`1/ζ(s − it)`, so it needs `zeta_inv_shallow` at the VK width too — the landed classical
width `c₄/log⁹(|t|+2)` is worth only `|t| ≤ exp((log y)^{1−δ})` of height (see the ⟦D1⟧
audit in `LambdaRateTwisted.lean`).  The stone is therefore shared by the principal and the
non-principal rows, which is why it is stated once, for `L(·,χ)` at every `χ`.

## Sign and bar conventions (the ⟦barred χ⟧ trap, re-armed)

The datum is the corpus's BARRED form `chiBarTwist χ t n = χ̄(n)·n^{+it}`
(`LambdaRateTwisted.lean` §2; the orientation is forced by `M4Chars.lean:29–60`).  Under
`§2`'s identity the L-function that appears is therefore `L(·, χ⁻¹)` — the INVERSE
character — at the SHIFTED argument `s − it`.  Both are load-bearing:

* `χ⁻¹` and `χ` have the same level `q`, the same `χ² ≠ 1` status
  (`(χ⁻¹)² = (χ²)⁻¹`), and the same `vkStripConst q`, so every gate of the landed χ-VK
  region serves at `χ⁻¹` with the SAME constant (`LFunction_zero_free_region_vk` already
  exploits this in its negative-height half).
* the shift `s − it` moves the box from heights `[−T, T]` to heights `[−T − t, T − t]`,
  which is the entire content of the height gate: §5's discharge is stated at the shifted
  box and the width is read at `|t| + T`.

## The four log scales (the standing trap)

`Lg = log|γ|` (the zero's height), `ℓ = log Lg`, `L3 = log(3|γ|)`, `ℓ3 = log L3` — the
landed region's own scales (`VkTwistRegion.lean` §2).  §6 works at the CONTOUR's scales
`L = log x`, `s = L^{1/10}`, `T = e^s`, and the coupling `H = |t| + T` is stated explicitly
at every step; nothing is left to the reader.
-/

open MeasureTheory Complex Set ArithmeticFunction Filter DirichletCharacter
open scoped LSeries.notation ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace Salt.MR

/-! ## §1 — the twist as a complex power -/

/-- The corpus's phase factor IS `n^{it}`: `exp((t·log n)i) = n^{it}` for `n ≠ 0`.  The
`n ≠ 0` guard is real (`Real.log 0 = 0` makes the left side `1` and the right side `0`). -/
lemma exp_phase_eq_cpow {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    Complex.exp (((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)
      = (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    have h := Complex.ofReal_log hnpos.le
    rw [Complex.ofReal_natCast] at h
    exact h.symm
  rw [Complex.cpow_def_of_ne_zero hnC, hlog]
  congr 1
  push_cast
  ring

/-- **The twisted datum, unpacked.**  `chiBarTwist χ t n = χ⁻¹(n)·n^{it}` for `n ≠ 0`: the
conjugate of a `MulChar` value is its inverse's value (`MulChar.star_apply'`) and the phase
is the complex power (§1). -/
lemma chiBarTwist_eq_inv_mul_cpow {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {n : ℕ}
    (hn : n ≠ 0) :
    chiBarTwist χ t n = χ⁻¹ (n : ZMod q) * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
  simp only [chiBarTwist]
  rw [exp_phase_eq_cpow hn t]
  congr 1
  rw [starRingEnd_apply, MulChar.star_apply']

/-! ## §2 — THE DIRICHLET SERIES: `∑ μ(n)χ̄(n)n^{it}n^{-s} = 1/L(s − it, χ⁻¹)` -/

/-- The twisted Möbius coefficient sequence `n ↦ μ(n)·χ̄(n)n^{it}`.  This is exactly the
summand of the landed `Salt.MR.MmuChi` (`MmuChi χ t y = ∑_{n ∈ Icc 1 y} muChiTw χ t n`, by
definition). -/
def muChiTw {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℕ → ℂ :=
  fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) * chiBarTwist χ t n

@[simp] lemma muChiTw_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    muChiTw χ t 0 = 0 := by
  simp [muChiTw]

/-- `‖μ(n)χ̄(n)n^{it}‖ ≤ 1` — the only size input the whole route needs on the `c`-line. -/
lemma norm_muChiTw_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    ‖muChiTw χ t n‖ ≤ 1 := by
  rw [muChiTw, norm_mul]
  have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [show (((ArithmeticFunction.moebius n : ℤ) : ℂ))
        = (((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hw := norm_chiBarTwist_le_one χ t n
  calc ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ * ‖chiBarTwist χ t n‖
      ≤ 1 * 1 := mul_le_mul hmu hw (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-- `MmuChi` is the partial sum of `muChiTw` (definitional; recorded so the two names are
interchangeable downstream). -/
lemma MmuChi_eq_sum_muChiTw {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (y : ℕ) :
    MmuChi χ t y = ∑ n ∈ Finset.Icc 1 y, muChiTw χ t n := rfl

/-- **§2 THE IDENTITY.**  For `Re s > 1`,
`∑_{n≥1} μ(n)χ̄(n)n^{it}·n^{-s} = (L(s − it, χ⁻¹))⁻¹`.

This is the whole reason the port's centerpiece is a re-run and not a new theory: the height
twist is a TRANSLATION of the spectral variable, and the character conjugation is a swap to
the inverse character.  Both moves are free; what they cost is that the contour must be run
at the SHIFTED box (see §5) — which is the ⟦D1⟧ height gate.

Inputs: mathlib's `DirichletCharacter.LSeries.mul_mu_eq_one` (the twisted Möbius inverse,
the same input the B-probe's `norm_LFunction_inv_cline_le` uses) and
`DirichletCharacter.LFunction_eq_LSeries`. -/
theorem LSeries_muChiTw_eq_LFunction_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (muChiTw χ t) s = (LFunction χ⁻¹ (s - (t : ℂ) * Complex.I))⁻¹ := by
  set u : ℂ := s - (t : ℂ) * Complex.I with hudef
  have hure : u.re = s.re := by
    rw [hudef]
    simp
  have hu : 1 < u.re := by rw [hure]; exact hs
  -- the inverse of `L(·,χ⁻¹)` as an `LSeries`, on `Re u > 1`
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ⁻¹ hu
  have hne : LSeries ↗(χ⁻¹) u ≠ 0 := by
    intro h; rw [h, zero_mul] at hmul; exact zero_ne_one hmul
  have hinv : (LSeries ↗(χ⁻¹) u)⁻¹ = LSeries (↗(χ⁻¹) * ↗ArithmeticFunction.moebius) u :=
    inv_eq_of_mul_eq_one_right hmul
  rw [LFunction_eq_LSeries χ⁻¹ hu, hinv]
  -- termwise
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hsplit : (n : ℂ) ^ s = (n : ℂ) ^ u * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
      rw [← Complex.cpow_add _ _ hnC, hudef]
      ring_nf
    have hcoe : (↗(χ⁻¹) * ↗ArithmeticFunction.moebius : ℕ → ℂ) n
        = χ⁻¹ (n : ZMod q) * ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
      simp [Pi.mul_apply]
    rw [hcoe, muChiTw, chiBarTwist_eq_inv_mul_cpow χ t hn, hsplit]
    have hnu : (n : ℂ) ^ u ≠ 0 := fun h => hnC ((Complex.cpow_eq_zero_iff _ _).mp h).1
    have hnt : (n : ℂ) ^ ((t : ℂ) * Complex.I) ≠ 0 :=
      fun h => hnC ((Complex.cpow_eq_zero_iff _ _).mp h).1
    field_simp

/-! ## §3 — the smoothed twisted Riesz mean and its Perron representation -/

/-- **The smoothed twisted Möbius Riesz mean** `M₁_{μχ̄}(t; x) = ∑_{n ≤ x} μ(n)χ̄(n)n^{it}(1 −
n/x)` — the twisted twin of `Salt.SW.Mmu1`. -/
def Mmu1Chi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, muChiTw χ t n * (1 - (n : ℂ) / (x : ℂ))

/-- **Domination** for the sum ↔ integral swap: `∑ₙ ‖μ(n)χ̄(n)n^{it}‖·(x/n)^c < ∞` for
`c > 1`.  The twist is 1-bounded, so this is the bare `p`-series — no character input, no
`LSeriesSummable` detour (contrast `Salt.SW.mmu_summable_dom`, which routes through
`ArithmeticFunction.LSeriesSummable_moebius_iff`). -/
lemma muChiTw_summable_dom {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {x : ℝ} (hx : 0 ≤ x)
    {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ => ‖muChiTw χ t n‖ * (x / n) ^ c) := by
  have hcomp : Summable (fun n : ℕ => x ^ c * (n : ℝ) ^ (-c)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left (x ^ c)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hcomp
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (show (-c) ≠ 0 by intro h; linarith [neg_eq_zero.mp h])]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Real.div_rpow hx hnpos.le, Real.rpow_neg hnpos.le]
    have hxc : (0 : ℝ) ≤ x ^ c := Real.rpow_nonneg hx c
    have hnc : (0 : ℝ) < (n : ℝ) ^ c := Real.rpow_pos_of_pos hnpos c
    rw [div_eq_mul_inv]
    calc ‖muChiTw χ t n‖ * (x ^ c * ((n : ℝ) ^ c)⁻¹)
        ≤ 1 * (x ^ c * ((n : ℝ) ^ c)⁻¹) :=
          mul_le_mul_of_nonneg_right (norm_muChiTw_le_one χ t n) (by positivity)
      _ = x ^ c * ((n : ℝ) ^ c)⁻¹ := one_mul _

/-- **§3 THE PERRON IDENTITY, `LSeries` form.**  For `x ≥ 1`, `c > 1`,
`M₁_{μχ̄}(t; x) = (1/2π)∫_ℝ x^{c+iv}/((c+iv)(c+iv+1))·L(μχ̄·^{it})(c+iv) dv`.

The kernel machinery is COEFFICIENT-AGNOSTIC and is cited, not re-proved:
`Salt.SW.kernel_sum_swap`, `Salt.SW.riesz_tsum_eq`, `Salt.SW.kernel_identity`,
`Salt.SW.integral_term_eq`, `Salt.SW.s_ne_zero`.  The proof is
`Salt.SW.mmu1_eq_integral_LSeries` with the coefficient sequence `↗μ` replaced by
`muChiTw χ t`; the only thing checked afresh is the domination (above). -/
theorem mmu1Chi_eq_integral_LSeries {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {x : ℝ}
    (hx : 1 ≤ x) {c : ℝ} (hc : 1 < c) :
    Mmu1Chi χ t x = (1 / (2 * Real.pi)) • ∫ v : ℝ,
        ((x : ℂ) ^ ((c : ℂ) + (v : ℂ) * Complex.I) /
            (((c : ℂ) + (v : ℂ) * Complex.I) * ((c : ℂ) + (v : ℂ) * Complex.I + 1)))
          * LSeries (muChiTw χ t) ((c : ℂ) + (v : ℂ) * Complex.I) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hc0 : (0 : ℝ) < c := lt_trans one_pos hc
  have hsum := muChiTw_summable_dom χ t hx0.le hc
  have hInt : (∫ v : ℝ,
        ((x : ℂ) ^ ((c : ℂ) + (v : ℂ) * Complex.I) /
            (((c : ℂ) + (v : ℂ) * Complex.I) * ((c : ℂ) + (v : ℂ) * Complex.I + 1)))
          * LSeries (muChiTw χ t) ((c : ℂ) + (v : ℂ) * Complex.I))
      = ∑' n : ℕ, ∫ v : ℝ, muChiTw χ t n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (v : ℂ) * Complex.I)
          / (((c : ℂ) + (v : ℂ) * Complex.I) * ((c : ℂ) + (v : ℂ) * Complex.I + 1)) := by
    rw [Salt.SW.kernel_sum_swap (muChiTw χ t) hx0 hc0 hsum]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    dsimp only
    rw [Salt.SW.riesz_tsum_eq (muChiTw χ t) hx0.le (Salt.SW.s_ne_zero hc0 v)]
    ring
  have htail : ∀ n ∉ Finset.Icc 1 ⌊x⌋₊,
      (∫ v : ℝ, muChiTw χ t n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (v : ℂ) * Complex.I)
        / (((c : ℂ) + (v : ℂ) * Complex.I) * ((c : ℂ) + (v : ℂ) * Complex.I + 1))) = 0 := by
    intro n hn
    rw [Salt.SW.integral_term_eq (muChiTw χ t n)]
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with h | h
    · have hn0 : n = 0 := Nat.lt_one_iff.mp h
      subst hn0
      rw [muChiTw_zero, zero_mul]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (by omega : n ≠ 0)
      have hypos : (0 : ℝ) < x / n := div_pos hx0 hnR
      have hylt : x / n < 1 := by
        rw [div_lt_one hnR]
        have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
        have h2 : ((⌊x⌋₊ : ℝ) + 1) ≤ n := by exact_mod_cast Nat.succ_le_of_lt h
        linarith
      have hker := Salt.SW.kernel_identity hypos hc0
      rw [if_neg (not_le.mpr hylt), Complex.real_smul] at hker
      have hJ0 := (mul_eq_zero.mp hker).resolve_left (by
        simp only [Complex.ofReal_eq_zero]
        exact (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)).ne')
      rw [hJ0, mul_zero]
  rw [hInt, tsum_eq_sum htail, Finset.smul_sum]
  simp only [Mmu1Chi]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_Icc] at hn
  obtain ⟨hn1, hn2⟩ := hn
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hxn : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hn2) (Nat.floor_le hx0.le)
  have hypos : (0 : ℝ) < x / n := div_pos hx0 hnR
  have hyge : 1 ≤ x / n := by rw [le_div_iff₀ hnR]; linarith
  have hker := Salt.SW.kernel_identity hypos hc0
  rw [if_pos hyge] at hker
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  rw [Salt.SW.integral_term_eq (muChiTw χ t n), ← mul_smul_comm, hker]
  push_cast
  field_simp

/-- **§3 THE PERRON IDENTITY, `1/L` form** — the contour-shift consumable.  For `x ≥ 1`,
`c > 1`,
`M₁_{μχ̄}(t; x) = (1/2π)∫_ℝ x^{c+iv}/((c+iv)(c+iv+1))·(L(c + i(v − t), χ⁻¹))⁻¹ dv`.

Note the SHIFTED height `v − t` in the L-function: this is where the height gate lives.  The
shift is exact (`(c : ℂ) + v·i − t·i = (c : ℂ) + (v − t)·i`), so the integrand is the landed
ζ-integrand with `ζ(c+iv)⁻¹` replaced by `L(c + i(v−t), χ⁻¹)⁻¹` and NOTHING else. -/
theorem mmu1Chi_eq_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) {x : ℝ}
    (hx : 1 ≤ x) {c : ℝ} (hc : 1 < c) :
    Mmu1Chi χ t x = (1 / (2 * Real.pi)) • ∫ v : ℝ,
        ((x : ℂ) ^ ((c : ℂ) + (v : ℂ) * Complex.I) /
            (((c : ℂ) + (v : ℂ) * Complex.I) * ((c : ℂ) + (v : ℂ) * Complex.I + 1)))
          * (LFunction χ⁻¹ ((c : ℂ) + ((v - t : ℝ) : ℂ) * Complex.I))⁻¹ := by
  rw [mmu1Chi_eq_integral_LSeries χ t hx hc]
  refine congrArg (fun z : ℂ => (1 / (2 * Real.pi)) • z) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  dsimp only
  have hre : ((c : ℂ) + (v : ℂ) * Complex.I).re = c := by simp
  have hs : 1 < ((c : ℂ) + (v : ℂ) * Complex.I).re := by rw [hre]; exact hc
  rw [LSeries_muChiTw_eq_LFunction_inv χ t hs]
  congr 2
  push_cast
  ring_nf

/-! ## §4 — the `c`-line inverse bound at the shifted height -/

/-- **The `c`-line bound, twisted.**  For `σ > 1` and ANY heights `v, t`,
`‖(L(σ + i(v−t), χ⁻¹))⁻¹‖ ≤ 1 + 1/(σ−1)`.

This is the landed B-probe bound `norm_LFunction_inv_cline_le` read at the shifted height —
the shift is free because the probe's bound is UNIFORM in the height (it is the twisted
Möbius series majorized termwise, with no height input at all).  On the `c`-line
`c = 1 + 1/log x` this is the constant `1 + log x`, exactly as in the `q = 1` route: the
`log⁷` tail-integral friction never appears. -/
lemma norm_LFunction_inv_shifted_cline_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (v t : ℝ) :
    ‖(LFunction χ⁻¹ ((σ : ℂ) + ((v - t : ℝ) : ℂ) * Complex.I))⁻¹‖ ≤ 1 + 1 / (σ - 1) :=
  norm_LFunction_inv_cline_le χ⁻¹ hσ (v - t)

/-- The same bound stated for the `LSeries` carrier of §2 (the form the Perron integrand
carries before the `1/L` rewrite). -/
lemma norm_muChiTw_LSeries_cline_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) {σ : ℝ} (hσ : 1 < σ) (v : ℝ) :
    ‖LSeries (muChiTw χ t) ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ≤ 1 + 1 / (σ - 1) := by
  have hre : ((σ : ℂ) + (v : ℂ) * Complex.I).re = σ := by simp
  have hs : 1 < ((σ : ℂ) + (v : ℂ) * Complex.I).re := by rw [hre]; exact hσ
  rw [LSeries_muChiTw_eq_LFunction_inv χ t hs]
  have hshift : (σ : ℂ) + (v : ℂ) * Complex.I - (t : ℂ) * Complex.I
      = (σ : ℂ) + ((v - t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hshift]
  exact norm_LFunction_inv_shifted_cline_le χ hσ v t

/-! ## §5 — THE BOX ZERO-FREE DISCHARGE (the height split; the STONE-C RULING (i) pattern)

The contour shift needs `hzf`: no zero of `L(·,χ⁻¹)` in the closed box
`[σ₀, c] × [−T − t, T − t]`.  Since `σ₀ = 1 − w`, that is exactly "every zero with
`Re ρ ≥ 1 − w` has `|Im ρ| > H`" at `H = |t| + T`.  This section discharges it from the
LANDED regions, with the width `w` explicit and the height split honest:

* heights `≥ exp(exp 100) + 1` — the χ-VK region, BOTH arms
  (`LFunction_zero_free_region_vk` for `χ² ≠ 1`, `LFunction_real_zero_free_region_vk` for
  `χ² = 1`), width `(1/(10⁸(A+7)))·1/((log|γ|)^{3/4}(log log|γ|)³)`, transported DOWN to the
  box's top height `H` by monotonicity of `γ ↦ (log γ)^{3/4}(log log γ)³`;
* heights `< exp(exp 100) + 1` — the classical explicit region
  `Salt.SW.zero_free_region_all'`, whose denominator `log(q(|γ|+2))` is bounded by
  `log q + exp 100 + 1` on that range, i.e. the below-floor width is CONSTANT in the height
  and costs only `log q ≤ 12 log log y`;
* the real axis `γ = 0` — the ξ₁ row, carried as the named carve-out hypothesis `hcarve`.
  This is Siegel territory: the `∃H₀` fold is wave P-7's and is deliberately NOT folded here.

**The gate collapses to a `q`-only condition.**  Both VK arms are gated at
`log(20000·(…)) ≤ A·log log|γ|`, and above the floor `log log|γ| ≥ 100` always; so the single
hypothesis `log(20000·(vkStripConst q + 8104)) ≤ 100·A` serves both arms at every admissible
height.  At `q ≤ (log y)^12` it is met by `A = (20 + 12 log log y)/100`, whose cost to the
width is one `log log y` — see the budget note at §6. -/

/-- The χ-VK arm's width at the box's top height `H` (`A` = the gate's free base). -/
def vkBoxWidth (A H : ℝ) : ℝ :=
  (1 / (10 ^ 8 * (A + 7)))
    * (1 / (Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (3 : ℕ)))

/-- The classical below-floor width: `zero_free_region_all'`'s `c₀/log(q(|γ|+2))` with the
height maximized at the VK floor, so `log(|γ|+2) ≤ exp 100 + 1`. -/
def clBoxWidth (c₀ : ℝ) (q : ℕ) : ℝ :=
  c₀ / (Real.log (q : ℝ) + Real.exp 100 + 1)

/-- **The shallow abscissa's width**: the minimum of the two arms, capped at `1/2` so that
the classical region's `1/2 ≤ Re ρ` hypothesis is available for free. -/
def boxWidth (c₀ A : ℝ) (q : ℕ) (H : ℝ) : ℝ :=
  min (1 / 2) (min (vkBoxWidth A H) (clBoxWidth c₀ q))

lemma boxWidth_le_half (c₀ A : ℝ) (q : ℕ) (H : ℝ) : boxWidth c₀ A q H ≤ 1 / 2 :=
  min_le_left _ _

lemma boxWidth_le_vk (c₀ A : ℝ) (q : ℕ) (H : ℝ) : boxWidth c₀ A q H ≤ vkBoxWidth A H :=
  le_trans (min_le_right _ _) (min_le_left _ _)

lemma boxWidth_le_cl (c₀ A : ℝ) (q : ℕ) (H : ℝ) : boxWidth c₀ A q H ≤ clBoxWidth c₀ q :=
  le_trans (min_le_right _ _) (min_le_right _ _)

/-- The width is POSITIVE — the strictness that makes the box discharge a contradiction.  Both
arms are positive above the VK floor (`log H ≥ exp 100`, so `log log H ≥ 100 > 0`) and the
classical denominator `log q + exp 100 + 1` is positive for every `q ≥ 1`. -/
lemma boxWidth_pos {A c₀ H : ℝ} (hA1 : 1 ≤ A) (hc₀pos : 0 < c₀) {q : ℕ}
    (hH : Real.exp (Real.exp 100) + 1 ≤ H) : 0 < boxWidth c₀ A q H := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hLH : Real.exp 100 ≤ Real.log H := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLH0 : (0 : ℝ) < Real.log H := by linarith
  have hℓH : (100 : ℝ) ≤ Real.log (Real.log H) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLH
  have hvk : 0 < vkBoxWidth A H := by
    rw [vkBoxWidth]
    have h1 : (0 : ℝ) < Real.log H ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLH0 _
    have h2 : (0 : ℝ) < Real.log (Real.log H) ^ (3 : ℕ) :=
      pow_pos (by linarith : (0 : ℝ) < Real.log (Real.log H)) 3
    have h3 : (0 : ℝ) < 1 / (10 ^ 8 * (A + 7)) := by positivity
    have h4 : (0 : ℝ) < 1 / (Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (3 : ℕ)) :=
      by positivity
    exact mul_pos h3 h4
  have hcl : 0 < clBoxWidth c₀ q := by
    rw [clBoxWidth]
    have hqlog : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
    have : (0 : ℝ) < Real.log (q : ℝ) + Real.exp 100 + 1 := by linarith
    positivity
  rw [boxWidth]
  exact lt_min (by norm_num) (lt_min hvk hcl)

/-- **The VK width is monotone in the height** — the transport that lets a zero at height
`|γ| ≤ H` be judged by the width at `H`.  Both `log` and `log log` are increasing above the
floor, and the exponents `3/4` (rpow) and `3` (npow) preserve that. -/
lemma vkBoxWidth_le_of_le {A γ H : ℝ} (hA1 : 1 ≤ A)
    (hγ : Real.exp (Real.exp 100) + 1 ≤ γ) (hγH : γ ≤ H) :
    vkBoxWidth A H
      ≤ (1 / (10 ^ 8 * (A + 7)))
          * (1 / (Real.log γ ^ ((3 : ℝ) / 4) * Real.log (Real.log γ) ^ (3 : ℕ))) := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hγpos : (0 : ℝ) < γ := by linarith
  have hLγ : Real.exp 100 ≤ Real.log γ := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLγ0 : (0 : ℝ) < Real.log γ := by linarith
  have hℓγ : (100 : ℝ) ≤ Real.log (Real.log γ) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLγ
  have hLH : Real.log γ ≤ Real.log H := Real.log_le_log hγpos hγH
  have hLH0 : (0 : ℝ) < Real.log H := by linarith
  have hℓH : Real.log (Real.log γ) ≤ Real.log (Real.log H) := Real.log_le_log hLγ0 hLH
  have hcoef : (0 : ℝ) < 1 / (10 ^ 8 * (A + 7)) := by positivity
  have hden : (0 : ℝ) < Real.log γ ^ ((3 : ℝ) / 4) * Real.log (Real.log γ) ^ (3 : ℕ) := by
    have h1 : (0 : ℝ) < Real.log γ ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLγ0 _
    have h2 : (0 : ℝ) < Real.log (Real.log γ) ^ (3 : ℕ) :=
      pow_pos (by linarith : (0 : ℝ) < Real.log (Real.log γ)) 3
    exact mul_pos h1 h2
  have hmono : Real.log γ ^ ((3 : ℝ) / 4) * Real.log (Real.log γ) ^ (3 : ℕ)
      ≤ Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (3 : ℕ) := by
    have h1 : Real.log γ ^ ((3 : ℝ) / 4) ≤ Real.log H ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hLγ0.le hLH (by norm_num)
    have h2 : Real.log (Real.log γ) ^ (3 : ℕ) ≤ Real.log (Real.log H) ^ (3 : ℕ) :=
      pow_le_pow_left₀ (by linarith) hℓH 3
    have h3 : (0 : ℝ) ≤ Real.log γ ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hLγ0.le _
    have h4 : (0 : ℝ) ≤ Real.log (Real.log H) ^ (3 : ℕ) :=
      pow_nonneg (by linarith : (0 : ℝ) ≤ Real.log (Real.log H)) 3
    calc Real.log γ ^ ((3 : ℝ) / 4) * Real.log (Real.log γ) ^ (3 : ℕ)
        ≤ Real.log γ ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (3 : ℕ) := by
          exact mul_le_mul_of_nonneg_left h2 h3
      _ ≤ Real.log H ^ ((3 : ℝ) / 4) * Real.log (Real.log H) ^ (3 : ℕ) := by
          exact mul_le_mul_of_nonneg_right h1 h4
  rw [vkBoxWidth]
  exact mul_le_mul_of_nonneg_left
    (one_div_le_one_div_of_le hden hmono) hcoef.le

/-- `log(|γ|+2) ≤ exp 100 + 1` below the VK floor: the below-floor width is CONSTANT in the
height, so the classical region's only cost is `log q`. -/
lemma log_le_of_below_floor {γ : ℝ} (hγ : γ < Real.exp (Real.exp 100) + 1) (hγ0 : 0 ≤ γ) :
    Real.log (γ + 2) ≤ Real.exp 100 + 1 := by
  set E : ℝ := Real.exp (Real.exp 100) with hE
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ E := by
    have h2 : Real.exp 100 ≤ E := by rw [hE]; exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hEe : E + 3 ≤ Real.exp (Real.exp 100 + 1) := by
    rw [Real.exp_add, ← hE]
    nlinarith [hEbig, he1]
  calc Real.log (γ + 2) ≤ Real.log (E + 3) := by
        apply Real.log_le_log (by linarith) (by linarith)
    _ ≤ Real.exp 100 + 1 := by
        rw [← Real.log_exp (Real.exp 100 + 1)]
        exact Real.log_le_log (by linarith) hEe

set_option maxHeartbeats 1200000 in
-- The three-way height split threads two VK arms and the classical region through one
-- width-monotonicity ladder; the elaborator needs headroom past the default.
/-- **§5 THE DISCHARGE — no zero of `L(·,χ)` in the shallow box, UNCONDITIONAL modulo the
ξ₁ carve-out.**  For `χ ≠ 1` mod `q`, under

* the collapsed `q`-scale gate `hgate : log(20000·(vkStripConst q + 8104)) ≤ 100·A`,
* the box's top height `H ≥ exp(exp 100) + 1`,
* the classical region `hcl` (instantiate with `Salt.SW.zero_free_region_all'`),
* the ξ₁ carve-out `hcarve` on the real axis (wave P-7's Siegel fold),

no zero `ρ` of `L(·,χ)` has `1 − boxWidth c₀ A q H ≤ Re ρ` and `|Im ρ| ≤ H`.

This is the "STONE-C RULING (i)" pattern — the VK region above the landed floor, the
classical explicit region below it — carried out at BOTH VK arms, so nothing is assumed about
`χ²`.  Note what is NOT needed: no primitivity (the classical arm is the imprimitive
extension `zero_free_region_all'`), no height sign convention (both VK arms are two-sided),
and no `Re ρ < 1` input (it comes free from `LFunction_ne_zero_of_one_le_re`). -/
theorem LFunction_no_zero_in_box {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) {A c₀ H : ℝ} (hA1 : 1 ≤ A) (hc₀pos : 0 < c₀)
    (hH : Real.exp (Real.exp 100) + 1 ≤ H)
    (hgate : Real.log (20000 * (vkStripConst q + 8104)) ≤ 100 * A)
    (hcl : ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
        (χ.primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)))
    (hcarve : ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im = 0 → ρ.re ≤ 1 - boxWidth c₀ A q H)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ : 1 - boxWidth c₀ A q H / 2 ≤ ρ.re)
    (hIm : |ρ.im| ≤ H) : False := by
  have hwpos : 0 < boxWidth c₀ A q H := boxWidth_pos hA1 hc₀pos hH
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast this
  -- `Re ρ < 1` for free
  have hβ1 : ρ.re < 1 := by
    by_contra hcn
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp hcn) hρ0
  -- `1/2 ≤ Re ρ` from the width cap
  have hhalf : (1 : ℝ) / 2 ≤ ρ.re := by
    have := boxWidth_le_half c₀ A q H
    linarith
  -- the VK arms' gate, at any admissible height
  have hgate_of : ∀ γ : ℝ, Real.exp (Real.exp 100) + 1 ≤ γ →
      Real.log (20000 * (vkStripConst q + 8104)) ≤ A * Real.log (Real.log γ) := by
    intro γ hγ
    have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
    have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
      have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hγpos : (0 : ℝ) < γ := by linarith
    have hLγ : Real.exp 100 ≤ Real.log γ := by
      rw [← Real.log_exp (Real.exp 100)]
      exact Real.log_le_log (Real.exp_pos _) (by linarith)
    have hℓγ : (100 : ℝ) ≤ Real.log (Real.log γ) := by
      rw [← Real.log_exp 100]
      exact Real.log_le_log (Real.exp_pos _) hLγ
    nlinarith [hgate, hℓγ, hA1]
  rcases le_or_gt (Real.exp (Real.exp 100) + 1) |ρ.im| with habove | hbelow
  · -- ABOVE THE FLOOR: the χ-VK region, both arms
    have hwid := vkBoxWidth_le_of_le (A := A) (γ := |ρ.im|) (H := H) hA1 habove hIm
    have hvk : ρ.re ≤ 1 - (1 / (10 ^ 8 * (A + 7)))
        * (1 / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ))) := by
      by_cases hsq : χ ^ 2 = 1
      · refine LFunction_real_zero_free_region_vk hχ1 hsq hA1 hρ0 hβ1 habove ?_
        exact hgate_of _ habove
      · refine LFunction_zero_free_region_vk hχ1 hsq hA1 hρ0 hβ1 habove ?_
        refine le_trans ?_ (hgate_of _ habove)
        apply Real.log_le_log
        · have := one_le_vkStripConst (q := q); positivity
        · have : (0 : ℝ) ≤ 8104 := by norm_num
          nlinarith [one_le_vkStripConst (q := q)]
    have hbw := boxWidth_le_vk c₀ A q H
    linarith [hvk, hwid, hbw]
  · -- BELOW THE FLOOR: the classical explicit region, or the ξ₁ carve-out at `γ = 0`
    rcases eq_or_ne ρ.im 0 with him0 | him0
    · linarith [hcarve ρ hρ0 him0]
    · have hcls := hcl hρ0 hhalf (Or.inr him0)
      have habs0 : (0 : ℝ) ≤ |ρ.im| := abs_nonneg _
      have hlog2 : Real.log ((q : ℝ) * (|ρ.im| + 2))
          ≤ Real.log (q : ℝ) + Real.exp 100 + 1 := by
        rw [Real.log_mul (by linarith) (by linarith)]
        linarith [log_le_of_below_floor (γ := |ρ.im|) hbelow habs0]
      have hden0 : (0 : ℝ) < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
        apply Real.log_pos
        nlinarith [habs0, hq1]
      have hmono : clBoxWidth c₀ q ≤ c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
        rw [clBoxWidth]
        exact div_le_div_of_nonneg_left hc₀pos.le hden0 hlog2
      have hbw := boxWidth_le_cl c₀ A q H
      linarith [hcls, hmono, hbw]

/-- **§5 COROLLARY — the `hzf` shape at the SHIFTED box.**  The contour of §3 reads
`L(·,χ⁻¹)` at heights `Im s − t` with `|Im s| ≤ T`, so with `H = |t| + T` the discharge above
is exactly the hypothesis the contour shift consumes.  (Stated at `χ` for reuse; the consumer
instantiates at `χ⁻¹`, whose level and gate are identical.) -/
theorem LFunction_no_zero_in_shifted_box {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) {A c₀ t T H : ℝ} (hA1 : 1 ≤ A) (hc₀pos : 0 < c₀)
    (hH : Real.exp (Real.exp 100) + 1 ≤ H) (hHt : |t| + T ≤ H)
    (hgate : Real.log (20000 * (vkStripConst q + 8104)) ≤ 100 * A)
    (hcl : ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
        (χ.primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)))
    (hcarve : ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im = 0 → ρ.re ≤ 1 - boxWidth c₀ A q H)
    {ρ : ℂ} (hρ0 : LFunction χ ρ = 0) (hβ : 1 - boxWidth c₀ A q H / 2 ≤ ρ.re)
    (hIm : |ρ.im + t| ≤ T) : False := by
  refine LFunction_no_zero_in_box hχ1 hA1 hc₀pos hH hgate hcl hcarve hρ0 hβ ?_
  have h1 := abs_le.mp hIm
  have h2 : t ≤ |t| := le_abs_self t
  have h3 : -|t| ≤ t := neg_abs_le t
  exact abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩

/-! ## §6 — THE RESIDUE, STATED: the χ-VK shallow inverse bound

What is left of O4+O5 after §§1–5 is ONE analytic statement, and it is the exact `L(·,χ)`
analogue of the landed `Salt.SW.zeta_inv_shallow` — moved from the classical width
`c₄/log⁹(|t|+2)` to the VK width.  Stated below as `LFunctionInvShallowVk`.

## THE ROUTE THAT CLOSES IT (the classical Landau page, with the arithmetic checked)

Not the anchor-plus-transport route: that one provably FAILS here.  With the landed strip
growth `M = vkStripConst q·(1 + log 3γ)` (`vk_char_box_growth`) and half-width `Θ = vkTheta`,
a 3-4-1 anchor at `σ − 1 = δ` gives `‖L‖ ≥ c·δ^{3/4}M^{−1/4}`, while Cauchy on a disc of
radius `Θ` gives `‖L′‖ ≤ M/Θ`, so the transport over `δ` closes only for
`δ ≲ Θ⁴/M⁵ ≍ 1/(q⁵(log γ)⁸)` — and the `q⁵` alone destroys the saving at
`q ≤ (log y)^12`.  **Record this as a dead end; it is not obvious from the outside.**

The route that works is the partial-fraction one:

1. `Salt.Vk.entire_norm_logDeriv_sub_sum_scaled` at `G = L(·,χ)/L(c,χ)`, `c = (1+Θ/2)+iτ`
   (the SAME call the B-probe's `LFunction_keep_one_disc` already makes — so the sphere
   hypotheses are already discharged by `LFunction_ratio_bound` at `M₀ = 5M/Θ`).  It returns
   the factorization `G = ∏_{ρ∈Z}(z−ρ)^{m ρ}·h` with `h` analytic and non-vanishing on the
   ball, plus `‖logDeriv G − ∑ m/(z−ρ)‖ ≤ K := (120/λ)·log(4M₀)` there, i.e.
   `‖logDeriv h‖ ≤ K`.
2. `log‖h(s)‖ − log‖h(c)‖ = Re ∫_c^s logDeriv h`, so `‖h(s)‖ ≥ ‖h(c)‖·e^{−K‖s−c‖}`; and
   `‖s−c‖ ≤ Θ` on the shallow segment, so the loss is `e^{−KΘ} = (20M/Θ)^{−140}` —
   POLYNOMIAL in `q` and `log γ`, which the quasi-power saving absorbs.
3. `G(c) = 1` forces `‖h(c)‖ = 1/∏‖c−ρ‖^{m ρ} ≥ 1` (every `‖c−ρ‖ ≤ 9Θ/7 < 1`).
4. The product factor: `‖s−ρ‖ ≥ w/2` for `s` on the line `1 − w/2` and every zero at
   `Re ρ ≤ 1 − w` (this is where §5's discharge is spent), against `‖c−ρ‖ ≤ 9Θ/7`, so the
   product loses `(7w/(18Θ))^{∑m}`.  With `w ≍ Θ/log(20M/Θ)` this is
   `exp(−∑m·(log log(20M/Θ) + O(1)))`.
5. THE ONE MISSING INPUT: a Jensen zero count `∑_{ρ∈Z} m ρ ≲ log(4M₀)` on the ball.  Then
   step 4's loss is `exp(−C·log(20M/Θ)·log log(20M/Θ))`, which at `log(20M/Θ) ≍ log log y`
   is `(log y)^{−C log log log y}` — beaten by the quasi-power saving
   `exp(−c(log y)^{1/4}/(log log y)³)` with room to spare.
   (`Salt.SW.LFunction_zero_count_le` and `Salt/SW/ZeroCountNearOne.lean` are the corpus's
   existing zero-count pages; whether either is stated at the ball this needs is the first
   thing the closing wave should grep.)

## THE o(1) BUDGET (REF-P-MATH's standing gate) — IT CLEARS, WITH ROOM

The gate: the delivered exponent must support `c ≥ 1.449` in the final cascade, and the
`−2 + o(1)` architecture ceiling admits `o(1) ≤ 0.29`.  The rate this route delivers is the
`∀ A` form — `y/(log y)^A` for EVERY fixed `A` — because the saving is
`x^{σ₀−1} = exp(−w·log x)` with

  `w ≍ 1/((log q + log log H)·(log H)^{3/4}·(log log H)³)`,  `H = |t| + T`,

so at the contour's parameters (`T = exp((log x)^{1/10})`, `|t| ≤ x`, `q ≤ (log x)^{12}`,
hence `log H ≤ 2 log x` and `log q ≤ 12 log log x`) the saving is

  `exp(−c·(log x)^{1/4}/((log log x)⁴))`,

a QUASI-POWER of `log x`, which is `o((log x)^{−A})` for every fixed `A` (a power of `log x`
in the exponent beats every fixed log-power; the crossover is the finite `x₀` the existential
in `MmuChiRate` absorbs).

III.3″ NUMERIC SANITY (symbolic, and it is worth stating because the threshold is large).
Write `L = log x`, take `|t| ≤ x` (so `log H ≑ L`), `q = L^12`, and read the width's own
constants: the gate needs `A ≑ (19 + 12 log L)/100` and the VK arm gives
`w = 1/(10⁸·(A+7)·L^{3/4}·(log L)³)`, so the saving exponent is
`w·L = L^{1/4}/(10⁸·(A+7)·(log L)³)`.  At `L = 10⁶` that is `≈ 1.4·10^{−11}` — NO saving yet.
The crossover against `A_target·log L` at `A_target = 5` is at `L ≈ 10^{77}`, i.e.
`x ≈ exp(10^{77})`: astronomically large, FINITE, and absorbed by `MmuChiRate`'s `∃ x₀`.  This
is the same genre as the landed `q = 1` route's own threshold note
(`MobiusRate.lean` §"III.3″ numeric sanity"), one iterated log worse because of the `q`-gate's
`A` and the `(log log H)³`.  Nothing in the cascade reads `x₀`.

**The `∀ A` form is `c = ∞`-genre in the cascade's accounting: the o(1) budget clears with the
whole `0.29` unspent.**  The polynomial edge losses of §6's steps
2 and 4 — `(20M/Θ)^{140}` and `exp(C log(20M/Θ)log log(20M/Θ))` — are absorbed by the same
quasi-power, which is why the width, not the edge constant, is the only thing that had to be
tracked sharply. -/

/-- The shallow width the stone must deliver: the VK shape, `q`-graded ADDITIVELY (the
`log q` sits in a factor, never in an exponent — the KR-2 finding of the B-probe, carried
through). -/
def vkShallowWidth (c₄ : ℝ) (q : ℕ) (H : ℝ) : ℝ :=
  c₄ / ((Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
          * Real.log (Real.log H) ^ (3 : ℕ))

lemma vkShallowWidth_pos {c₄ H : ℝ} (hc₄ : 0 < c₄) {q : ℕ}
    (hH : Real.exp (Real.exp 100) + 1 ≤ H) : 0 < vkShallowWidth c₄ q H := by
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hLH : Real.exp 100 ≤ Real.log H := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLH0 : (0 : ℝ) < Real.log H := by linarith
  have hℓH : (100 : ℝ) ≤ Real.log (Real.log H) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLH
  have h1 : (0 : ℝ) < Real.log H ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLH0 _
  have h2 : (0 : ℝ) < Real.log (Real.log H) ^ (3 : ℕ) :=
    pow_pos (by linarith : (0 : ℝ) < Real.log (Real.log H)) 3
  have hq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  rw [vkShallowWidth]
  have hden : (0 : ℝ) < (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
      * Real.log (Real.log H) ^ (3 : ℕ) := by
    have : (0 : ℝ) < Real.log (q : ℝ) + 1 := by linarith
    positivity
  exact div_pos hc₄ hden

/-- **⟦THE RESIDUE OF O4+O5⟧ — the χ-VK shallow inverse bound.  NOT LANDED.**

`‖L(σ+it,χ)⁻¹‖ ≤ K·((log q + 1)·log H)^m` throughout the shallow box
`1 − vkShallowWidth c₄ q H ≤ σ ≤ 2`, `|t| ≤ H`, for every `χ ≠ 1` mod `q` and every
`H ≥ exp(exp 100) + 1`, GIVEN the ξ₁ carve-out on the real axis.

This is the exact `L(·,χ)` analogue of the landed `Salt.SW.zeta_inv_shallow`, at the VK width
instead of the classical one.  It is the ONLY thing between this file and `MmuChiRate`:

* `hzf` (no zero in the box) — LANDED above, `LFunction_no_zero_in_box` / `_in_shifted_box`;
* `hbox` (the edge bound) — THIS `Prop`;
* the contour shift, the budget and the de-smoothing — line-for-line mirrors of
  `Salt.SW.mmu1_contour_shift`, `mmu1_shift_decay`, `mmuRate_of_smoothed`, with `ζ(s)⁻¹`
  replaced by `L(s − it, χ⁻¹)⁻¹` (§3's Perron identity is already in that form) and the
  `c`-line constant supplied by §4 (`1 + 1/(σ−1)`, uniform in the height — the same
  simplification the `q = 1` route enjoys).

The polynomial form `K·((log q+1)·log H)^m` of the bound is deliberately generous: §6's
budget note shows the quasi-power saving absorbs ANY fixed polynomial in `log q` and `log H`,
so the closing wave is free to be lossy in the edge constant and must be sharp only in the
width.  The `q = 1`/principal row is included (`χ ≠ 1` fails only for the principal character
mod `q`, whose row reads `1/ζ(s−it)·∏_{p∣q}(1−p^{−s+it})^{−1}`; the ζ factor needs THE SAME
stone at VK width, and the finite Euler product is bounded by `2^{ω(q)}`-genre bookkeeping on
`Re ≥ 1/2`). -/
def LFunctionInvShallowVk : Prop :=
  ∃ (c₄ K : ℝ) (m : ℕ), 0 < c₄ ∧ 0 < K ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ H : ℝ,
      Real.exp (Real.exp 100) + 1 ≤ H →
      (∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im = 0 → ρ.re < 1 - vkShallowWidth c₄ q H) →
      ∀ σ t : ℝ, 1 - vkShallowWidth c₄ q H ≤ σ → σ ≤ 2 → |t| ≤ H →
        ‖(LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖
          ≤ K * ((Real.log (q : ℝ) + 1) * Real.log H) ^ m

/-- **The residue, in one line.**  `LFunctionInvShallowVk` plus the mechanical mirror of the
`q = 1` contour/budget/de-smoothing chain yields the ⟦D1⟧-amended `MmuChiRate` with the ξ₁
carve-out.  Recorded as a `Prop`-level statement of the remaining obligation so that the
closing wave has a single target and the corpus census can see it.

NOT a theorem: the mirror is ~800 lines of `Salt.SW.MobiusRateClose` re-run, and this wave
stopped at the analytic boundary rather than at the mechanical one (the ruling: a STOP on a
deliverable is first-class).  §6 records both the route and the arithmetic that the mirror
needs; nothing in it is open except the stone. -/
def MmuChiRate_residue : Prop :=
  LFunctionInvShallowVk →
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ ρ : ℂ, LFunction χ⁻¹ ρ = 0 → ρ.im = 0 → ρ.re < 1 / 2) →
      MmuChiRate

end Salt.MR

end
