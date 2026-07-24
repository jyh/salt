/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ChiEuler

/-!
# ROUTE A leg H2 — the bounded-height χ-quality floor (`ChiFloorLow`)

The LAST stone of ROUTE A (`docs/exploration/chi-check-0724.md`, the "BIGGER FINDING"):
`ChiFloor.lean`'s `chi_floor_orderOf` covers the EXTREME frequencies `1 ≤ |k·t|`
(`k = 2·orderOf χ`); this file covers the complementary BOUNDED band `|k·t| < 1`, i.e.
`|t| < 1/(2·orderOf χ)`, and JOINS the two into a single all-`t` statement.

## The honest supply verdict (recorded, not guessed)

The floor-side bridge `chi_dist_bridge` (`ChiEuler.lean:339`) reduces H2 to ONE analytic
input — a LOWER bound on `log‖L(1 + 1/log X − it, χ)‖` at bounded height.  A census of the
landed SW zero-theory chain gives:

* **(a) — NOT available.**  The chain exports the zero-free REGION
  (`Salt.SW.zero_free_region_all'`, `c₀ = 1/126848`) and the Landau/Borel–Carathéodory
  machinery it is built from (`landau_neg_logDeriv_re_lower`, `three_four_one`,
  `LFunction_norm_logDeriv_sub_sum`), but NO `‖L(σ+it,χ)‖` lower bound near `σ = 1`.  The
  only landed `‖L‖` lower bounds are `Salt.SW.LFunction_center_lower` (`Re s ≥ 2`, value
  `1/4` — far from the 1-line) and the `s = 1` Siegel family below.
* **(b) — available only at `s = 1`, and the shift does NOT close.**
  `Salt.SW.siegel_theorem` / `siegel_L_one_exceptional` / `L1_lower_siegel` /
  `goldfeld_L_one_lower` bound `L(1,χ)` from below (ineffectively, as Siegel must).  The
  excursion from `s = 1` to `s = 1 + 1/log X − it` is NOT bounded over the whole H2 band:
  at `ord χ = 2` the band is `|t| < 1/4`, and `|L(1+δ−it,χ)/L(1,χ)|` there is governed by
  exactly the missing (a)-grade bound.  (Only the sub-band `|t| ≲ 1/log X` closes by a
  tangent/FTC estimate — a strictly smaller range than the join needs.)
* **(c) — THE EXIT TAKEN.**  The general-χ H2 floor is landed in NAMED-HYPOTHESIS form
  (`chi_floor_low_of_Llower`), pinning the exact interface the future (a)-stone must
  supply; and the PRINCIPAL character `χ₀` is landed UNCONDITIONALLY
  (`chi_floor_low_principal`), where the ζ-side pole patch `Salt.MR.zeta_lower_small_t`
  supplies the missing lower bound outright.  Consequently ROUTE A closes WHOLE and
  unconditionally at `χ = χ₀` (`chi_floor_all_principal`), and closes for every χ modulo
  the single named L-lower hypothesis (`chi_floor_all_of_Llower`).

Nothing here hides the Siegel obstruction: it is genuinely present.  A Siegel-zero
character has `χ(p) ≈ −1 = λ(p)` on most primes, so `λ·χ̄ ≈ 1 = n^{i·0}` and the H2 floor is
FALSE for it without an ineffective input.  The named hypothesis `−B ≤ log‖L(…)‖` is
precisely where that ineffective constant enters.

## Contents

* `chi_floor_low_of_Llower` (F1) — the H2 floor from a named L-lower bound at the bridge
  point `1 + 1/log X − it`.  One `linarith` off `chi_dist_bridge`.
* `chiTwist_one_sum_ge` (F2a) — the `χ₀`-vs-`1` prime-sum comparison, with the HONEST
  `primeDivSum` deficit (constant `1`, per-prime exact, matching `pretDistSq_chiPrin_ge`).
* `chi_floor_low_principal` (F2) — the UNCONDITIONAL H2 floor at `χ = χ₀`, valid on the
  whole bounded band `|t| ≤ 3` (which strictly contains the H2 band `|t| < 1/2` there):
  `loglog X − C − ∑_{p|q, p≤X} 1/p ≤ 𝔻(λ·χ̄₀, n^{it}; X)²`.
* `chi_floor_all_principal` / `chi_floor_all_principal_twisted` (F3) — the ROUTE-A JOIN at
  `χ₀`: ALL `t`, unconditional, in the `λ·χ̄` and in the MRT `𝔻(λ, χ·n^{it})` shape.
* `chi_floor_all_of_Llower` / `chi_floor_all_of_Llower_twisted` (F3) — the ROUTE-A JOIN for
  a general χ, carrying the L-lower hypothesis ONLY on the bounded band.

## The join geometry

`k := 2·orderOf χ` (even, nonzero, kills χ).  For every real `t` exactly one of

* `1 ≤ |k·t|` — H1 fires (`chi_floor_orderOf`), debit
  `(3/4)loglog(|kt|+3) + 5·logloglog(|kt|+16) + C_{H1} + ∑_{p|q,p≤X}1/p`, all over `k²`;
* `|k·t| < 1` — H2 fires (this file), debit `B + C_{H2}` (χ₀: `C + ∑_{p|q,p≤X}1/p`).

The two debits have genuinely different shapes, so the join is stated as the `min` of the
two floors — no lossy common majorant is invented.  The two constants are carried as two
SEPARATE existentials, so neither branch pays the other's price.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## F1 — the H2 floor from a named L-lower bound -/

/-- **F1 — the bounded-height χ-quality floor, conditional form
(`chi_floor_low_of_Llower`).**  There is a constant `K`, UNIFORM in `q`, `χ`, `X`, `t` and
`B`, such that a lower bound `−B ≤ log‖L(1 + 1/log X − it, χ)‖` at the bridge point yields

  `loglog X − B − K ≤ 𝔻(λ·χ̄, n^{it}; X)²`   for `X ≥ e`.

This is the EXACT interface the H2 leg needs: the sign-pinned argument
`1 + 1/log X − it` (not `+it`, not `χ̄` — see `ChiEuler.lean`'s sign page), and the debit
enters additively, so an `L`-lower of grade `q^{−ε}` gives a debit `ε·log q` and an
`L`-lower of grade `(log(q(|t|+2)))^{−A}` gives `A·log log(q(|t|+2))`.

One `linarith` off the landed `chi_dist_bridge` (`ChiEuler.lean:339`); `K` is that bridge's
constant verbatim, so it is `q`-free, `χ`-free, `X`-free and `t`-free. -/
theorem chi_floor_low_of_Llower :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X t B : ℝ),
      Real.exp 1 ≤ X →
      -B ≤ Real.log ‖DirichletCharacter.LFunction χ
            (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ →
        Real.log (Real.log X) - B - K ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨K, hK⟩ := chi_dist_bridge
  refine ⟨K, ?_⟩
  intro q _ χ X t B hX hB
  have h := hK q χ X t hX
  linarith

/-! ## F2 — the principal character, UNCONDITIONALLY -/

/-- **F2a — the `χ₀`-vs-`1` prime-sum comparison.**  For every modulus `q` and all real
`t, X`,

  `∑_{p≤X} cos(t·log p)/p − ∑_{p|q, p≤X} 1/p ≤ ∑_{p≤X} Re(χ₀(p)·p^{it})/p`.

Per prime, EXACTLY as in `pretDistSq_chiPrin_ge`: at `p ∤ q` the two sides agree
(`χ₀(p) = 1`); at `p | q` the left loses `cos(t·log p)/p − 1/p ≤ 0`.  The honest constant
is `1`, not `2`. -/
theorem chiTwist_one_sum_ge (q : ℕ) (t X : ℝ) :
    (∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
        Real.cos (t * Real.log p) / (p : ℝ)) - primeDivSum q X
      ≤ ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
          (chiTwist (1 : DirichletCharacter ℂ q) t p).re / (p : ℝ) := by
  have hpds : primeDivSum q X
      = ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
          (if p ∣ q then (1 : ℝ) / (p : ℝ) else 0) := by
    unfold primeDivSum
    rw [← Finset.filter_filter, Finset.sum_filter]
  rw [hpds, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_filter] at hp
  have hprime : Nat.Prime p := hp.2
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  by_cases hdvd : p ∣ q
  · have hnu : ¬ IsUnit ((p : ℕ) : ZMod q) := by
      rw [ZMod.isUnit_prime_iff_not_dvd hprime]; exact not_not_intro hdvd
    have hz : (1 : DirichletCharacter ℂ q) ((p : ℕ) : ZMod q) = 0 := MulChar.map_nonunit _ hnu
    have hneg : (0 : ℝ) ≤ (1 - Real.cos (t * Real.log p)) / (p : ℝ) :=
      div_nonneg (by linarith [Real.cos_le_one (t * Real.log (p : ℝ))]) hppos.le
    rw [sub_div] at hneg
    rw [if_pos hdvd]
    simp only [chiTwist_apply, hz, zero_mul, Complex.zero_re, zero_div]
    linarith
  · have hu : IsUnit ((p : ℕ) : ZMod q) := (ZMod.isUnit_prime_iff_not_dvd hprime).mpr hdvd
    have hone : (1 : DirichletCharacter ℂ q) ((p : ℕ) : ZMod q) = 1 := MulChar.one_apply hu
    rw [if_neg hdvd]
    simp only [chiTwist_apply, hone, one_mul, costwist_re, sub_zero]
    exact le_refl _

/-- **F2 — the UNCONDITIONAL bounded-height floor at the PRINCIPAL character.**  There is
a constant `C` (uniform in `q`, `X`, `t`) with

  `loglog X − C − ∑_{p|q, p≤X} 1/p ≤ 𝔻(λ·χ̄₀, n^{it}; X)²`   for `X ≥ e` and `|t| ≤ 3`.

This is the (c)-verdict's unconditional half.  The route bypasses the missing L-lower bound
entirely by staying on the PRIME-SUM side: `pretDistSq_lamChi_split` splits off the Mertens
part, `chiTwist_one_sum_ge` trades `χ₀` for the constant datum `1` at the honest
`primeDivSum` price, the landed λ-side ζ-bridge `euler_osc_bridge_le_unconditional` turns
the remaining `∑cos(t·log p)/p` into `log‖ζ(1+1/log X+it)‖ − K`, and the ζ pole patch
`zeta_lower_small_t` (`ZetaLowerAllT.lean:103`) bounds that below by `log δ` on the whole
box `Re ∈ [1,2]`, `|Im| ≤ 3` — the pole at `s = 1` only HELPS, which is exactly why the
principal character escapes Siegel.  `C = 12 + K − M − log δ` with `M` the Meissel–Mertens
constant.  The height cap `3` strictly contains the H2 band at `χ₀` (`|t| < 1/2`). -/
theorem chi_floor_low_principal :
    ∃ C : ℝ, ∀ (q : ℕ) (X t : ℝ), Real.exp 1 ≤ X → |t| ≤ 3 →
      Real.log (Real.log X) - C - primeDivSum q X
        ≤ pretDistSq (lamChi (1 : DirichletCharacter ℂ q)) (costwist t) X := by
  obtain ⟨K, hK⟩ := euler_osc_bridge_le_unconditional
  obtain ⟨δ, hδ, hsmall⟩ := zeta_lower_small_t
  refine ⟨12 + K - Salt.Mertens.mertensM - Real.log δ, ?_⟩
  intro q X t hX ht3
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hX2 : (2 : ℝ) ≤ X := le_trans h2e hX
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hd0 : (0 : ℝ) < 1 / Real.log X := one_div_pos.mpr hlogXpos
  have hd1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hlogXpos]; linarith
  have hzlow := hsmall (1 / Real.log X) t hd0.le hd1 ht3 (fun h => absurd h.1 (ne_of_gt hd0))
  have hlogz : Real.log δ ≤ Real.log ‖riemannZeta
      (((1 + 1 / Real.log X : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ := Real.log_le_log hδ hzlow
  have hbr := hK X t hX
  have hmert := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hX2)
  have h12 : 12 / Real.log X ≤ 12 := by
    rw [div_le_iff₀ hlogXpos]; nlinarith
  have hsum := chiTwist_one_sum_ge q t X
  rw [pretDistSq_lamChi_split (1 : DirichletCharacter ℂ q) t X]
  linarith [hmert.1]

/-! ## F3 — the ROUTE-A JOIN -/

/-- **F3 — the ROUTE-A χ-quality floor, WHOLE and UNCONDITIONAL at the principal
character.**  There are constants `CH1` (the H1 debit) and `CH2` (the H2 debit) with: for
every `q ≠ 0`, every `X ≥ e` and EVERY real `t`,

  `min( loglog X − CH2 − ∑_{p|q,p≤X}1/p,`
  `     [loglog X − (3/4)loglog(|2t|+3) − 5·logloglog(|2t|+16) − CH1 − ∑_{p|q,p≤X}1/p]/4 )`
  `  ≤ 𝔻(λ·χ̄₀, n^{it}; X)²`.

The two frequency ranges of ROUTE A, joined: `1 ≤ |2t|` is H1
(`chi_floor_orderOf` at `k = 2·orderOf χ₀ = 2`, so the `1/k²` is `1/4`), and `|2t| < 1`
forces `|t| < 1/2 ≤ 3`, which is H2 (`chi_floor_low_principal`).  No hypothesis beyond
`q ≠ 0` and `X ≥ e`: at `χ₀` ROUTE A is COMPLETE. -/
theorem chi_floor_all_principal :
    ∃ CH1 CH2 : ℝ, ∀ (q : ℕ) (X t : ℝ), q ≠ 0 → Real.exp 1 ≤ X →
      min (Real.log (Real.log X) - CH2 - primeDivSum q X)
          ((Real.log (Real.log X)
              - (3 / 4) * Real.log (Real.log (|2 * t| + 3))
              - 5 * Real.log (Real.log (Real.log (|2 * t| + 16)))
              - CH1 - primeDivSum q X) / 4)
        ≤ pretDistSq (lamChi (1 : DirichletCharacter ℂ q)) (costwist t) X := by
  obtain ⟨CH1, hCH1⟩ := chi_floor_orderOf
  obtain ⟨CH2, hCH2⟩ := chi_floor_low_principal
  refine ⟨CH1, CH2, fun q X t hq hX => ?_⟩
  have hk : ((2 * orderOf (1 : DirichletCharacter ℂ q) : ℕ) : ℝ) = 2 := by
    rw [orderOf_one]; norm_num
  have h4 : ((2 : ℝ)) ^ 2 = 4 := by norm_num
  by_cases hbig : 1 ≤ |2 * t|
  · refine le_trans (min_le_right _ _) ?_
    have h := hCH1 q (1 : DirichletCharacter ℂ q) X t hq hX (by rw [hk]; exact hbig)
    rw [hk, h4] at h
    exact h
  · refine le_trans (min_le_left _ _) ?_
    have hlt : |2 * t| < 1 := not_le.mp hbig
    have habs : |2 * t| = 2 * |t| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [habs] at hlt
    exact hCH2 q X t hX (by linarith [abs_nonneg t])

/-- **F3 (MRT shape) — the same all-`t` unconditional floor on `𝔻(λ, χ₀·n^{it}; X)²`**, the
object the quality infimum `M(λ; X, W)` actually ranges over.  One rewrite through the exact
twist transfer `pretDistSq_lam_chi_twist` (`ChiFloor.lean:208`). -/
theorem chi_floor_all_principal_twisted :
    ∃ CH1 CH2 : ℝ, ∀ (q : ℕ) (X t : ℝ), q ≠ 0 → Real.exp 1 ≤ X →
      min (Real.log (Real.log X) - CH2 - primeDivSum q X)
          ((Real.log (Real.log X)
              - (3 / 4) * Real.log (Real.log (|2 * t| + 3))
              - 5 * Real.log (Real.log (Real.log (|2 * t| + 16)))
              - CH1 - primeDivSum q X) / 4)
        ≤ pretDistSq lam
            (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q) * costwist t n) X := by
  obtain ⟨CH1, CH2, hC⟩ := chi_floor_all_principal
  refine ⟨CH1, CH2, fun q X t hq hX => ?_⟩
  rw [pretDistSq_lam_chi_twist (1 : DirichletCharacter ℂ q) t X]
  exact hC q X t hq hX

/-- **F3 — the ROUTE-A χ-quality floor, WHOLE for a general character.**  With
`k = 2·orderOf χ`, there are constants `CH1`, `CH2` such that for every `q`, `χ mod q`,
`X ≥ e`, every real `t` and every `B`, GIVEN the L-lower bound

  `|k·t| < 1  →  −B ≤ log‖L(1 + 1/log X − it, χ)‖`

(demanded ONLY on the bounded band — the extreme band needs nothing), one has

  `min( loglog X − B − CH2,`
  `     [loglog X − (3/4)loglog(|kt|+3) − 5·logloglog(|kt|+16) − CH1 − ∑_{p|q,p≤X}1/p]/k² )`
  `  ≤ 𝔻(λ·χ̄, n^{it}; X)²`.

This is the (c)-verdict's general half: ROUTE A's frequency geometry is CLOSED (H1 ∪ H2
covers ℝ with no gap), and the single remaining analytic debt is named in-statement.  The
hypothesis is exactly what a future (a)-grade stone — a `‖L(σ+it,χ)‖` lower bound near the
1-line, derived from the landed `Salt.SW.zero_free_region_all'` plus the Siegel branch
(`Salt.SW.siegel_L_one_exceptional`) — must deliver; its ineffective constant lands in `B`
and nowhere else. -/
theorem chi_floor_all_of_Llower :
    ∃ CH1 CH2 : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X t B : ℝ),
      Real.exp 1 ≤ X →
      (|((2 * orderOf χ : ℕ) : ℝ) * t| < 1 →
        -B ≤ Real.log ‖DirichletCharacter.LFunction χ
              (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖) →
        min (Real.log (Real.log X) - B - CH2)
            ((Real.log (Real.log X)
                - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
          ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨CH1, hCH1⟩ := chi_floor_orderOf
  obtain ⟨CH2, hCH2⟩ := chi_floor_low_of_Llower
  refine ⟨CH1, CH2, ?_⟩
  intro q _ χ X t B hX hL
  by_cases hbig : 1 ≤ |((2 * orderOf χ : ℕ) : ℝ) * t|
  · exact le_trans (min_le_right _ _) (hCH1 q χ X t (NeZero.ne q) hX hbig)
  · exact le_trans (min_le_left _ _) (hCH2 q χ X t B hX (hL (not_le.mp hbig)))

/-- **F3 (MRT shape) — the general-χ all-`t` floor on `𝔻(λ, χ·n^{it}; X)²`.**  The
`chi_floor_all_of_Llower` statement moved to the `g`-side twist by
`pretDistSq_lam_chi_twist`; this is the shape `M(λ; X, W) = inf_{χ,t} 𝔻(λ, χ n^{it}; X)²`
consumes directly. -/
theorem chi_floor_all_of_Llower_twisted :
    ∃ CH1 CH2 : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X t B : ℝ),
      Real.exp 1 ≤ X →
      (|((2 * orderOf χ : ℕ) : ℝ) * t| < 1 →
        -B ≤ Real.log ‖DirichletCharacter.LFunction χ
              (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖) →
        min (Real.log (Real.log X) - B - CH2)
            ((Real.log (Real.log X)
                - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
          ≤ pretDistSq lam (fun n => χ (n : ZMod q) * costwist t n) X := by
  obtain ⟨CH1, CH2, hC⟩ := chi_floor_all_of_Llower
  refine ⟨CH1, CH2, ?_⟩
  intro q _ χ X t B hX hL
  rw [pretDistSq_lam_chi_twist χ t X]
  exact hC q χ X t B hX hL

end Salt.MR
