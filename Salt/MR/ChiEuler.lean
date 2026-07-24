/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ChiFloor
import Salt.MR.PrimeTail
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# ROUTE A leg H2 — the χ-Euler bridge (`ChiEuler`)

The character analogue of the LANDED `euler_osc_bridge_unconditional`
(`Salt/MR/PrimeTail.lean:410`): for every Dirichlet character `χ mod q` and every real `t`,
the truncated χ-twisted oscillation sum agrees with `log‖L(1+1/log x − it, χ)‖` up to a
constant that is UNIFORM in `q`, `χ`, `x` and `t`.

Design source: `docs/exploration/chi-check-0724.md` (the ROUTE A finding + the EULER-SCOPE
correction block): the q = 1 λ-Euler bridge closed 2026-07-19, and the χ-twisted bridge is
a [B]-grade clone because (i) mathlib holds the χ log-Euler form
(`DirichletCharacter.LSeries_eulerProduct_exp_log`), (ii) the `σ`-shift head, the `p > x`
tail and the `k ≥ 2` Mercator peel are all χ-FREE, and (iii) the landed
`euler_osc_truncation` (`PrimeSigmaShift.lean:242`) is already stated for an ARBITRARY
1-bounded `g : ℕ → ℂ`, so the χ-twist is an *instance*, not a new estimate.

## Contents

* `chiTwist` — the `g`-side datum `n ↦ χ(n)·n^{it}` (1-bounded; it VANISHES at `p | q`,
  which costs nothing: every stone below is stated for arbitrary 1-bounded data).
* `log_norm_L_eq_re_tsum` (E1) — the χ down-payment: for `Re s > 1`,
  `log‖L(s,χ)‖ = ∑'_p Re(−log(1 − χ(p)p^{−s}))`, on the corpus's L-object
  `DirichletCharacter.LFunction` (bridged to the naive `LSeries` by `LFunction_eq_LSeries`,
  which is what the SW zero-theory chain — `zero_free_region_all'` — quantifies over).
* `peel_term_bound_gen`, `chi_peel_term_bound`, `chi_peel_sum_bound` (E2) — the Mercator
  `k ≥ 2` peel at `z = χ(p)·p^{−s}`.  The per-prime stone is stated for an arbitrary `z`
  with `‖z‖ ≤ 1/p`, so the χ-case is the trivial instance `‖χ(p)‖ ≤ 1` (including the
  `p | q` case `χ(p) = 0`, where both sides are `0`).  The constant is the χ-free `cpeel`.
* `chi_euler_osc_bridge` / `chi_euler_osc_bridge_unconditional` (E3) — THE EXIT.
* `pretDistSq_lamChi_split`, `chi_dist_bridge` (E4) — the floor-side composition à la
  `NonPretClose.lean`: `𝔻(λ·χ̄, n^{it}; X)² ≥ loglog X + log‖L(1+1/log X − it, χ)‖ − K`.

## The sign page (E4 — pinned, not guessed)

`lamChi χ p = λ(p)·conj χ(p) = −conj χ(p)` and `conj(costwist t p) = conj(p^{it})`, so

  `lamChi χ p · conj(costwist t p) = −conj(χ(p)·p^{it})`,

whence the per-prime term of `𝔻(λ·χ̄, n^{it}; X)²` is `(1 + Re(χ(p)·p^{it}))/p` — the
twist enters UNCONJUGATED and with `+t`.  Matching that against the Euler side
`Re(χ(p)·p^{−s}) = p^{−σ}·Re(χ(p)·p^{it})` forces `s = σ − it`.  Hence every statement
below carries `L(1 + 1/log x − it, χ)` — NOT `+it`, and NOT `χ̄`.  (The two alternatives
are equal in modulus, `‖L(s̄,χ̄)‖ = ‖L(s,χ)‖`, but the form below is the one that composes
with `ChiFloor.lean`'s `lamChi` datum with zero further bookkeeping.)

## Uniformity verdict

`K = cpeel + (Ctail + (1 + (log 4 + 4)))` — `cpeel = ∑'_p 1/p²` (χ-free), `Ctail` from the
χ-free `prime_tail_shift`, and the `σ`-shift constant from the χ-free Mertens-1 upper.
NO `q`-dependence enters anywhere: the character is only ever used through
`‖χ(a)‖ ≤ 1`.  The `p | q` primes are not excluded and cost nothing here (they are handled
downstream by `ChiFloor.primeDivSum`, and only on the `χ₀ → 1` leg).
-/

namespace Salt.MR

open scoped BigOperators

/-! ## The χ-twisted datum -/

/-- **The χ-twisted unimodular datum** `n ↦ χ(n)·n^{it}` — the `g`-side of the χ-Euler
bridge.  Note it is `0` (not unimodular) at `p | q`; every stone in this file is stated for
1-bounded data, so that costs nothing. -/
noncomputable def chiTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℕ → ℂ :=
  fun n => χ (n : ZMod q) * costwist t n

@[simp] theorem chiTwist_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    chiTwist χ t n = χ (n : ZMod q) * costwist t n := rfl

/-- The χ-twist is 1-bounded (`DirichletCharacter.norm_le_one` × `costwist_norm`). -/
theorem chiTwist_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    ‖chiTwist χ t n‖ ≤ 1 := by
  rw [chiTwist_apply, norm_mul, costwist_norm, mul_one]
  exact DirichletCharacter.norm_le_one χ _

/-! ## E1 — the χ down-payment (`log_norm_L_eq_re_tsum`) -/

/-- Summability of the χ-twisted Dirichlet summand over the primes, for `Re s > 1`. -/
theorem summable_chi_cpow {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)) := by
  have hb : ∀ p : Nat.Primes, ‖χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ ((-s).re) := by
    intro p
    rw [norm_mul, Complex.norm_natCast_cpow_of_re_ne_zero _
      (Complex.re_neg_ne_zero_of_one_lt_re hs)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (DirichletCharacter.norm_le_one χ _)
  exact ((Nat.Primes.summable_rpow.mpr (by rw [Complex.neg_re]; linarith)).of_nonneg_of_le
    (fun _ => norm_nonneg _) hb).of_norm

/-- **E1 — the χ bridge down-payment (`log_norm_L_eq_re_tsum`).**  For `Re s > 1`,
`log‖L(s,χ)‖ = ∑'_p Re(−log(1 − χ(p)·p^{−s}))`: the real part of the χ log-Euler product.

Byte-parallel to the q = 1 `log_norm_zeta_eq_re_tsum` (`NonPret.lean:189`), on mathlib's
`DirichletCharacter.LSeries_eulerProduct_exp_log` via `‖exp z‖ = exp(Re z)` and
`Re ∘ ∑' = ∑' ∘ Re`.  Stated on the corpus's L-object `DirichletCharacter.LFunction` (the
one `Salt.SW.zero_free_region_all'` quantifies over), through `LFunction_eq_LSeries`. -/
theorem log_norm_L_eq_re_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    Real.log ‖DirichletCharacter.LFunction χ s‖
      = ∑' p : Nat.Primes, (-Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))).re := by
  have hsum : Summable
      (fun p : Nat.Primes => -Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))) :=
    (summable_chi_cpow χ hs).clog_one_sub.neg
  have hL : DirichletCharacter.LFunction χ s
      = Complex.exp
          (∑' p : Nat.Primes, -Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact (DirichletCharacter.LSeries_eulerProduct_exp_log χ hs).symm
  rw [hL, Complex.norm_exp, Real.log_exp]
  exact Complex.re_tsum hsum

/-! ## E2 — the Mercator `k ≥ 2` peel, χ-twisted -/

/-- **The per-prime Euler `k ≥ 2` peel, at arbitrary `z`.**  For `p ≥ 2` and `‖z‖ ≤ 1/p`,
`|Re(−log(1−z)) − Re z| ≤ 1/p²`.  This is `peel_term_bound`
(`PrimeSigmaShift.lean:300`) with the base point freed: the landed version fixes
`z = p^{−s}`, and the χ-twisted case needs `z = χ(p)·p^{−s}`.  Same mathlib Taylor
remainder `Complex.norm_log_one_sub_inv_sub_self_le`. -/
theorem peel_term_bound_gen {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : ‖z‖ ≤ 1 / (p : ℝ)) :
    |(-Complex.log (1 - z)).re - z.re| ≤ 1 / (p : ℝ) ^ 2 := by
  have hpge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hnn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  have hhalf : ‖z‖ ≤ 1 / 2 := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpge2
    linarith
  have hnlt1 : ‖z‖ < 1 := by linarith
  have hslit : (1 - z) ∈ Complex.slitPlane := by
    have h := Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by rwa [norm_neg])
    simpa [sub_eq_add_neg] using h
  have hlogeq : -Complex.log (1 - z) = Complex.log (1 - z)⁻¹ :=
    (Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit)).symm
  have hbnd := Complex.norm_log_one_sub_inv_sub_self_le hnlt1
  have hre : (-Complex.log (1 - z)).re - z.re = ((-Complex.log (1 - z)) - z).re := by
    rw [Complex.sub_re]
  rw [hre]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [hlogeq]
  refine le_trans hbnd ?_
  have hden : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hsq : ‖z‖ ^ 2 ≤ (1 / (p : ℝ)) ^ 2 := pow_le_pow_left₀ hnn hz 2
  have hkey : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 := by
    have hz2 : (0 : ℝ) ≤ ‖z‖ ^ 2 := by positivity
    nlinarith [hden, hz2]
  have hfin : (1 / (p : ℝ)) ^ 2 = 1 / (p : ℝ) ^ 2 := by rw [div_pow, one_pow]
  linarith [hkey, hsq, hfin.le, hfin.ge]

/-- **E2 (per-prime) — the χ-twisted Euler `k ≥ 2` peel.**  For prime `p ≥ 2` and
`1 ≤ Re s`, `|Re(−log(1 − χ(p)p^{−s})) − Re(χ(p)p^{−s})| ≤ 1/p²`.  The only χ-input is
`‖χ(p)‖ ≤ 1`; at `p | q` the character vanishes and both sides are `0`. -/
theorem chi_peel_term_bound {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : 2 ≤ p) {s : ℂ}
    (hs : 1 ≤ s.re) :
    |(-Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))).re
        - (χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)).re| ≤ 1 / (p : ℝ) ^ 2 := by
  refine peel_term_bound_gen hp ?_
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hsre0 : (-s).re ≠ 0 := by rw [Complex.neg_re]; intro h; linarith
  rw [norm_mul, Complex.norm_natCast_cpow_of_re_ne_zero _ hsre0, Complex.neg_re]
  calc ‖χ ((p : ℕ) : ZMod q)‖ * (p : ℝ) ^ (-s.re)
      ≤ 1 * (p : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (p : ℝ) ^ (-s.re) := one_mul _
    _ ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]

/-- **E2 (summed) — the χ-twisted Euler `k ≥ 2` peel.**  For `1 < Re s`,
`|∑'_p Re(−log(1 − χ(p)p^{−s})) − ∑'_p Re(χ(p)p^{−s})| ≤ cpeel` with the SAME χ-free
constant `cpeel = ∑'_p 1/p²` as the q = 1 `peel_sum_bound`. -/
theorem chi_peel_sum_bound {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    |(∑' p : Nat.Primes, (-Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))).re)
        - ∑' p : Nat.Primes, (χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)).re| ≤ cpeel := by
  have hfs := summable_chi_cpow χ hs
  have hsum : Summable
      (fun p : Nat.Primes => -Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))) :=
    hfs.clog_one_sub.neg
  have hA : Summable
      (fun p : Nat.Primes => (-Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))).re) := by
    simpa only [Complex.reCLM_apply] using Complex.reCLM.summable hsum
  have hB : Summable (fun p : Nat.Primes => (χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)).re) := by
    simpa only [Complex.reCLM_apply] using Complex.reCLM.summable hfs
  have hdiff := hA.sub hB
  rw [← Summable.tsum_sub hA hB]
  calc |∑' p : Nat.Primes, ((-Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))).re
            - (χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)).re)|
      = ‖∑' p : Nat.Primes, ((-Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))).re
            - (χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)).re)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' p : Nat.Primes, ‖(-Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))).re
            - (χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)).re‖ :=
        norm_tsum_le_tsum_norm
          (by simpa only [Real.norm_eq_abs] using summable_abs_iff.mpr hdiff)
    _ = ∑' p : Nat.Primes, |(-Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))).re
            - (χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)).re| := by simp only [Real.norm_eq_abs]
    _ ≤ ∑' p : Nat.Primes, 1 / (p : ℝ) ^ 2 :=
        (summable_abs_iff.mpr hdiff).tsum_le_tsum
          (fun p => chi_peel_term_bound χ p.2.two_le (le_of_lt hs)) cpeel_summable
    _ = cpeel := rfl

/-! ## E3 — the χ-Euler oscillation bridge (THE EXIT) -/

/-- **The `σ`-`it` split of the χ-twisted Euler summand.**  For a prime `p` and reals `σ, t`,
`Re(χ(p)·p^{−(σ−it)}) = p^{−σ}·Re(χ(p)·p^{it})`.  This is the χ-analogue of `cpow_neg_re`
(`PrimeSigmaShift.lean:341`); note the `−it` in the exponent, which is what makes the twist
appear UNCONJUGATED on the right (see the file header's sign page). -/
theorem chi_cpow_re {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : 0 < p) (σ t : ℝ) :
    (χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-((σ : ℂ) - (t : ℂ) * Complex.I))).re
      = (p : ℝ) ^ (-σ : ℝ) * (chiTwist χ t p).re := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := Complex.natCast_log.symm
  have hrp : (((p : ℝ) ^ (-σ : ℝ) : ℝ) : ℂ)
      = Complex.exp ((Real.log p * (-σ) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hppos, Complex.ofReal_exp]
  have hcpow : (p : ℂ) ^ (-((σ : ℂ) - (t : ℂ) * Complex.I))
      = (((p : ℝ) ^ (-σ : ℝ) : ℝ) : ℂ) * costwist t p := by
    unfold costwist
    rw [Complex.cpow_def_of_ne_zero hp0, hlog, hrp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hcpow, mul_left_comm, Complex.re_ofReal_mul]
  rfl

/-- **E3 — the two-sided χ-Euler-oscillation bridge (`chi_euler_osc_bridge`).**  Given the
(χ-free) R0.2 tail bound, there is a SINGLE constant `K` such that for every modulus `q`,
every Dirichlet character `χ mod q`, every `x ≥ e` and every real `t`,

  `|∑_{p≤x} Re(χ(p)·p^{it})/p − log‖L(1+1/log x − it, χ)‖| ≤ K`.

`K = cpeel + (Ctail + (1 + (log 4 + 4)))` is UNIFORM in `q`, `χ`, `x`, `t` — the character
enters only through `‖χ(a)‖ ≤ 1`, and every constant on the route (`cpeel = ∑'_p 1/p²`, the
`p > x` tail `Ctail`, the Mertens-1 `σ`-shift) is χ-free.

Assembled exactly as the q = 1 `euler_osc_bridge` (`PrimeSigmaShift.lean:414`): the χ
log-Euler product (`log_norm_L_eq_re_tsum`), the `k ≥ 2` peel (`chi_peel_sum_bound`), the
`σ`-`it` split (`chi_cpow_re`), and the LANDED general-`g` truncation
`euler_osc_truncation` at `g = chiTwist χ t`. -/
theorem chi_euler_osc_bridge (hPTS : PrimeTailShiftBounded) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x t : ℝ), Real.exp 1 ≤ x →
      |(∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (chiTwist χ t p).re / (p : ℝ))
          - Real.log ‖DirichletCharacter.LFunction χ
              (((1 + 1 / Real.log x : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖|
        ≤ K := by
  obtain ⟨Ctail, hCtail⟩ := hPTS
  refine ⟨cpeel + (Ctail + (1 + (Real.log 4 + 4))), ?_⟩
  intro q _ χ x t hx
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  set s : ℂ := ((1 + 1 / Real.log x : ℝ) : ℂ) - (t : ℝ) * Complex.I with hsdef
  have hsre : s.re = 1 + 1 / Real.log x := by
    rw [hsdef]; simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hs1 : 1 < s.re := by
    rw [hsre]
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hLid := log_norm_L_eq_re_tsum χ hs1
  have htsumeq : (∑' p : Nat.Primes, (χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)).re)
      = ∑' p : Nat.Primes, (chiTwist χ t p).re * (p : ℝ) ^ (-1 - 1 / Real.log x : ℝ) := by
    refine tsum_congr (fun p => ?_)
    rw [hsdef, chi_cpow_re χ p.2.pos (1 + 1 / Real.log x) t,
      show (-1 - 1 / Real.log x : ℝ) = -(1 + 1 / Real.log x) from by ring]
    ring
  have hR04 := euler_osc_truncation hx (hCtail x hx) (chiTwist χ t) (chiTwist_norm_le χ t)
  have hpeel := chi_peel_sum_bound χ hs1
  rw [hLid]
  calc |(∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (chiTwist χ t p).re / (p : ℝ))
          - ∑' p : Nat.Primes,
              (-Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))).re|
      ≤ |(∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (chiTwist χ t p).re / (p : ℝ))
            - ∑' p : Nat.Primes, (χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)).re|
          + |(∑' p : Nat.Primes, (χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s)).re)
              - ∑' p : Nat.Primes,
                  (-Complex.log (1 - χ ((p : ℕ) : ZMod q) * (p : ℂ) ^ (-s))).re| :=
        abs_sub_le _ _ _
    _ ≤ (Ctail + (1 + (Real.log 4 + 4))) + cpeel := by
        apply add_le_add
        · rw [htsumeq, abs_sub_comm]; exact hR04
        · rw [abs_sub_comm]; exact hpeel
    _ = cpeel + (Ctail + (1 + (Real.log 4 + 4))) := by ring

/-- **E3 (unconditional) — `chi_euler_osc_bridge_unconditional`.**  The R0.2 discharge
(`prime_tail_shift`, `PrimeTail.lean:357`, χ-free) makes the χ-Euler bridge unconditional.
This is ROUTE A's H2 leg: the exact χ-analogue of `euler_osc_bridge_unconditional`. -/
theorem chi_euler_osc_bridge_unconditional :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x t : ℝ), Real.exp 1 ≤ x →
      |(∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (chiTwist χ t p).re / (p : ℝ))
          - Real.log ‖DirichletCharacter.LFunction χ
              (((1 + 1 / Real.log x : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖|
        ≤ K :=
  chi_euler_osc_bridge prime_tail_shift

/-! ## E4 — the floor-side composition (`chi_dist_bridge`) -/

/-- **The `λ·χ̄` Liouville split.**  `𝔻(λ·χ̄, n^{it}; X)² = S(X) + ∑_{p≤X} Re(χ(p)·p^{it})/p`,
where `S(X) = ∑_{p≤X} 1/p` is the divergent Mertens part.

This is the E4 sign page, discharged: `lamChi χ p · conj(costwist t p)
= −conj(χ(p)·costwist t p)`, so the per-prime term `(1 − Re(·))/p` is exactly
`(1 + Re(χ(p)·p^{it}))/p` — the twist UNCONJUGATED, at `+t`.  (The χ-analogue of
`pretDistSq_liouville_split` specialised to the `λ·χ̄` datum of `ChiFloor.lean`.) -/
theorem pretDistSq_lamChi_split {q : ℕ} (χ : DirichletCharacter ℂ q) (t X : ℝ) :
    pretDistSq (lamChi χ) (costwist t) X
      = Salt.Mertens.SPartial X
        + ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
            (chiTwist χ t p).re / (p : ℝ) := by
  unfold pretDistSq Salt.Mertens.SPartial
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hmul : lamChi χ p * (starRingEnd ℂ) (costwist t p)
      = -((starRingEnd ℂ) (chiTwist χ t p)) := by
    simp only [lamChi, lam, chiTwist, map_mul]
    ring
  rw [hmul, Complex.neg_re, Complex.conj_re]
  ring

/-- **E4 — the H2 floor-side bridge (`chi_dist_bridge`).**  There is a constant `K`,
UNIFORM in `q`, `χ`, `X` and `t`, with

  `loglog X + log‖L(1+1/log X − it, χ)‖ − K ≤ 𝔻(λ·χ̄, n^{it}; X)²`   for `X ≥ e`.

The χ-analogue of the `NonPretClose.lean` glue: the `λ·χ̄` Liouville split
(`pretDistSq_lamChi_split`) plus the sharp real Mertens-2
(`S(X) ≥ loglog X + M − 12/log X`, and `12/log X ≤ 12` for `X ≥ e`) plus the `≥`-side of
the χ-Euler bridge.  `K = 12 + K₀ − M` with `K₀` the bridge constant and `M` the
Meissel–Mertens constant.  This is the input the H2 leg feeds to the zero-free-region
lower bound on `log‖L‖` (NOT proved here — that is the next stone). -/
theorem chi_dist_bridge :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X t : ℝ), Real.exp 1 ≤ X →
      Real.log (Real.log X)
          + Real.log ‖DirichletCharacter.LFunction χ
              (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ - K
        ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨K, hK⟩ := chi_euler_osc_bridge_unconditional
  refine ⟨12 + K - Salt.Mertens.mertensM, ?_⟩
  intro q _ χ X t hX
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hX2 : (2 : ℝ) ≤ X := le_trans h2e hX
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hmert := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hX2)
  have h12 : 12 / Real.log X ≤ 12 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hbr := abs_le.mp (hK q χ X t hX)
  rw [pretDistSq_lamChi_split χ t X]
  linarith [hmert.1, hbr.1, h12]

/-- **E4 (upper side) — `chi_dist_bridge_le`.**  The matching `≤` direction, uniform in the
same data: `𝔻(λ·χ̄, n^{it}; X)² ≤ loglog X + log‖L(1+1/log X − it, χ)‖ + K`.  Same route,
using the other side of the sharp Mertens-2 and of the χ-Euler bridge. -/
theorem chi_dist_bridge_le :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X t : ℝ), Real.exp 1 ≤ X →
      pretDistSq (lamChi χ) (costwist t) X
        ≤ Real.log (Real.log X)
            + Real.log ‖DirichletCharacter.LFunction χ
                (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ + K := by
  obtain ⟨K, hK⟩ := chi_euler_osc_bridge_unconditional
  refine ⟨12 + K + Salt.Mertens.mertensM, ?_⟩
  intro q _ χ X t hX
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hX2 : (2 : ℝ) ≤ X := le_trans h2e hX
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hmert := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hX2)
  have h12 : 12 / Real.log X ≤ 12 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hbr := abs_le.mp (hK q χ X t hX)
  rw [pretDistSq_lamChi_split χ t X]
  linarith [hmert.2, hbr.2, h12]

end Salt.MR


