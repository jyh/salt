/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Dist
import Salt.MR.ZetaLowerAllT

/-!
# MR-gate wave, stone S5 — the λ-non-pretentiousness (RANGE/QUALITY split)

Rung card (MR freeze, S5 NONPRET-SPLIT — THE A-ARM CARRIER): the λ-instantiation
of Tao's non-pretentiousness hypothesis (1.6), in the range/quality SPLIT form
grounded at `chowla.txt:210-218` (heights `|t| ≤ Q·x`, χ periods `≤ Q`).  For the
pure `χ = 1` (Liouville) case consumed by the ζ-only region:

  `∀ Q ≥ 1, ∃ x₀ C, ∀ x ≥ x₀, |t| ≤ Q·x:
     (1/4)·loglog x − 4·logloglog(|t|+16) − C ≤ 𝔻(λ, n^{it}; x)²`.

## The honest coefficient + o(1) shape (RECORDED — see flags MR-W3)

The freeze's one-line compression writes `(1/4)·loglog x − C(Q)` with `C(Q)`
constant.  The provable form carries the **`− 4·logloglog(|t|+16)`** correction:
the region bound `zeta_lower_all_t` has the load-bearing `(loglog)⁴` denominator
factor (3 region + 1 cut, confirmed MR-W2 flags), so `log‖ζ‖ ≥ … − 4·logloglog`.
This matches the prompt's own STONE (2) shape (`… − C·(logloglog x)-grade`) and
the downstream S10b pricing (`(1/4)log Hhi beats ~26 loglog Hhi + opaque const`).
The coefficient is **exactly 1/4**; only the additive correction is o(loglog x).

## Structure

* `lam`, `costwist` — the Liouville-on-primes value (`f(p) = −1`) and the `n^{it}`
  twist (`(costwist t p).re = cos(t·log p)`), so via `pretDistSq_liouville_split`
  `𝔻(λ, costwist t; x)² = ∑_{p≤x}(1 + cos(t·log p))/p`.
* `loglog_height_le` — the height absorption: for `|t| ≤ Q·x` and `x ≥ e`,
  `loglog(|t|+3) ≤ loglog x + log(1 + log(Q+3))` (a genuine `Q`-constant).
* `lambda_nonpret_of_bridge` — **THE CASH-OUT** (load-bearing): given the
  Euler bridge `𝔻² ≥ loglog x + log‖ζ(1+1/logx+it)‖ − K` as a named hypothesis,
  compose with `zeta_lower_all_t` + the height absorption to land the S5 SPLIT
  bound.  The bridge is the single residual (see flags MR-W3 / MR-W1 S1).
-/

namespace Salt.MR

open scoped BigOperators

/-- The Liouville value on primes as a complex-valued function (`λ(p) = −1`). -/
noncomputable def lam : ℕ → ℂ := fun _ => -1

/-- The `n^{it}` twist `costwist t n = e^{i·t·log n}`, so its real part on a prime
`p` is `cos(t·log p)` — the classical shape of the λ-non-pretentiousness sum. -/
noncomputable def costwist (t : ℝ) : ℕ → ℂ :=
  fun n => Complex.exp (((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)

/-- The real part of the twist on any argument is the cosine of the phase. -/
theorem costwist_re (t : ℝ) (n : ℕ) :
    (costwist t n).re = Real.cos (t * Real.log (n : ℝ)) := by
  unfold costwist
  exact Complex.exp_ofReal_mul_I_re _

/-- **The height absorption (the range side of the SPLIT).**  For `|t| ≤ Q·x`,
`Q ≥ 1`, `x ≥ e`: `loglog(|t|+3) ≤ loglog x + log(1 + log(Q+3))`.  The additive
term is a genuine constant depending only on `Q`; this is what keeps the leading
coefficient at exactly `1/4` after the `−(3/4)loglog(|t|+3)` from `log‖ζ‖`. -/
theorem loglog_height_le {Q : ℝ} (hQ : 1 ≤ Q) {x t : ℝ}
    (hx : Real.exp 1 ≤ x) (ht : |t| ≤ Q * x) :
    Real.log (Real.log (|t| + 3))
      ≤ Real.log (Real.log x) + Real.log (1 + Real.log (Q + 3)) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hQ3pos : (0 : ℝ) < Q + 3 := by linarith
  have htnn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have htp3 : (0 : ℝ) < |t| + 3 := by linarith
  -- `|t| + 3 ≤ (Q+3)·x`
  have hle1 : |t| + 3 ≤ (Q + 3) * x := by nlinarith [ht, hx1, hQ]
  -- `log(|t|+3) ≤ log(Q+3) + log x`
  have hlogmul : Real.log ((Q + 3) * x) = Real.log (Q + 3) + Real.log x :=
    Real.log_mul (ne_of_gt hQ3pos) (ne_of_gt hxpos)
  have hlog1 : Real.log (|t| + 3) ≤ Real.log (Q + 3) + Real.log x := by
    rw [← hlogmul]; exact Real.log_le_log htp3 hle1
  -- `log x ≥ 1`, `log(Q+3) ≥ 0`, `log(|t|+3) > 0`
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hlogQ3nn : (0 : ℝ) ≤ Real.log (Q + 3) := Real.log_nonneg (by linarith)
  have hloglt : (0 : ℝ) < Real.log (|t| + 3) := Real.log_pos (by linarith)
  -- `loglog(|t|+3) ≤ log(log(Q+3) + log x)`
  have h2 : Real.log (Real.log (|t| + 3))
      ≤ Real.log (Real.log (Q + 3) + Real.log x) :=
    Real.log_le_log hloglt hlog1
  -- `log(Q+3) + log x ≤ log x·(1 + log(Q+3))` (since `log(Q+3)·(log x − 1) ≥ 0`)
  have hstep : Real.log (Q + 3) + Real.log x
      ≤ Real.log x * (1 + Real.log (Q + 3)) := by
    nlinarith [mul_nonneg hlogQ3nn (by linarith : (0 : ℝ) ≤ Real.log x - 1)]
  have hargpos : (0 : ℝ) < Real.log (Q + 3) + Real.log x := by linarith
  have h3 : Real.log (Real.log (Q + 3) + Real.log x)
      ≤ Real.log (Real.log x * (1 + Real.log (Q + 3))) :=
    Real.log_le_log hargpos hstep
  have h4 : Real.log (Real.log x * (1 + Real.log (Q + 3)))
      = Real.log (Real.log x) + Real.log (1 + Real.log (Q + 3)) :=
    Real.log_mul (ne_of_gt hLpos) (by positivity)
  linarith [h2, h3, h4]

/-- **S5 — the CASH-OUT (`lambda_nonpret_of_bridge`).**  Given the λ-Euler bridge
`𝔻(λ, n^{it}; x)² ≥ loglog x + log‖ζ(1+1/logx+it)‖ − K` (the single residual
stone — see flags), compose with the all-`t` region bound `zeta_lower_all_t` and
the height absorption to land the S5 range/quality SPLIT bound: for every `Q ≥ 1`
there are `x₀, C` with, for all `x ≥ x₀` and `|t| ≤ Q·x`,

  `(1/4)·loglog x − 4·logloglog(|t|+16) − C ≤ 𝔻(λ, n^{it}; x)²`.

Heights `|t| ≤ Q·x` GROUNDED (chowla.txt:212-218).  Coefficient EXACTLY `1/4`;
the `−4·logloglog(|t|+16)` correction is the honest o(loglog x) shape (RECORDED). -/
theorem lambda_nonpret_of_bridge {K : ℝ}
    (hbridge : ∀ x t : ℝ, Real.exp 1 ≤ x →
      Real.log (Real.log x)
          + Real.log ‖riemannZeta ((1 + 1 / Real.log x : ℝ) + (t : ℝ) * Complex.I)‖
          - K
        ≤ pretDistSq lam (costwist t) x) :
    ∀ Q : ℝ, 1 ≤ Q → ∃ x0 C : ℝ, ∀ x t : ℝ, x0 ≤ x → |t| ≤ Q * x →
      (1 / 4) * Real.log (Real.log x)
          - 4 * Real.log (Real.log (Real.log (|t| + 16))) - C
        ≤ pretDistSq lam (costwist t) x := by
  obtain ⟨c'', hc'', hz⟩ := zeta_lower_all_t
  intro Q hQ
  refine ⟨Real.exp 1,
    (3 / 4) * Real.log (1 + Real.log (Q + 3)) - Real.log c'' + K, ?_⟩
  intro x t hx ht
  -- scale setup: `d' = 1/log x ∈ (0,1]`, so the pole point is excluded
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hd'0 : (0 : ℝ) ≤ 1 / Real.log x := by positivity
  have hd'1 : 1 / Real.log x ≤ 1 := (div_le_one hLpos).mpr hlogx1
  have hd'ne : ¬((1 / Real.log x : ℝ) = 0 ∧ t = 0) := by
    rintro ⟨h0, _⟩; exact (one_div_ne_zero (ne_of_gt hLpos)) h0
  -- the region lower bound at `d' = 1/log x`
  have hzb := hz (1 / Real.log x) t hd'0 hd'1 hd'ne
  -- denominator factor positivity
  have hApos : (0 : ℝ) < Real.log (|t| + 3) :=
    Real.log_pos (by have := abs_nonneg t; linarith)
  have hBinner : (1 : ℝ) < Real.log (|t| + 16) := by
    have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by have := abs_nonneg t; linarith)
  have hBpos : (0 : ℝ) < Real.log (Real.log (|t| + 16)) := Real.log_pos hBinner
  have hpowApos : (0 : ℝ) < Real.log (|t| + 3) ^ ((3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos hApos _
  have hpowBpos : (0 : ℝ) < Real.log (Real.log (|t| + 16)) ^ (4 : ℕ) :=
    pow_pos hBpos 4
  have hDpos : (0 : ℝ) < Real.log (|t| + 3) ^ ((3 : ℝ) / 4)
      * Real.log (Real.log (|t| + 16)) ^ (4 : ℕ) := mul_pos hpowApos hpowBpos
  -- take logs of the region bound
  have hquotpos : (0 : ℝ) < c'' / (Real.log (|t| + 3) ^ ((3 : ℝ) / 4)
      * Real.log (Real.log (|t| + 16)) ^ (4 : ℕ)) := div_pos hc'' hDpos
  have hlogzeta0 : Real.log (c'' / (Real.log (|t| + 3) ^ ((3 : ℝ) / 4)
        * Real.log (Real.log (|t| + 16)) ^ (4 : ℕ)))
      ≤ Real.log ‖riemannZeta ((1 + 1 / Real.log x : ℝ) + (t : ℝ) * Complex.I)‖ :=
    Real.log_le_log hquotpos hzb
  -- unfold the log of the quotient
  have hlogunfold : Real.log (c'' / (Real.log (|t| + 3) ^ ((3 : ℝ) / 4)
        * Real.log (Real.log (|t| + 16)) ^ (4 : ℕ)))
      = Real.log c'' - ((3 / 4) * Real.log (Real.log (|t| + 3))
          + 4 * Real.log (Real.log (Real.log (|t| + 16)))) := by
    rw [Real.log_div (ne_of_gt hc'') (ne_of_gt hDpos),
        Real.log_mul (ne_of_gt hpowApos) (ne_of_gt hpowBpos),
        Real.log_rpow hApos, Real.log_pow]
    push_cast
    ring
  rw [hlogunfold] at hlogzeta0
  -- the bridge and the height absorption
  have hbr := hbridge x t hx
  have hh := loglog_height_le hQ hx ht
  linarith [hbr, hlogzeta0, hh]

/-- **Bridge down-payment — the full-sum side (`log_norm_zeta_eq_re_tsum`).**  For
`Re s > 1`, `log‖ζ(s)‖ = ∑'_p Re(−log(1 − p^{−s}))`: the real part of the
log-Euler product, from mathlib's `riemannZeta_eulerProduct_exp_log`
(`exp(∑'_p −log(1−p^{−s})) = ζ(s)`) via `‖exp z‖ = exp(Re z)` and `Re ∘ ∑' = ∑' ∘ Re`.

This is the FULL prime-sum side of the λ-Euler bridge, holding at any `s = σ + it`
with `σ > 1` (in particular `σ = 1 + 1/log x`).  It reduces the bridge's residual
(see flags MR-W3) to the single missing piece: comparing `∑'_p Re(−log(1−p^{−s}))`
(= `∑'_p cos(t·log p)·p^{−σ} + O(1)` after the Mercator `k≥2` peel) against the
TRUNCATED sum `∑_{p≤x} cos(t·log p)/p` — the `σ = 1` prime partial→full and
`σ`-shift estimates, which need prime-density / prime-Abel-summation inputs that
are an explicitly flagged open corpus gap (EulerLink R5-FINISH; MR-W1 S1). -/
theorem log_norm_zeta_eq_re_tsum {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖riemannZeta s‖
      = ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-s))).re := by
  have hb : ∀ p : Nat.Primes, ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ ((-s).re) := by
    intro p
    rw [Complex.norm_natCast_cpow_of_re_ne_zero _
      (Complex.re_neg_ne_zero_of_one_lt_re hs)]
  have hfs : Summable (fun p : Nat.Primes => (p : ℂ) ^ (-s)) :=
    ((Nat.Primes.summable_rpow.mpr (by rw [Complex.neg_re]; linarith)).of_nonneg_of_le
      (fun _ => norm_nonneg _) hb).of_norm
  have hsum : Summable (fun p : Nat.Primes => -Complex.log (1 - (p : ℂ) ^ (-s))) :=
    hfs.clog_one_sub.neg
  have hzeta : riemannZeta s
      = Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))) :=
    (riemannZeta_eulerProduct_exp_log hs).symm
  rw [hzeta, Complex.norm_exp, Real.log_exp]
  exact Complex.re_tsum hsum

end Salt.MR
