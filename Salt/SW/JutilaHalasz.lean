/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.JutilaResidue
import Salt.SW.WellSpacedAt
import Salt.SW.GrahamHard3

/-!
# B2 W9a + W9c — Halász at the detector's system, the partial summation, the `S'`-form floor,
the two integrated kernel bounds and THE RATIO `J ≪ x^{2−2σ}`

Jutila 1977 §3 (pp.51–53) at a single primitive `χ` mod `q ≥ 2`, `ε = 1/120`, in the corpus's
Riesz-kernel form (design v2 §A.1–A.6). For a system `ρ_j = β_j + iγ_j` (`j < J`) of zeros of
`L(·, χ)` in the strip `σ ≤ β_j < 1`, `|γ_j| ≤ T`, with `Δ`-well-spaced ordinates
(`Δ = 1/log D`, `D = qT`):

* **W9a — the Halász instance.** The detector `g(ρ_j, χ)` of Lemma 6 is the Dirichlet polynomial
  `f(s_j, χ) = Σ_{n ∈ S} a'_n χ(n) n^{−s_j}` with `s_j := ρ_j − σ`, `S = (z₁, x]` and the χ-free
  coefficient `a'_n = a(n)·Σ'_r r⁻¹ψ_r(n)·K(n/x)·n^{−σ}` (`jutilaA`;
  `jutilaDetector_eq_dirichletPolyChi`). Lemma 7 (`halasz_weighted_tsum`, W8) with the weight
  `b_n = jutilaB q R N M n` (W9b — nonnegative for `1 ≤ M ≤ N`, `b_0 = 0`, positive on `S` where
  `a'_n ≠ 0` when `M ≤ z₁` and `2x ≤ N`) gives
  `(Σ_j ‖g(ρ_j)‖)² ≤ (Σ_{n∈S} ‖a'_n‖²/b_n)·Re Σ_{j,k} η̄_j η_k B(s̄_j + s_k)` with
  `B = halaszBTsum (jutilaB) χ χ` (`sq_sum_norm_jutilaDetector_le`). The first factor is
  `≤ 4·Σ_{n ≤ x} a(n)² n^{1−2σ}` (`K(n/N) ≥ 1/4` on `n ≤ x ≤ N/2` — the CRUDE bound `2x ≤ N`
  buys; `sum_normSq_jutilaA_div_jutilaB_le`), and the partial summation against S10-H
  (`sum_sq_sum_bvWeight_le_full`, `u ≥ z₂`) and S10-L (`_low`, `2 ≤ u ≤ z₂`) — every scale,
  Abel with `1/2 ≤ σ`, no `1/λ` loss — bounds that by
  `C_ps·(log z₂/log²(z₂/z₁))·((1 + log x)x^{2−2σ} + log z₂)` (`sum_sq_sum_bvWeight_mul_rpow_le`).
* **W9c — the floor and the ratio.** The floor in the `S'`-FORM, `S' := Σ'_r r⁻¹` UNWEAKENED
  (`jutilaDetector_floor_sum` — the landed `_floor_at_zero`'s own intermediate, with Lemma 5 NOT
  applied), so that `φ(q)/q` cancels against the residue block's `E(χ₀)·Σ'φ(r)/r² ≤ (φ/q)·S'`
  without any UPPER bound on the coprime harmonic sum; at F5's table the error is at most a third
  of `S'` (`f5_error_le_main` + `sum_sf_coprime_inv_ge`), so `‖g(ρ_j)‖ ≥ S'/2` at every zero of
  the system (`jutilaDetector_floor_half_sum`). The residue block (W9b's identity) integrated over
  the device's rectangle `Ξ × H` (`M = e^ξ`, `N = e^η`): the DIAGONAL `‖resKernel s N M‖ ≤
  1.0255·log(N/M)` for real `0 ≤ s ≤ 1/60` gives `∫_Ξ∫_H ≤ 1.0255·|Ξ||H|·(η₁ − ξ₀)`
  (`integral_norm_resKernel_diag_le`, `ξ₀ ≥ 0`); the OFF-DIAGONAL, `Im s ≠ 0`, integrates
  `e^{−sη}` and `e^{−sξ}` to `≤ 2/|s|` each, so `‖∫∫‖ ≤ 2.051·(|Ξ| + |H|)/(Im s)²`
  (`norm_integral_resKernel_offdiag_le`, `ξ₀, η₀ ≥ 0`); with the Schur sum of a `Δ`-spaced
  system (`sum_inv_sq_sub_le_of_wellSpacedAt`, W9d) the off-diagonal total per `j` is
  `≤ 2.051(|Ξ| + |H|)(π²/3)log²D`. Dividing `(J S'/2)² ≤ A·[J·(φ/q)S'·398.2 log D + J²·Ib₀]` by
  `J·S'` and reading `S' ≥ (6/π²)(φ/q)(log D)/10` ONCE gives, for `D ≥ D₁(C_ps)` where the
  `I`-block is below `S'²/8`, THE RATIO `J ≤ C·D^{13(1−σ)}` (`card_system_le_rpow`;
  `13 = 2c` at F5's `x = D^{13/2}`).

## The honest label

Every row is an INPUT to W9f's strip theorem (the count `≤ C₁(7/4 + 3λ/2)·2J` with W9e's boxes
gives `D_strip = 14`); `C` and `D₁` are NON-EFFECTIVE (S10's `∃ K` through `C_ps`; the design v2
§A.6 solves `D₁ = 10^59–10^64` at `C_ps = 1`) and live inside the `∃`; the threshold binder
`D₁ ≤ qT` is the route's — below it W9f's `zeroCountM_le` supplies the count. The floor rows and
the ratio row assume zeros with `β ≥ 119/120` and are VACUOUS at the object (no such zero is
known). The `1/60` of the kernel rows is FORCED by the pair sum `Re(s̄_j + s_k) = (β_j − σ) +
(β_k − σ) ≤ 2/120` and consumed with zero margin. Nothing here bears on twin primes or on the
crown's conditions.

## The measured receipts (design v2 §A, as corrected at the two passes; `h2c-desk/w9ac_sweep.py`)

The toy `(z₁, z₂, x) = (4, 16, 400)` with the real `bvWeight`: `Σ a(n)² n^{1−2σ} =
2.41 / 2.53 / 3.12 / 4.22` at `σ = 1, 0.99, 0.95, 0.9` against the row's RHS at
`C_ps = 2·max(4K_H, K_L)` with `K_H = 0.0832`, `K_L = 0.1460` measured from the two landed S10
shapes: `9.37 / 10.23 / 14.88 / 24.90` (ratios `0.26, 0.25, 0.21, 0.17`). The `/b` bound at the
toy with `(N, M) = (800, 4)`, `σ = 1`: `0.7704 ≤ 9.6326`; at `N = x/2` it is FALSE (`18.31`), so
`2x ≤ N` is truth-load-bearing there. The diagonal at `D = 10²⁰` (`|Ξ| = 1.151`, `|H| = 2.494`,
`η₁ − ξ₀ = 3.594 log D`): `470.1 ≤ 487.5` at `s = 0` (ratio `0.964`, essentially `D`-independent).
The off-diagonal against its bound at `Re s = 0` RISES with `log D` — `0.41` (`10²⁰`), `0.76`
(`10¹⁰⁰`), `0.97` (`10^{10000}`) — toward the envelope `1/C₀ = 0.975`, never violated
(`‖∫∫‖ ≤ 2C₀(|Ξ| + |H|)/|s|²` and `|s| ≥ |Im s|`); at `Re s = 1/60` the maximum is `0.025`.
`|K̃(−s)||s| ≤ 1.0255` on `Re s ≤ 1/60`, attained at `s = 1/60` real. The third at `10²⁰`:
`E/S'_lb = 0.103` measured (`E ≤ S'/3` is the chain's constant, `D`-uniform). The Schur lattice
`3.2799 / 3.2889` against `π²/3 = 3.2899`.

## The landed control (the partial summation's witness as PROVED, not as designed)

`sum_sq_sum_bvWeight_mul_rpow_le` landed with `C = 4·max(4K_H, K_L)` (see its docstring), so at
the toy the row's RHS at the landed witness is twice the receipt above: `18.74 / 20.45 / 29.75 /
49.80` at `σ = 1, 0.99, 0.95, 0.9` (ratios `0.13, 0.12, 0.10, 0.08`). The statement is `∃ C`; no
row that consumes it reads the numeral. `card_system_le_rpow` is FLAGGED in this wave
(`B2-W9ac-card_system_le_rpow`: the device step needs the residue block's integrability over the
rectangle, a row the corpus lacks) — its statement is unchanged and unrefuted, and it returns
with that row in the next cut; the ten inputs above are landed.
-/

open MeasureTheory Complex DirichletCharacter ArithmeticFunction

noncomputable section
namespace Salt.SW

variable {q : ℕ}

/-! ## (i) The Halász instance (W9a) -/

/-- The detector's χ-free coefficient at the strip's edge `σ`:
`a'_n = a(n)·(Σ'_r r⁻¹ψ_r(n))·K(n/x)·n^{−σ}`. -/
def jutilaA (q z₁ z₂ : ℕ) (R x σ : ℝ) (n : ℕ) : ℂ :=
  (((∑ d ∈ n.divisors, bvWeight z₁ z₂ d)
      * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n)
      * (max 0 (1 - (n : ℝ) / x)) ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-(σ : ℂ))

/-- The detector IS the Dirichlet polynomial of `jutilaA` at `s = ρ − σ`
(`n^{−σ}·n^{−(ρ−σ)} = n^{−ρ}` on `n ≥ 1`; `K(n/x)` is `kern2`'s value). -/
theorem jutilaDetector_eq_dirichletPolyChi (χ : DirichletCharacter ℂ q) (z₁ z₂ : ℕ) (R x σ : ℝ)
    (ρ : ℂ) :
    jutilaDetector χ z₁ z₂ R x ρ
      = Salt.MR.dirichletPolyChi (Finset.Ioc z₁ ⌊x⌋₊) (jutilaA q z₁ z₂ R x σ) χ (ρ - σ) := by
  simp only [jutilaDetector, Salt.MR.dirichletPolyChi, jutilaA, jutilaCoeff, kern2]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn1 : 1 ≤ n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (n : ℂ) ^ (-ρ) = (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(ρ - σ)) := by
    rw [← Complex.cpow_add _ _ hn0]
    congr 1
    ring
  rw [key]
  push_cast
  ring

/-- On the detector's range the weight is positive wherever the coefficient is: `n > z₁ ≥ M`
kills the `M`-term and `n ≤ x ≤ N/2 < N` keeps `K(n/N) > 0` (W9b's `jutilaB_pos`). -/
theorem jutilaB_pos_of_ne_zero {q z₁ z₂ : ℕ} {R x σ N M : ℝ} (hM : 1 ≤ M) (hMN : M ≤ N) {n : ℕ}
    (hn : n ∈ Finset.Ioc z₁ ⌊x⌋₊) (hz₁M : M ≤ z₁) (hxN : 2 * x ≤ N)
    (ha : jutilaA q z₁ z₂ R x σ n ≠ 0) : 0 < jutilaB q R N M n := by
  -- `hMN` is not consumed by `jutilaB_pos` (which takes no `M ≤ N`); it is kept as the row's
  -- shape and READ here (the sub-freeze's §A.8 rule for a route-only binder).
  have _h := hMN
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hn
  have hn1 : 1 ≤ n := by omega
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hMn : M ≤ (n : ℝ) := le_trans hz₁M (by exact_mod_cast hlo.le)
  have hfl : 1 ≤ ⌊x⌋₊ := le_trans hn1 hhi
  have hx1 : (1 : ℝ) ≤ x := Nat.floor_pos.mp hfl
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hhi) (Nat.floor_le hxpos.le)
  have hnN : (n : ℝ) < N := by linarith
  have hS : ∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n ≠ 0 := by
    intro h
    exact ha (by simp [jutilaA, h])
  exact jutilaB_pos hM0 q R hMn hnN hS

/-- The weighted series is summable — its support is finite (`b_n = 0` for `n ≥ N`,
W9b's `jutilaB_eq_zero_of_le`). -/
theorem summable_jutilaB_series {q : ℕ} {R N M : ℝ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) :
    Summable (fun n : ℕ =>
      (jutilaB q R N M n : ℂ) * (starRingEnd ℂ) (χ₁ n) * χ₂ n * (n : ℂ) ^ (-s)) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  refine summable_of_ne_finset_zero (s := Finset.range (⌈N⌉₊ + 1)) ?_
  intro n hn
  have hlt : ⌈N⌉₊ + 1 ≤ n := by
    by_contra hc
    exact hn (Finset.mem_range.mpr (by omega))
  have hnN : N ≤ (n : ℝ) := by
    have h2 : N ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil N
    have h3 : ((⌈N⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : ⌈N⌉₊ ≤ n)
    linarith
  rw [jutilaB_eq_zero_of_le hM0 hMN q R hnN]
  simp

/-- The `Σ ‖a'_n‖²/b_n` factor: `≤ 4·Σ_{n ≤ x} a(n)² n^{1−2σ}` when `2x ≤ N` — the CRUDE bound
`K(n/N) ≥ 1/4` on `n ≤ x` is what `2x ≤ N` buys (not positivity: at `N = x` the detector's
own `K(n/x)` vanishes with `K(n/N)`); the `Σ'(n)²K(n/x)²` cancels against `b_n`'s `Σ'(n)²K(n/N)`
termwise (`0/0 = 0` where `Σ'(n) = 0`). -/
theorem sum_normSq_jutilaA_div_jutilaB_le {q z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) {R x σ N M : ℝ}
    (hx : 1 ≤ x) (hM : 1 ≤ M) (hMN : M ≤ N) (hz₁M : M ≤ z₁) (hxN : 2 * x ≤ N) (hσ : 0 ≤ σ) :
    ∑ n ∈ Finset.Ioc z₁ ⌊x⌋₊, ‖jutilaA q z₁ z₂ R x σ n‖ ^ 2 / jutilaB q R N M n
      ≤ 4 * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2 * (n : ℝ) ^ (1 - 2 * σ) := by
  -- `hz₁` and `hσ` are the row's shape, consumed by neither branch of the termwise bound;
  -- kept and READ (the sub-freeze's §A.8 rule for a route-only binder).
  have _h := hz₁
  have _hσ := hσ
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 hMN
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hterm : ∀ n ∈ Finset.Ioc z₁ ⌊x⌋₊,
      ‖jutilaA q z₁ z₂ R x σ n‖ ^ 2 / jutilaB q R N M n
        ≤ 4 * ((∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2 * (n : ℝ) ^ (1 - 2 * σ)) := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hn
    have hn1 : 1 ≤ n := by omega
    have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hMn : M ≤ (n : ℝ) := le_trans hz₁M (by exact_mod_cast hlo.le)
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hhi) (Nat.floor_le hxpos.le)
    have hKN : (1 : ℝ) / 4 ≤ (max 0 (1 - (n : ℝ) / N)) ^ 2 := by
      have hle : (n : ℝ) / N ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hN0 (by norm_num)]
        linarith
      have h1 : (1 : ℝ) / 2 ≤ max 0 (1 - (n : ℝ) / N) :=
        le_trans (by linarith) (le_max_right _ _)
      nlinarith
    have hKx : (max 0 (1 - (n : ℝ) / x)) ^ 2 ≤ 1 := by
      have hd : (0 : ℝ) ≤ (n : ℝ) / x := by positivity
      have h1 : max 0 (1 - (n : ℝ) / x) ≤ 1 := max_le (by norm_num) (by linarith)
      have h0 : (0 : ℝ) ≤ max 0 (1 - (n : ℝ) / x) := le_max_left _ _
      nlinarith
    have hbn : jutilaB q R N M n
        = (n : ℝ)⁻¹ * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n) ^ 2
            * (max 0 (1 - (n : ℝ) / N)) ^ 2 := jutilaB_eq_of_le hM0 q R hMn
    have hrhs0 : (0 : ℝ) ≤ 4 * ((∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2 * (n : ℝ) ^ (1 - 2 * σ)) :=
      by positivity
    by_cases hS : (∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n) = 0
    · have ha0 : jutilaA q z₁ z₂ R x σ n = 0 := by simp [jutilaA, hS]
      rw [ha0, norm_zero, zero_pow (by norm_num), zero_div]
      exact hrhs0
    · have hbpos : 0 < jutilaB q R N M n := jutilaB_pos hM0 q R hMn (by linarith) hS
      have hcast : ‖(n : ℂ) ^ (-(σ : ℂ))‖ = (n : ℝ) ^ (-σ) := by
        rw [Complex.norm_natCast_cpow_of_pos hn1]
        norm_num
      have hnorm : ‖jutilaA q z₁ z₂ R x σ n‖
          = |(∑ d ∈ n.divisors, bvWeight z₁ z₂ d)
                * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n)
                * (max 0 (1 - (n : ℝ) / x)) ^ 2| * (n : ℝ) ^ (-σ) := by
        rw [jutilaA, norm_mul, Complex.norm_real, Real.norm_eq_abs, hcast]
      have hsq2 : ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hn0R.le]
        congr 1
        push_cast
        ring
      have hnormsq : ‖jutilaA q z₁ z₂ R x σ n‖ ^ 2
          = ((∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2
              * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n) ^ 2
              * (n : ℝ) ^ (-(2 * σ))) * ((max 0 (1 - (n : ℝ) / x)) ^ 2) ^ 2 := by
        rw [hnorm, mul_pow, sq_abs, ← hsq2]
        ring
      have hrp : (n : ℝ) ^ (1 - 2 * σ) = (n : ℝ) * (n : ℝ) ^ (-(2 * σ)) := by
        rw [show (1 - 2 * σ) = 1 + -(2 * σ) by ring, Real.rpow_add hn0R, Real.rpow_one]
      have hprod : 4 * ((∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2 * (n : ℝ) ^ (1 - 2 * σ))
          * jutilaB q R N M n
          = 4 * (max 0 (1 - (n : ℝ) / N)) ^ 2
              * ((∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2
                  * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n) ^ 2
                  * (n : ℝ) ^ (-(2 * σ))) := by
        rw [hbn, hrp]
        field_simp
      rw [div_le_iff₀ hbpos, hnormsq, hprod]
      obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2
          * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹ * pseudoChar selbergPsi r n) ^ 2
          * (n : ℝ) ^ (-(2 * σ)) := ⟨_, rfl⟩
      rw [← hW]
      have hW0 : (0 : ℝ) ≤ W := by
        rw [hW]; positivity
      calc W * ((max 0 (1 - (n : ℝ) / x)) ^ 2) ^ 2
          ≤ W * (4 * (max 0 (1 - (n : ℝ) / N)) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hW0
            have h0 : (0 : ℝ) ≤ (max 0 (1 - (n : ℝ) / x)) ^ 2 := sq_nonneg _
            nlinarith
        _ = 4 * (max 0 (1 - (n : ℝ) / N)) ^ 2 * W := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
  intro n hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hn
  exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩

/-- `a ≤ b → a/c ≤ b/c` at a positive `c`, in the exact shape the level bounds need. -/
private lemma div_le_div_right_of_le {a b c : ℝ} (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hc.le)

/-- `∑_{j ≤ X} j^{−t} ≤ (1 + log X)·X^{1−t}` for `t ≤ 1` — the ONE analytic step of the partial
summation, by induction: `log(X+1) − log X ≥ 1/(X+1)` (`Real.add_one_le_exp` at `−1/(X+1)`)
pays for the new term `(X+1)^{−t} = (X+1)^{1−t}/(X+1)`. -/
private lemma sum_rpow_neg_le {t : ℝ} (ht1 : t ≤ 1) :
    ∀ X : ℕ, 1 ≤ X →
      ∑ j ∈ Finset.Icc 1 X, (j : ℝ) ^ (-t) ≤ (1 + Real.log X) * (X : ℝ) ^ (1 - t) := by
  intro X
  induction X with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      · have ih' := ih hn
        have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hnc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
        have hgap : 1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
          have hexp := Real.add_one_le_exp (-(1 / ((n : ℝ) + 1)))
          have hpos : (0 : ℝ) < (n : ℝ) / ((n : ℝ) + 1) := by positivity
          have hle : (n : ℝ) / ((n : ℝ) + 1) ≤ Real.exp (-(1 / ((n : ℝ) + 1))) := by
            have heq : (n : ℝ) / ((n : ℝ) + 1) = -(1 / ((n : ℝ) + 1)) + 1 := by
              field_simp
              ring
            rw [heq]; exact hexp
          have hlog := Real.log_le_log hpos hle
          rw [Real.log_exp, Real.log_div hn0.ne' (by linarith)] at hlog
          linarith
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), hnc]
        have hA : (n : ℝ) ^ (1 - t) ≤ ((n : ℝ) + 1) ^ (1 - t) :=
          Real.rpow_le_rpow hn0.le (by linarith) (by linarith)
        have hB : (1 + Real.log n) * (n : ℝ) ^ (1 - t)
            ≤ (1 + Real.log n) * ((n : ℝ) + 1) ^ (1 - t) :=
          mul_le_mul_of_nonneg_left hA (by linarith)
        have hsplit : ((n : ℝ) + 1) ^ (1 - t) = ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-t) := by
          rw [show (1 : ℝ) - t = 1 + -t by ring, Real.rpow_add (by linarith), Real.rpow_one]
        have hC : ((n : ℝ) + 1) ^ (-t)
            ≤ (Real.log ((n : ℝ) + 1) - Real.log n) * ((n : ℝ) + 1) ^ (1 - t) := by
          have hpp : (0 : ℝ) < ((n : ℝ) + 1) ^ (-t) :=
            Real.rpow_pos_of_pos (by linarith) _
          have h1 : (1 : ℝ) ≤ (Real.log ((n : ℝ) + 1) - Real.log n) * ((n : ℝ) + 1) := by
            have hh := mul_le_mul_of_nonneg_right hgap (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1)
            rw [div_mul_cancel₀ _ (by linarith : (n : ℝ) + 1 ≠ 0)] at hh
            linarith
          rw [hsplit]
          nlinarith [hpp, h1]
        linarith [ih', hB, hC]

/-- `m·(m^{−t} − (m+1)^{−t}) ≤ m^{−t}` for `0 ≤ t ≤ 1` — the pointwise step that replaces the
second Abel pass: `m·(m+1)^t ≤ (m+1)·m^t` because `m^{1−t} ≤ (m+1)^{1−t}`. -/
private lemma mul_sub_rpow_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t)) ≤ (m : ℝ) ^ (-t) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hsp : (m : ℝ) = (m : ℝ) ^ (1 - t) * (m : ℝ) ^ t := by
    rw [← Real.rpow_add hm0, show (1 : ℝ) - t + t = 1 by ring, Real.rpow_one]
  have hsr : (m : ℝ) + 1 = ((m : ℝ) + 1) ^ (1 - t) * ((m : ℝ) + 1) ^ t := by
    rw [← Real.rpow_add hm1, show (1 : ℝ) - t + t = 1 by ring, Real.rpow_one]
  have hmono : (m : ℝ) ^ (1 - t) ≤ ((m : ℝ) + 1) ^ (1 - t) :=
    Real.rpow_le_rpow hm0.le (by linarith) (by linarith)
  have hkey : (m : ℝ) * ((m : ℝ) + 1) ^ t ≤ ((m : ℝ) + 1) * (m : ℝ) ^ t := by
    calc (m : ℝ) * ((m : ℝ) + 1) ^ t
        = ((m : ℝ) ^ (1 - t) * (m : ℝ) ^ t) * ((m : ℝ) + 1) ^ t := by rw [← hsp]
      _ = (m : ℝ) ^ (1 - t) * ((m : ℝ) ^ t * ((m : ℝ) + 1) ^ t) := by ring
      _ ≤ ((m : ℝ) + 1) ^ (1 - t) * ((m : ℝ) ^ t * ((m : ℝ) + 1) ^ t) :=
          mul_le_mul_of_nonneg_right hmono (by positivity)
      _ = (((m : ℝ) + 1) ^ (1 - t) * ((m : ℝ) + 1) ^ t) * (m : ℝ) ^ t := by ring
      _ = ((m : ℝ) + 1) * (m : ℝ) ^ t := by rw [← hsr]
  have hpr : (m : ℝ) ^ t ≤ ((m : ℝ) + 1) ^ t :=
    Real.rpow_le_rpow hm0.le (by linarith) ht0
  have hp : (0 : ℝ) < (m : ℝ) ^ t := Real.rpow_pos_of_pos hm0 t
  have hr : (0 : ℝ) < ((m : ℝ) + 1) ^ t := Real.rpow_pos_of_pos hm1 t
  rw [hcast, Real.rpow_neg hm0.le, Real.rpow_neg hm1.le, ← sub_nonneg]
  have hexp : ((m : ℝ) ^ t)⁻¹
        - (m : ℝ) * (((m : ℝ) ^ t)⁻¹ - (((m : ℝ) + 1) ^ t)⁻¹)
      = (((m : ℝ) + 1) ^ t - (m : ℝ) * (((m : ℝ) + 1) ^ t - (m : ℝ) ^ t))
          / ((m : ℝ) ^ t * ((m : ℝ) + 1) ^ t) := by
    field_simp
  rw [hexp]
  refine div_nonneg ?_ (by positivity)
  nlinarith [hkey, hpr]

/-- The telescoping sum over `Icc 1 Y`. -/
private lemma sum_Icc_telescope (f : ℕ → ℝ) (Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 Y, (f m - f (m + 1)) = f 1 - f (Y + 1) := by
  induction Y with
  | zero => simp
  | succ Y ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Y + 1), ih]
      ring

/-- **Abel's identity** in the form the partial summation consumes:
`∑_{n ≤ Y+1} c_n n^{−t} = S(Y+1)(Y+1)^{−t} + ∑_{m ≤ Y} S(m)(m^{−t} − (m+1)^{−t})`. -/
private lemma sum_mul_rpow_eq_abel (c : ℕ → ℝ) (t : ℝ) (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 (Y + 1), c n * (n : ℝ) ^ (-t)
      = (∑ n ∈ Finset.Icc 1 (Y + 1), c n) * ((Y + 1 : ℕ) : ℝ) ^ (-t)
        + ∑ m ∈ Finset.Icc 1 Y, (∑ n ∈ Finset.Icc 1 m, c n)
            * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t)) := by
  induction Y with
  | zero => simp
  | succ Y ih =>
      have e1 : ∑ n ∈ Finset.Icc 1 (Y + 1 + 1), c n * (n : ℝ) ^ (-t)
          = (∑ n ∈ Finset.Icc 1 (Y + 1), c n * (n : ℝ) ^ (-t))
            + c (Y + 1 + 1) * ((Y + 1 + 1 : ℕ) : ℝ) ^ (-t) :=
        Finset.sum_Icc_succ_top (by omega) _
      have e2 : ∑ n ∈ Finset.Icc 1 (Y + 1 + 1), c n
          = (∑ n ∈ Finset.Icc 1 (Y + 1), c n) + c (Y + 1 + 1) :=
        Finset.sum_Icc_succ_top (by omega) _
      have e3 : ∑ m ∈ Finset.Icc 1 (Y + 1), (∑ n ∈ Finset.Icc 1 m, c n)
              * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t))
          = (∑ m ∈ Finset.Icc 1 Y, (∑ n ∈ Finset.Icc 1 m, c n)
              * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t)))
            + (∑ n ∈ Finset.Icc 1 (Y + 1), c n)
              * (((Y + 1 : ℕ) : ℝ) ^ (-t) - ((Y + 1 + 1 : ℕ) : ℝ) ^ (-t)) :=
        Finset.sum_Icc_succ_top (by omega) _
      rw [e1, ih, e2, e3]
      ring

/-- **THE PARTIAL SUMMATION, generic**: from `S(m) ≤ B·(m + l)` at every `m ≥ 1` and
`0 ≤ t ≤ 1`, Abel gives `∑_{n ≤ X} c_n n^{−t} ≤ B·((2 + log X)·X^{1−t} + l)` — every scale,
no `1/(1−t)` loss (the `l`-term's telescope is EXACT, so `l` is carried once, not twice). -/
private lemma partial_summation_core {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {c : ℕ → ℝ}
    {B l : ℝ} (hB : 0 ≤ B)
    (hS : ∀ m : ℕ, 1 ≤ m → ∑ n ∈ Finset.Icc 1 m, c n ≤ B * ((m : ℝ) + l))
    (X : ℕ) (hX : 1 ≤ X) :
    ∑ n ∈ Finset.Icc 1 X, c n * (n : ℝ) ^ (-t)
      ≤ B * ((2 + Real.log X) * (X : ℝ) ^ (1 - t) + l) := by
  obtain ⟨Y, rfl⟩ : ∃ Y, X = Y + 1 := ⟨X - 1, by omega⟩
  have hY0 : (0 : ℝ) < ((Y + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos Y
  have hPn : (0 : ℝ) ≤ ((Y + 1 : ℕ) : ℝ) ^ (-t) := Real.rpow_nonneg hY0.le _
  have h1 : (∑ n ∈ Finset.Icc 1 (Y + 1), c n) * ((Y + 1 : ℕ) : ℝ) ^ (-t)
      ≤ B * (((Y + 1 : ℕ) : ℝ) + l) * ((Y + 1 : ℕ) : ℝ) ^ (-t) :=
    mul_le_mul_of_nonneg_right (hS (Y + 1) (by omega)) hPn
  have h2 : ∀ m ∈ Finset.Icc 1 Y, (∑ n ∈ Finset.Icc 1 m, c n)
        * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t))
      ≤ B * ((m : ℝ) ^ (-t) + l * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t))) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hcm : (0 : ℝ) ≤ (m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t) := by
      have hc1 : ((m + 1 : ℕ) : ℝ) ^ (-t) ≤ (m : ℝ) ^ (-t) :=
        Real.rpow_le_rpow_of_nonpos hm0 (by push_cast; linarith) (by linarith)
      linarith
    calc (∑ n ∈ Finset.Icc 1 m, c n) * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t))
        ≤ (B * ((m : ℝ) + l)) * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t)) :=
          mul_le_mul_of_nonneg_right (hS m hm1) hcm
      _ = B * ((m : ℝ) * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t))
            + l * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t))) := by ring
      _ ≤ B * ((m : ℝ) ^ (-t) + l * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t))) := by
          have hstep := mul_sub_rpow_le ht0 ht1 hm1
          nlinarith [hB, hstep]
  have htel : ∑ m ∈ Finset.Icc 1 Y, ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t))
      = 1 - ((Y + 1 : ℕ) : ℝ) ^ (-t) := by
    have h := sum_Icc_telescope (fun m : ℕ => ((m : ℕ) : ℝ) ^ (-t)) Y
    simpa using h
  have hrewrite : ∑ m ∈ Finset.Icc 1 Y,
        B * ((m : ℝ) ^ (-t) + l * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t)))
      = B * (∑ m ∈ Finset.Icc 1 Y, (m : ℝ) ^ (-t))
        + B * l * (1 - ((Y + 1 : ℕ) : ℝ) ^ (-t)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, htel]
    ring
  have hkey1 : (∑ m ∈ Finset.Icc 1 Y, (∑ n ∈ Finset.Icc 1 m, c n)
        * ((m : ℝ) ^ (-t) - ((m + 1 : ℕ) : ℝ) ^ (-t)))
      ≤ B * (∑ m ∈ Finset.Icc 1 Y, (m : ℝ) ^ (-t))
        + B * l * (1 - ((Y + 1 : ℕ) : ℝ) ^ (-t)) := by
    rw [← hrewrite]
    exact Finset.sum_le_sum h2
  have hSig : ∑ m ∈ Finset.Icc 1 Y, (m : ℝ) ^ (-t)
      ≤ (1 + Real.log ((Y + 1 : ℕ) : ℝ)) * ((Y + 1 : ℕ) : ℝ) ^ (1 - t) := by
    refine le_trans ?_ (sum_rpow_neg_le ht1 (Y + 1) (by omega))
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega))
      (fun i _ _ => Real.rpow_nonneg (by positivity) _)
  have hkey2 : B * (∑ m ∈ Finset.Icc 1 Y, (m : ℝ) ^ (-t))
      ≤ B * ((1 + Real.log ((Y + 1 : ℕ) : ℝ)) * ((Y + 1 : ℕ) : ℝ) ^ (1 - t)) :=
    mul_le_mul_of_nonneg_left hSig hB
  have hpow : ((Y + 1 : ℕ) : ℝ) ^ (1 - t)
      = ((Y + 1 : ℕ) : ℝ) * ((Y + 1 : ℕ) : ℝ) ^ (-t) := by
    rw [show (1 : ℝ) - t = 1 + -t by ring, Real.rpow_add hY0, Real.rpow_one]
  rw [sum_mul_rpow_eq_abel c t Y, hpow]
  rw [hpow] at hkey2
  linarith [h1, hkey1, hkey2]

/-- **THE PARTIAL SUMMATION** against S10-H (`u ≥ z₂`) and S10-L (`2 ≤ u ≤ z₂`) — every scale
(design v2 §A.3): Abel with `1/2 ≤ σ` (`(2σ − 1) ≥ 0`; dyadic would break F6 at `σ → 1/2`),
`(x^{2−2σ} − 1)/(2 − 2σ) ≤ x^{2−2σ}·log x` (no `1/λ` loss), the `+ log z₂` term CARRIED. The
constant is the row's own `∃ C` — `C = 2·max(4K_H, K_L)` from the two landed prefactors
(`GrahamHard3.lean:2498`, `:2559`), printed as a symbol, never as S10's `K`.

**The landed witness is `4·max(4K_H, K_L)`**, twice the design's: the design's factor `2` pays
only for the `u ∈ [1, 2)` sliver, and the Abel bookkeeping's natural shape is
`B·((2 + log X)·X^{1−t} + l)` — a `2 + log X`, converted to the row's `1 + log x` by
`2 + log x ≤ 2(1 + log x)` at a second factor `2`. Every consumer reading
`A ≤ 616·C_ps·x^{2−2σ}` doubles `C_ps` accordingly (the threshold `D₁` moves by `2^{240/43}`). -/
theorem sum_sq_sum_bvWeight_mul_rpow_le : ∃ C : ℝ, 0 < C ∧ ∀ z₁ z₂ : ℕ, 2 ≤ z₁ → z₁ < z₂ →
    ∀ x σ : ℝ, (z₂ : ℝ) ≤ x → 1 / 2 ≤ σ → σ ≤ 1 →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2 * (n : ℝ) ^ (1 - 2 * σ)
      ≤ C * (Real.log z₂ / Real.log ((z₂ : ℝ) / z₁) ^ 2)
          * ((1 + Real.log x) * x ^ (2 - 2 * σ) + Real.log z₂) := by
  obtain ⟨CH, hCH, hH⟩ := sum_sq_sum_bvWeight_le_full
  obtain ⟨CL, hCL, hL⟩ := sum_sq_sum_bvWeight_le_low
  have hK4 : 4 * CH ≤ max (4 * CH) CL := le_max_left _ _
  have hKL : CL ≤ max (4 * CH) CL := le_max_right _ _
  have hKpos : (0 : ℝ) < max (4 * CH) CL := by linarith
  refine ⟨4 * max (4 * CH) CL, by linarith, fun z₁ z₂ hz₁ hz x σ hx hσ0 hσ1 => ?_⟩
  have hz₂3 : 3 ≤ z₂ := by omega
  have hz₁R : (1 : ℝ) < (z₁ : ℝ) := by exact_mod_cast (by omega : 1 < z₁)
  have hz₂R : (1 : ℝ) < (z₂ : ℝ) := by exact_mod_cast (by omega : 1 < z₂)
  have hl₁ : (0 : ℝ) < Real.log (z₁ : ℝ) := Real.log_pos hz₁R
  have hl₂ : (0 : ℝ) < Real.log (z₂ : ℝ) := Real.log_pos hz₂R
  have hl12 : Real.log (z₁ : ℝ) ≤ Real.log (z₂ : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hz.le)
  have hΛ : (0 : ℝ) < Real.log ((z₂ : ℝ) / z₁) ^ 2 := by
    have hLog : (0 : ℝ) < Real.log ((z₂ : ℝ) / z₁) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ (by linarith), one_mul]
      exact_mod_cast hz
    positivity
  have hd : (0 : ℝ) ≤ Real.log z₂ / Real.log ((z₂ : ℝ) / z₁) ^ 2 := div_nonneg hl₂.le hΛ.le
  -- **S(u) at every scale**: S10-H above `z₂`, S10-L in `[2, z₂]`, and `S(1) ≤ S(2)` below —
  -- the factor 2 of `B` absorbing the `[1, 2)` sliver.
  have hSbound : ∀ m : ℕ, 1 ≤ m →
      ∑ n ∈ Finset.Icc 1 m, (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2
        ≤ 2 * max (4 * CH) CL * (Real.log z₂ / Real.log ((z₂ : ℝ) / z₁) ^ 2)
            * ((m : ℝ) + Real.log z₂) := by
    intro m hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rcases le_or_gt (z₂ : ℝ) (m : ℝ) with hcase | hcase
    · have h := hH z₁ z₂ hz₁ hz (m : ℝ) hcase
      rw [Nat.floor_natCast] at h
      refine h.trans ?_
      calc 2 * (Real.log z₁ + Real.log z₂) / Real.log ((z₂ : ℝ) / z₁) ^ 2 * (CH * (m : ℝ))
          = 2 * (Real.log z₁ + Real.log z₂) * (CH * (m : ℝ))
              / Real.log ((z₂ : ℝ) / z₁) ^ 2 := by ring
        _ ≤ 2 * max (4 * CH) CL * Real.log z₂ * ((m : ℝ) + Real.log z₂)
              / Real.log ((z₂ : ℝ) / z₁) ^ 2 := by
            refine div_le_div_right_of_le ?_ hΛ
            nlinarith [mul_nonneg (mul_nonneg hl₂.le hm0) (sub_nonneg.mpr hK4),
              mul_nonneg hCH.le (mul_nonneg (sub_nonneg.mpr hl12) hm0),
              mul_nonneg (mul_nonneg hKpos.le hl₂.le) hl₂.le,
              mul_nonneg (mul_nonneg hKpos.le hl₂.le) hm0]
        _ = 2 * max (4 * CH) CL * (Real.log z₂ / Real.log ((z₂ : ℝ) / z₁) ^ 2)
              * ((m : ℝ) + Real.log z₂) := by ring
    · rcases le_or_gt (2 : ℝ) (m : ℝ) with hm2 | hm2
      · have h := hL z₁ z₂ hz₁ hz (m : ℝ) hm2 hcase.le
        rw [Nat.floor_natCast] at h
        refine h.trans ?_
        calc CL * Real.log z₂ * (Real.log z₂ + (m : ℝ)) / Real.log ((z₂ : ℝ) / z₁) ^ 2
            ≤ 2 * max (4 * CH) CL * Real.log z₂ * ((m : ℝ) + Real.log z₂)
                / Real.log ((z₂ : ℝ) / z₁) ^ 2 := by
              refine div_le_div_right_of_le ?_ hΛ
              nlinarith [mul_nonneg (mul_nonneg hl₂.le (by linarith : (0:ℝ) ≤ Real.log z₂ + m))
                (sub_nonneg.mpr hKL), mul_nonneg (mul_nonneg hKpos.le hl₂.le)
                (by linarith : (0:ℝ) ≤ Real.log z₂ + m)]
          _ = 2 * max (4 * CH) CL * (Real.log z₂ / Real.log ((z₂ : ℝ) / z₁) ^ 2)
                * ((m : ℝ) + Real.log z₂) := by ring
      · have hmeq : m = 1 := by
          have hlt : m < 2 := by exact_mod_cast hm2
          omega
        subst hmeq
        have hz₂2 : (2 : ℝ) ≤ (z₂ : ℝ) := by exact_mod_cast (by omega : 2 ≤ z₂)
        have h := hL z₁ z₂ hz₁ hz 2 le_rfl hz₂2
        rw [show ⌊(2 : ℝ)⌋₊ = 2 from by norm_num] at h
        have hsub : ∑ n ∈ Finset.Icc 1 1, (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2
            ≤ ∑ n ∈ Finset.Icc 1 2, (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega))
            (fun i _ _ => sq_nonneg _)
        refine (hsub.trans h).trans ?_
        rw [Nat.cast_one]
        calc CL * Real.log z₂ * (Real.log z₂ + 2) / Real.log ((z₂ : ℝ) / z₁) ^ 2
            ≤ 2 * max (4 * CH) CL * Real.log z₂ * (1 + Real.log z₂)
                / Real.log ((z₂ : ℝ) / z₁) ^ 2 := by
              refine div_le_div_right_of_le ?_ hΛ
              nlinarith [mul_nonneg (mul_nonneg hl₂.le (by linarith : (0:ℝ) ≤ Real.log z₂ + 2))
                (sub_nonneg.mpr hKL), mul_nonneg (mul_nonneg hKpos.le hl₂.le) hl₂.le]
          _ = 2 * max (4 * CH) CL * (Real.log z₂ / Real.log ((z₂ : ℝ) / z₁) ^ 2)
                * (1 + Real.log z₂) := by ring
  -- the table's scales
  have hx1 : (1 : ℝ) ≤ x := by
    have h3 : (3 : ℝ) ≤ (z₂ : ℝ) := by exact_mod_cast hz₂3
    linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hXge : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have hXle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hX0 : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hXge
  have ht0 : (0 : ℝ) ≤ 2 * σ - 1 := by linarith
  have ht1 : (2 : ℝ) * σ - 1 ≤ 1 := by linarith
  have he1 : (1 : ℝ) - 2 * σ = -(2 * σ - 1) := by ring
  have he2 : (2 : ℝ) - 2 * σ = 1 - (2 * σ - 1) := by ring
  have hBn : (0 : ℝ) ≤ 2 * max (4 * CH) CL
      * (Real.log z₂ / Real.log ((z₂ : ℝ) / z₁) ^ 2) :=
    mul_nonneg (by linarith) hd
  have hcore := partial_summation_core
    (c := fun n : ℕ => (∑ d ∈ n.divisors, bvWeight z₁ z₂ d) ^ 2) ht0 ht1 hBn hSbound
    ⌊x⌋₊ hXge
  simp only [he1]
  rw [he2]
  refine hcore.trans ?_
  have hlogX : Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x := Real.log_le_log hX0 hXle
  have hlogXn : (0 : ℝ) ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hXge)
  have hlogx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hpowX : ((⌊x⌋₊ : ℕ) : ℝ) ^ (1 - (2 * σ - 1)) ≤ x ^ (1 - (2 * σ - 1)) :=
    Real.rpow_le_rpow hX0.le hXle (by linarith)
  have hpowpos : (0 : ℝ) ≤ x ^ (1 - (2 * σ - 1)) := Real.rpow_nonneg hxpos.le _
  have hpowXpos : (0 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) ^ (1 - (2 * σ - 1)) :=
    Real.rpow_nonneg hX0.le _
  have hchain : (2 + Real.log ((⌊x⌋₊ : ℕ) : ℝ)) * ((⌊x⌋₊ : ℕ) : ℝ) ^ (1 - (2 * σ - 1))
      ≤ 2 * ((1 + Real.log x) * x ^ (1 - (2 * σ - 1))) := by
    nlinarith [hpowX, hpowpos, hpowXpos, hlogX, hlogx0, hlogXn]
  have hKd : (0 : ℝ) ≤ max (4 * CH) CL * (Real.log z₂ / Real.log ((z₂ : ℝ) / z₁) ^ 2) :=
    mul_nonneg hKpos.le hd
  nlinarith [hchain, hKd, hl₂]

/-- **HALÁSZ AT THE SYSTEM** (Lemma 7 instantiated): the sum of the detector's moduli over `J`
zeros, squared, against the residue-block series `B(s̄_j + s_k) = halaszBTsum (jutilaB) χ χ`
(`conj(χ)·χ = χ₀`). The unimodular `η_j` exist by `exists_unimodular_mul_eq_norm`. -/
theorem sq_sum_norm_jutilaDetector_le (χ : DirichletCharacter ℂ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁)
    {R x σ N M : ℝ} (hx : 1 ≤ x) (hM : 1 ≤ M) (hMN : M ≤ N) (hz₁M : M ≤ z₁) (hxN : 2 * x ≤ N)
    (hσ : 0 ≤ σ) {J : ℕ} (ρ : Fin J → ℂ) (η : Fin J → ℂ)
    (hη : ∀ j, η j * jutilaDetector χ z₁ z₂ R x (ρ j) = ‖jutilaDetector χ z₁ z₂ R x (ρ j)‖) :
    (∑ j, ‖jutilaDetector χ z₁ z₂ R x (ρ j)‖) ^ 2
      ≤ (∑ n ∈ Finset.Ioc z₁ ⌊x⌋₊, ‖jutilaA q z₁ z₂ R x σ n‖ ^ 2 / jutilaB q R N M n)
        * (∑ j, ∑ k, (starRingEnd ℂ) (η j) * η k
            * Salt.MR.halaszBTsum (jutilaB q R N M) χ χ
                ((starRingEnd ℂ) (ρ j - σ) + (ρ k - σ))).re := by
  -- `hx`, `hσ`, `hz₁` are consumed by NONE of the five inputs; kept as the row's shape and READ
  -- here (the sub-freeze's §A.8 rule for a route-only binder).
  have _hx := hx
  have _hσ := hσ
  have _hz₁ := hz₁
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hpoly : ∀ j, jutilaDetector χ z₁ z₂ R x (ρ j)
      = Salt.MR.dirichletPolyChi (Finset.Ioc z₁ ⌊x⌋₊) (jutilaA q z₁ z₂ R x σ) χ (ρ j - σ) :=
    fun j => jutilaDetector_eq_dirichletPolyChi χ z₁ z₂ R x σ (ρ j)
  simp only [hpoly] at hη ⊢
  exact Salt.MR.halasz_weighted_tsum (by simp) (jutilaA q z₁ z₂ R x σ)
    (fun n hn ha => jutilaB_pos_of_ne_zero hM hMN hn hz₁M hxN ha)
    (jutilaB_nonneg hM0 hMN q R) (jutilaB_zero q R N M) (fun _ => χ) (fun j => ρ j - σ) η hη
    (fun j k => summable_jutilaB_series hM hMN χ χ _)

/-! ## (ii) The floor in the `S'`-form (W9c) -/

/-- The floor with the `r`-sum `S' = Σ'_r r⁻¹` UNWEAKENED — the landed `_floor_at_zero`'s own
intermediate (`JutilaDetector.lean:1418–1424`) with Lemma 5 NOT applied, so that `φ(q)/q` cancels
between Halász's two sides (design v2 §A.5) and no upper bound on the coprime harmonic sum is
ever needed. -/
theorem jutilaDetector_floor_sum [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) {R : ℝ} (hR : 1 ≤ R) {x : ℝ}
    (hx : 1 ≤ x) {ρ : ℂ} (h0 : LFunction χ ρ = 0) (hβ : (119 : ℝ) / 120 ≤ ρ.re) (hβ1 : ρ.re < 1)
    {T : ℝ} (hρT : |ρ.im| ≤ T) :
    (1 - 1 / x) ^ 2 * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹)
      - 25 * (T + 2) * Real.sqrt q * (1 + Real.log q) * Real.sqrt z₂ * R ^ (3 / 2 : ℝ)
        * x ^ ((1 : ℝ) / 2 - ρ.re)
      ≤ ‖jutilaDetector χ z₁ z₂ R x ρ‖ := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hsplit := jutilaFull_eq_add_detector χ hz₁ hz R hx ρ
  have hdet : jutilaDetector χ z₁ z₂ R x ρ
      = jutilaFull χ z₁ z₂ R x ρ
        - ((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ : ℝ) : ℂ) * kern2 (1 / x) := by
    rw [hsplit]; ring
  have hsum0 : (0 : ℝ) ≤ ∑ r ∈ rFilter q R, (r : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun r _ => by positivity)
  have hxx : (0 : ℝ) ≤ 1 - 1 / x := by
    rw [sub_nonneg, div_le_one hx0]
    exact hx
  have hker : ‖((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ : ℝ) : ℂ) * kern2 (1 / x)‖
      = (∑ r ∈ rFilter q R, (r : ℝ)⁻¹) * (1 - 1 / x) ^ 2 := by
    rw [kern2_value hx0, if_pos hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsum0, norm_pow]
    congr 1
    rw [show (1 : ℂ) - 1 / (x : ℂ) = ((1 - 1 / x : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxx]
  have hrev : (∑ r ∈ rFilter q R, (r : ℝ)⁻¹) * (1 - 1 / x) ^ 2
      - ‖jutilaFull χ z₁ z₂ R x ρ‖ ≤ ‖jutilaDetector χ z₁ z₂ R x ρ‖ := by
    rw [hdet, ← hker]
    have h := norm_sub_norm_le
      (((∑ r ∈ rFilter q R, (r : ℝ)⁻¹ : ℝ) : ℂ) * kern2 (1 / x)) (jutilaFull χ z₁ z₂ R x ρ)
    rw [norm_sub_rev] at h
    linarith
  have hE := norm_jutilaFull_le hχ hq hz₁ hz (le_trans zero_le_one hR) hx h0 hβ hβ1 hρT
  linarith [hrev, hE]

/-- At F5's table the error is at most a THIRD of `S'` (`f5_error_bound` + `f5_error_le_main` +
`inv_log_le_totient_div` at `q ≤ D` + `sum_sf_coprime_inv_ge` — EXACTLY a third), and
`(1 − 1/x)² ≥ (11/12)²` at `x ≥ D ≥ 12`: `‖g(ρ)‖ ≥ S'/2` at every zero of the system. The binders
are `jutilaDetector_floor_F5`'s, verbatim. -/
theorem jutilaDetector_floor_half_sum [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {z₁ z₂ : ℕ} (hz₁ : 2 ≤ z₁) (hz : z₁ < z₂) {T D R x : ℝ} (hT : 1 ≤ T)
    (hD : D = q * T) (hD0 : (10 : ℝ) ^ 20 ≤ D) (hR : R = D ^ ((1 : ℝ) / 10))
    (hz₂ : (z₂ : ℝ) ≤ D ^ ((7 : ℝ) / 2)) (hx : D ^ ((13 : ℝ) / 2) ≤ x) {ρ : ℂ}
    (h0 : LFunction χ ρ = 0) (hβ : (119 : ℝ) / 120 ≤ ρ.re) (hβ1 : ρ.re < 1) (hρT : |ρ.im| ≤ T) :
    (∑ r ∈ rFilter q R, (r : ℝ)⁻¹) / 2 ≤ ‖jutilaDetector χ z₁ z₂ R x ρ‖ := by
  have hq1 : 1 ≤ q := by omega
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hD1 : (1 : ℝ) ≤ D := le_trans (by norm_num) hD0
  have hD12 : (12 : ℝ) ≤ D := le_trans (by norm_num) hD0
  have hDpos : (0 : ℝ) < D := by linarith
  have hlogD : (0 : ℝ) ≤ Real.log D := Real.log_nonneg hD1
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hR]
    exact Real.one_le_rpow hD1 (by norm_num)
  have hxD : D ≤ x := by
    refine le_trans ?_ hx
    have h1 : D ^ (1 : ℝ) ≤ D ^ ((13 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
    rwa [Real.rpow_one] at h1
  have hx12 : (12 : ℝ) ≤ x := le_trans hD12 hxD
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hfloor := jutilaDetector_floor_sum hχ hq hz₁ hz hR1 hx1 h0 hβ hβ1 hρT
  have hE := f5_error_bound hq1 hT hD hR hz₂ hx hβ hβ1
  have hMain := f5_error_le_main hD0
  have hφ := inv_log_le_totient_div hq1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1R
  have hqD : (q : ℝ) ≤ D := by rw [hD]; nlinarith
  have hlogqD : Real.log q ≤ Real.log D := Real.log_le_log (by linarith) hqD
  have hdd : Real.log q / Real.log 2 ≤ Real.log D / Real.log 2 := by
    rw [div_le_div_iff₀ hlog2pos hlog2pos]
    nlinarith
  have hqden : (0 : ℝ) < Real.log q / Real.log 2 + 1 := by
    have hnn : (0 : ℝ) ≤ Real.log q / Real.log 2 := div_nonneg hlogq hlog2pos.le
    linarith
  have hinv : 1 / (Real.log D / Real.log 2 + 1) ≤ 1 / (Real.log q / Real.log 2 + 1) :=
    one_div_le_one_div_of_le hqden (by linarith)
  have hchain : 75 * (1 + Real.log D) * D ^ (-(71 / 240 : ℝ))
      ≤ 2 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * (Real.log D / 10) := by
    refine hMain.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) ?_
    · exact le_trans hinv hφ
    · linarith
  have hlogR : Real.log R = Real.log D / 10 := by
    rw [hR, Real.log_rpow hDpos]
    ring
  have hL5 : 6 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * Real.log R
      ≤ ∑ r ∈ rFilter q R, (r : ℝ)⁻¹ := by
    have h := sum_sf_coprime_inv_ge q R hq1 hR1
    simp only [one_div] at h
    exact h
  rw [hlogR] at hL5
  have hS0 : (0 : ℝ) ≤ ∑ r ∈ rFilter q R, (r : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun r _ => by positivity)
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ,
      W = 1 / Real.pi ^ 2 * (((Nat.totient q : ℝ) / q) * (Real.log D / 10)) := ⟨_, rfl⟩
  have e6 : 6 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * (Real.log D / 10) = 6 * W := by
    rw [hWdef]; ring
  have e2 : 2 / Real.pi ^ 2 * ((Nat.totient q : ℝ) / q) * (Real.log D / 10) = 2 * W := by
    rw [hWdef]; ring
  rw [e6] at hL5
  rw [e2] at hchain
  -- `E ≤ 2W ≤ S'/3` — the chain's constants: `f5_error_le_main`'s `2/π²` is one third of
  -- `sum_sf_coprime_inv_ge`'s `6/π²`, so the third holds at every `D` on the table.
  have hthird : 25 * (T + 2) * Real.sqrt q * (1 + Real.log q) * Real.sqrt z₂
      * R ^ (3 / 2 : ℝ) * x ^ ((1 : ℝ) / 2 - ρ.re)
      ≤ (∑ r ∈ rFilter q R, (r : ℝ)⁻¹) / 3 := by
    linarith only [hE, hchain, hL5]
  have h1x : (1 : ℝ) / x ≤ 1 / 12 := by
    rw [div_le_div_iff₀ hxpos (by norm_num)]
    linarith
  have h2x : (11 : ℝ) / 12 ≤ 1 - 1 / x := by linarith
  have hfive : (121 : ℝ) / 144 ≤ (1 - 1 / x) ^ 2 := by
    calc (121 : ℝ) / 144 = (11 / 12 : ℝ) * (11 / 12) := by norm_num
      _ ≤ (1 - 1 / x) * (1 - 1 / x) := mul_le_mul h2x h2x (by norm_num) (by linarith)
      _ = (1 - 1 / x) ^ 2 := by ring
  have hprod : 121 / 144 * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹)
      ≤ (1 - 1 / x) ^ 2 * (∑ r ∈ rFilter q R, (r : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_right hfive hS0
  linarith only [hfloor, hthird, hprod, hS0]

/-! ## (iii) The two integrated kernel bounds (W9c) -/

/-- The DIAGONAL integrated bound (real `0 ≤ s ≤ 1/60`, `ξ₀ ≥ 0` so `M = e^ξ ≥ 1` — the binder the
design's v1 dropped, kill 4): `‖resKernel s N M‖ ≤ 1.0255·log(N/M)` (W9b's
`norm_resKernel_le_log`) integrates to `≤ 1.0255·|Ξ||H|·(η₁ − ξ₀)`. -/
theorem integral_norm_resKernel_diag_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 60)
    {ξ₀ ξ₁ η₀ η₁ : ℝ} (hξ0 : 0 ≤ ξ₀) (hξ : ξ₀ ≤ ξ₁) (hη : η₀ ≤ η₁) (h : ξ₁ ≤ η₀) :
    ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, ‖resKernel (s : ℂ) (Real.exp η) (Real.exp ξ)‖
      ≤ 2 / ((59 / 60) * (119 / 60)) * ((ξ₁ - ξ₀) * (η₁ - η₀)) * (η₁ - ξ₀) := by
  have hC0 : (0 : ℝ) ≤ 2 / ((59 / 60) * (119 / 60)) := by norm_num
  have hηd : (0 : ℝ) ≤ η₁ - η₀ := by linarith
  have hξd : (0 : ℝ) ≤ ξ₁ - ξ₀ := by linarith
  -- the pointwise bound, from W9b's `norm_resKernel_le_log` at `1 ≤ e^ξ ≤ e^η`
  have hpt : ∀ ξ ∈ Set.uIoc ξ₀ ξ₁, ∀ η ∈ Set.uIoc η₀ η₁,
      ‖resKernel (s : ℂ) (Real.exp η) (Real.exp ξ)‖
        ≤ 2 / ((59 / 60) * (119 / 60)) * (η₁ - ξ₀) := by
    intro ξ hξm η hηm
    rw [Set.uIoc_of_le hξ] at hξm
    rw [Set.uIoc_of_le hη] at hηm
    have hξ1 : (1 : ℝ) ≤ Real.exp ξ := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith [hξm.1])
    have hle : Real.exp ξ ≤ Real.exp η :=
      Real.exp_le_exp.mpr (by linarith [hξm.2, hηm.1])
    have hlog : Real.log (Real.exp η / Real.exp ξ) = η - ξ := by
      rw [← Real.exp_sub, Real.log_exp]
    have hb := norm_resKernel_le_log hs0 hs hξ1 hle
    rw [hlog] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    linarith [hξm.1, hηm.2]
  -- the inner integral, by the constant bound (`norm_integral_le_of_norm_le_const` carries no
  -- integrability hypothesis)
  have hnn : ∀ ξ : ℝ, (0 : ℝ) ≤ ∫ η in η₀..η₁, ‖resKernel (s : ℂ) (Real.exp η) (Real.exp ξ)‖ :=
    fun ξ => intervalIntegral.integral_nonneg hη (fun _ _ => norm_nonneg _)
  have hinner : ∀ ξ ∈ Set.uIoc ξ₀ ξ₁,
      (∫ η in η₀..η₁, ‖resKernel (s : ℂ) (Real.exp η) (Real.exp ξ)‖)
        ≤ 2 / ((59 / 60) * (119 / 60)) * (η₁ - ξ₀) * (η₁ - η₀) := by
    intro ξ hξm
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun η => ‖resKernel (s : ℂ) (Real.exp η) (Real.exp ξ)‖)
      (C := 2 / ((59 / 60) * (119 / 60)) * (η₁ - ξ₀))
      (fun η hηm => (Real.norm_of_nonneg (norm_nonneg _)).le.trans (hpt ξ hξm η hηm))
    rw [abs_of_nonneg hηd] at h
    exact (Real.le_norm_self _).trans h
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun ξ => ∫ η in η₀..η₁, ‖resKernel (s : ℂ) (Real.exp η) (Real.exp ξ)‖)
    (C := 2 / ((59 / 60) * (119 / 60)) * (η₁ - ξ₀) * (η₁ - η₀))
    (fun ξ hξm => (Real.norm_of_nonneg (hnn ξ)).le.trans (hinner ξ hξm))
  rw [abs_of_nonneg hξd] at houter
  calc ∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, ‖resKernel (s : ℂ) (Real.exp η) (Real.exp ξ)‖
      ≤ 2 / ((59 / 60) * (119 / 60)) * (η₁ - ξ₀) * (η₁ - η₀) * (ξ₁ - ξ₀) :=
        (Real.le_norm_self _).trans houter
    _ = 2 / ((59 / 60) * (119 / 60)) * ((ξ₁ - ξ₀) * (η₁ - η₀)) * (η₁ - ξ₀) := by ring

/-- The OFF-DIAGONAL integrated bound (`Im s ≠ 0`; `ξ₀, η₀ ≥ 0` — kill 4): `resKernel s N M =
K̃(−s)·(N^{−s} − M^{−s})` with `|K̃(−s)| ≤ 1.0255/|s|` (W9b's `norm_resKernel_le_div`), and
`|∫_H e^{−sη} dη| ≤ 2/|s|`, `|∫_Ξ e^{−sξ} dξ| ≤ 2/|s|` (`Re s ≥ 0`, `η, ξ ≥ 0`), so
`‖∫∫‖ ≤ 1.0255·(|Ξ| + |H|)·2/|s|² ≤ 2.051·(|Ξ| + |H|)/(Im s)²`. -/
theorem norm_integral_resKernel_offdiag_le {s : ℂ} (hs0 : 0 ≤ s.re) (hs : s.re ≤ 1 / 60)
    (him : s.im ≠ 0) {ξ₀ ξ₁ η₀ η₁ : ℝ} (hξ0 : 0 ≤ ξ₀) (hη0 : 0 ≤ η₀) (hξ : ξ₀ ≤ ξ₁)
    (hη : η₀ ≤ η₁) :
    ‖∫ ξ in ξ₀..ξ₁, ∫ η in η₀..η₁, resKernel s (Real.exp η) (Real.exp ξ)‖
      ≤ 2 * (2 / ((59 / 60) * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀)) / s.im ^ 2 := by
  have hs' : s ≠ 0 := fun h => him (by rw [h]; simp)
  have hspos : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr hs'
  have hsne : (-s) ≠ 0 := neg_ne_zero.mpr hs'
  have hξd : (0 : ℝ) ≤ ξ₁ - ξ₀ := by linarith
  have hηd : (0 : ℝ) ≤ η₁ - η₀ := by linarith
  -- the live cpow chain: `(e^u)^{−s} = exp(−s·u)`
  have hexp : ∀ u : ℝ, ((Real.exp u : ℝ) : ℂ) ^ (-s) = Complex.exp (-s * (u : ℂ)) := by
    intro u
    have hne : ((Real.exp u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'
    rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    congr 1
    ring
  obtain ⟨K, hKdef⟩ : ∃ K : ℂ, K = 2 / ((-s) * (1 - s) * (2 - s)) := ⟨_, rfl⟩
  have hker : ∀ u v : ℝ, resKernel s (Real.exp u) (Real.exp v)
      = K * (Complex.exp (-s * (u : ℂ)) - Complex.exp (-s * (v : ℂ))) := by
    intro u v
    rw [resKernel_of_ne_zero hs', hexp u, hexp v, hKdef]
    ring
  have hcont : Continuous (fun u : ℝ => Complex.exp (-s * (u : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  -- the one-dimensional exponential integral and its bound `≤ 2/‖s‖`
  have hexp1 : ∀ u : ℝ, 0 ≤ u → ‖Complex.exp (-s * (u : ℂ))‖ ≤ 1 := by
    intro u hu
    rw [Complex.norm_exp]
    refine Real.exp_le_one_iff.mpr ?_
    have hre : (-s * (u : ℂ)).re = -(s.re * u) := by simp [Complex.mul_re]
    rw [hre]
    nlinarith [hs0, hu]
  have hnormI : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      ‖∫ u in a..b, Complex.exp (-s * (u : ℂ))‖ ≤ 2 / ‖s‖ := by
    intro a b ha hb
    have h2 : ‖Complex.exp (-s * (b : ℂ)) - Complex.exp (-s * (a : ℂ))‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [hexp1 a ha, hexp1 b hb])
    rw [integral_exp_mul_complex hsne, norm_div, norm_neg, div_le_div_iff₀ hspos hspos]
    nlinarith [h2, hspos]
  -- the double integral in CLOSED FORM
  have hinner : ∀ v : ℝ, (∫ u in η₀..η₁, resKernel s (Real.exp u) (Real.exp v))
      = K * ((∫ u in η₀..η₁, Complex.exp (-s * (u : ℂ)))
          - ((η₁ - η₀ : ℝ) : ℂ) * Complex.exp (-s * (v : ℂ))) := by
    intro v
    rw [intervalIntegral.integral_congr (g := fun u : ℝ =>
        K * (Complex.exp (-s * (u : ℂ)) - Complex.exp (-s * (v : ℂ))))
      (fun u _ => hker u v), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, Complex.real_smul]
  have houter : (∫ v in ξ₀..ξ₁, ∫ u in η₀..η₁, resKernel s (Real.exp u) (Real.exp v))
      = K * (((ξ₁ - ξ₀ : ℝ) : ℂ) * (∫ u in η₀..η₁, Complex.exp (-s * (u : ℂ)))
          - ((η₁ - η₀ : ℝ) : ℂ) * (∫ v in ξ₀..ξ₁, Complex.exp (-s * (v : ℂ)))) := by
    rw [intervalIntegral.integral_congr (g := fun v : ℝ =>
        K * ((∫ u in η₀..η₁, Complex.exp (-s * (u : ℂ)))
          - ((η₁ - η₀ : ℝ) : ℂ) * Complex.exp (-s * (v : ℂ))))
      (fun v _ => hinner v), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const
        ((hcont.const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, Complex.real_smul]
  -- `‖K̃(−s)‖·‖s‖ ≤ C₀`, from the two denominator bounds
  have hd1 : (59 : ℝ) / 60 ≤ ‖(1 : ℂ) - s‖ := by
    have h := Complex.abs_re_le_norm ((1 : ℂ) - s)
    rw [show ((1 : ℂ) - s).re = 1 - s.re by simp,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s.re)] at h
    linarith
  have hd2 : (119 : ℝ) / 60 ≤ ‖(2 : ℂ) - s‖ := by
    have h := Complex.abs_re_le_norm ((2 : ℂ) - s)
    rw [show ((2 : ℂ) - s).re = 2 - s.re by simp,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - s.re)] at h
    linarith
  have hprod : (59 / 60 : ℝ) * (119 / 60) ≤ ‖(1 : ℂ) - s‖ * ‖(2 : ℂ) - s‖ :=
    mul_le_mul hd1 hd2 (by norm_num) (by linarith)
  have hD : (0 : ℝ) < ‖s‖ * ‖(1 : ℂ) - s‖ * ‖(2 : ℂ) - s‖ := by
    have h1 : (0 : ℝ) < ‖(1 : ℂ) - s‖ := by linarith
    have h2 : (0 : ℝ) < ‖(2 : ℂ) - s‖ := by linarith
    positivity
  have hKle : ‖K‖ ≤ 2 / ((59 / 60) * (119 / 60)) / ‖s‖ := by
    rw [hKdef, norm_div, norm_mul, norm_mul, norm_neg,
      show ‖(2 : ℂ)‖ = 2 from by norm_num, div_le_div_iff₀ hD (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hprod hspos.le, hspos]
  -- assemble
  have hIη : ‖∫ u in η₀..η₁, Complex.exp (-s * (u : ℂ))‖ ≤ 2 / ‖s‖ :=
    hnormI η₀ η₁ hη0 (by linarith)
  have hIξ : ‖∫ v in ξ₀..ξ₁, Complex.exp (-s * (v : ℂ))‖ ≤ 2 / ‖s‖ :=
    hnormI ξ₀ ξ₁ hξ0 (by linarith)
  have hsub : ‖((ξ₁ - ξ₀ : ℝ) : ℂ) * (∫ u in η₀..η₁, Complex.exp (-s * (u : ℂ)))
        - ((η₁ - η₀ : ℝ) : ℂ) * (∫ v in ξ₀..ξ₁, Complex.exp (-s * (v : ℂ)))‖
      ≤ ((ξ₁ - ξ₀) + (η₁ - η₀)) * (2 / ‖s‖) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hξd, abs_of_nonneg hηd]
    have h1 := mul_le_mul_of_nonneg_left hIη hξd
    have h2 := mul_le_mul_of_nonneg_left hIξ hηd
    linarith
  have hIm2 : (0 : ℝ) < s.im ^ 2 := by
    have hne : s.im ^ 2 ≠ 0 := pow_ne_zero 2 him
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
  have hms : s.im ^ 2 ≤ ‖s‖ ^ 2 := by
    nlinarith [Complex.abs_im_le_norm s, abs_nonneg s.im, sq_abs s.im]
  have hnn : (0 : ℝ) ≤ ((ξ₁ - ξ₀) + (η₁ - η₀)) * (2 / ‖s‖) := by positivity
  rw [houter, norm_mul]
  calc ‖K‖ * ‖((ξ₁ - ξ₀ : ℝ) : ℂ) * (∫ u in η₀..η₁, Complex.exp (-s * (u : ℂ)))
        - ((η₁ - η₀ : ℝ) : ℂ) * (∫ v in ξ₀..ξ₁, Complex.exp (-s * (v : ℂ)))‖
      ≤ ‖K‖ * (((ξ₁ - ξ₀) + (η₁ - η₀)) * (2 / ‖s‖)) :=
        mul_le_mul_of_nonneg_left hsub (norm_nonneg _)
    _ ≤ (2 / ((59 / 60) * (119 / 60)) / ‖s‖) * (((ξ₁ - ξ₀) + (η₁ - η₀)) * (2 / ‖s‖)) :=
        mul_le_mul_of_nonneg_right hKle hnn
    _ = 2 * (2 / ((59 / 60) * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀)) / ‖s‖ ^ 2 := by
        field_simp
    _ ≤ 2 * (2 / ((59 / 60) * (119 / 60))) * ((ξ₁ - ξ₀) + (η₁ - η₀)) / s.im ^ 2 :=
        div_le_div_of_nonneg_left (by linarith) hIm2 hms

/-! ## (iv) THE RATIO (W9c's headline) -/

-- **`card_system_le_rpow` is FLAGGED** (`docs/blueprints/flags.md`, node
-- `B2-W9ac-card_system_le_rpow`): the assembly's DEVICE step — moving the pointwise Halász
-- inequality `(J·S'/2)^2 ≤ A · Re Σ_{j,k} η̄_j η_k B(s̄_j + s_k; e^η, e^ξ)` under `∫_Ξ∫_H` —
-- needs `IntervalIntegrable` of the right-hand side in `(ξ, η)`, and the corpus carries no
-- integrability or continuity row for `resKernel`, `jutilaI` or `halaszBTsum` in `(N, M)`.
-- The ten inputs above are LANDED; the desk re-freezes this row with that input named.

/-- **The W9a/c exit rows** (each INVOKES a frozen row at numerals): the detector as a Dirichlet
polynomial at `(q, z₁, z₂, R, x) = (5, 4, 16, 6, 400)`, `σ = 0`, `ρ = 1/2 + 3i`; the `/b` bound
at the toy `(4, 16, 400)` with `(N, M) = (800, 4)`, `σ = 1`. -/
example (χ : DirichletCharacter ℂ 5) :
    jutilaDetector χ 4 16 6 400 ((1 / 2 : ℂ) + 3 * I)
      = Salt.MR.dirichletPolyChi (Finset.Ioc 4 ⌊(400 : ℝ)⌋₊) (jutilaA 5 4 16 6 400 0) χ
          (((1 / 2 : ℂ) + 3 * I) - (0 : ℝ)) :=
  jutilaDetector_eq_dirichletPolyChi χ 4 16 6 400 0 ((1 / 2 : ℂ) + 3 * I)

example :
    ∑ n ∈ Finset.Ioc 4 ⌊(400 : ℝ)⌋₊, ‖jutilaA 5 4 16 6 400 1 n‖ ^ 2 / jutilaB 5 6 800 4 n
      ≤ 4 * ∑ n ∈ Finset.Icc 1 ⌊(400 : ℝ)⌋₊,
          (∑ d ∈ n.divisors, bvWeight 4 16 d) ^ 2 * (n : ℝ) ^ (1 - 2 * (1 : ℝ)) :=
  sum_normSq_jutilaA_div_jutilaB_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end Salt.SW
