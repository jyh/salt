/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.VanDerCorput

/-!
# The L9 middle band — the socket on `1 ≤ |u| ≤ N²`

`Salt/MR/VanDerCorput.lean` discharged the socket

  `‖∑_{n=1}^N exp(i·u·log n)‖ ≤ Cvdc·(N/√(1+u²) + √(1+|u|)·(1+log(2+|u|)))`

on the two **frequency corners** `|u| ≤ 1` (`halasz_socket_small`) and
`|u| ≥ N²` (`halasz_socket_large`), plus the single-block tiles
`socketBlock_kusmin` (`U ≥ u`) and `socketBlock_strip` (`U ≍ u`).  This file
attacks the **middle band** `1 ≤ |u| ≤ N²`.

## The dissolution of the inherited LITT-COVER debt

The VDC-ASM scout traced the middle band to the ExpSum track's open
`LITT-COVER` residual and warned "no single global `k` covers all dyadic
scales; the strip tile is `√U`-per-block, summing to `√t·log t`".  **The debt
does not transfer.**  `LITT-COVER` (recorded at `Salt/ExpSum/ZetaGrowth.lean`,
`zeta_partial_growth`) targets the *power-saving* Littlewood-grade bound
`‖∑_{n≤X} n^{−it}‖ ≤ C·X^{1−1/(2^k−2)}` **uniformly across all dyadic scales**,
with `k` growing by scale to reach the `ζ(1+it) ≪ log t/log log t` refinement —
a bound *strictly sharper* than the socket, one that must **remove** the log.

The socket only asks for Montgomery *Ten Lectures* (33) `Z(iu) ≪ N/|u| +
√|u|·log|u|`, which **tolerates** the log.  The `√u·log u` tail is exactly the
`log u` second-derivative blocks each contributing `√u`.  So the middle band
needs only the crude `k = 2` van der Corput test per block — **no k-window, no
global coverage.**

The concrete artifact is `zeta_block_secondDeriv` (STONE 4): the general
second-derivative block bound `‖∑_{(U,2U]} eR(phi u n)‖ ≤ 16√A + 16·U/√A`
(`A = u/2π`), valid for **every** block `U ≥ 1`, `u > 0` — this is precisely
`zeta_block_strip` with its regime-simplification (`N ≤ t ≤ 27πN`, used only to
collapse `16√A + 16U/√A` into `112√N`) **removed**.

## The regime arithmetic (the assembly, paper-math)

Fix `u ≥ 1`.  Dyadically split `[1,N]` into blocks `(2^j, 2^{j+1}]`.

* Blocks with `U ≤ u` use STONE 4: `16√A + 16U/√A ≤ (16 + 16)√A`-grade `= O(√u)`
  each (since `U/√A = U√(2π)/√u ≤ √(2π)·√u`), and there are `≤ log₂u + 1`
  of them → total `O(√u·log u)`, the socket **tail**.
* Blocks with `U > u` use `socketBlock_kusmin`: `2π(2U+1)/u`, a geometric sum
  dominated by the top `U ≈ N` → `O(N/u)`, the socket **head**.

The block **count** on the second-derivative side is `≤ log₂(min(u,N)) + 1 ≤
log₂u + 1 ≤ C(1+log(2+u))` in *both* sub-cases (`u ≤ N`: blocks with `U ≤ u`;
`u > N`: all `log₂N ≤ log₂u` blocks) — so the `u ≈ 1` corner is harmless (only
`U = 1` is a second-derivative block; every `U ≥ 2 > u` is a Kušmin/head block).
-/

noncomputable section

open Complex Finset
open scoped Real

namespace Salt.MR

open Salt.ExpSum (eR phi)

/-! ### STONE 4 — the general second-derivative block tile (no k-window)

The concrete dissolution artifact.  `Salt.Vk.zeta_block_strip` proves the same
`vdC_2nd_ZR` bound but then spends the regime `N ≤ t ≤ 27πN` to collapse
`16√A + 16U/√A` into `112√N`.  Here we keep the honest `16√A + 16U/√A`, which
holds for every block. -/

/-- **STONE 4 (corpus form).**  For every dyadic block `(U, 2U]` (`U ≥ 1`) and
every frequency `u > 0`, the ζ-phase block sum obeys the general
second-derivative bound `‖∑_{U<n≤2U} eR(phi u n)‖ ≤ 16√A + 16·U/√A` with
`A = u/2π`.  No k-window, no strip-regime hypothesis — the mild generalization
of `Salt.Vk.zeta_block_strip` that dissolves LITT-COVER for the socket. -/
theorem zeta_block_secondDeriv {u : ℝ} {U : ℕ} (hU1 : 1 ≤ U) (hu : 0 < u) :
    ‖∑ n ∈ Finset.Ioc (U : ℤ) (2 * U), eR (phi u n)‖
      ≤ 16 * Real.sqrt (u / (2 * π)) + 16 * (U : ℝ) / Real.sqrt (u / (2 * π)) := by
  have hUR1 : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU1
  have hU0R : (0 : ℝ) < (U : ℝ) := by linarith
  have hπpos : 0 < π := Real.pi_pos
  set A : ℝ := u / (2 * π) with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  set μ : ℝ := A / (4 * (U : ℝ) ^ 2) with hμ
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  -- the ζ-phase second-difference identity
  have hd2 : ∀ n : ℤ, (phi u (n + 2) - phi u (n + 1)) - (phi u (n + 1) - phi u n)
      = A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ)) := by
    intro n; simp only [Salt.ExpSum.phi, ← hA]; push_cast; ring
  -- lower second-difference bound (μ ≤ Δ²)
  have hlb : ∀ n : ℤ, (U : ℤ) < n → n < 2 * U →
      μ ≤ (phi u (n + 2) - phi u (n + 1)) - (phi u (n + 1) - phi u n) := by
    intro n hlo hhi
    rw [hd2 n]
    have hnR1 : (U : ℝ) + 1 ≤ (n : ℝ) := by
      have : (U : ℤ) + 1 ≤ n := by omega
      exact_mod_cast this
    have hmpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hll := Salt.Vk.log_2diff_lower hmpos
    have hnu : (n : ℝ) + 1 ≤ 2 * (U : ℝ) := by
      have : n + 1 ≤ 2 * (U : ℤ) := by omega
      exact_mod_cast this
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ 4 * (U : ℝ) ^ 2 := by nlinarith [hnu, hU0R]
    have hstep1 : μ ≤ A / ((n : ℝ) + 1) ^ 2 := by
      rw [hμ, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hsq, hA0.le]
    have heq2 : A / ((n : ℝ) + 1) ^ 2 = A * (1 / ((n : ℝ) + 1) ^ 2) := by ring
    have hstep2 : A / ((n : ℝ) + 1) ^ 2
        ≤ A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ)) := by
      rw [heq2]; exact mul_le_mul_of_nonneg_left hll hA0.le
    linarith [hstep1, hstep2]
  -- upper second-difference bound (Δ² ≤ 4μ)
  have hub : ∀ n : ℤ, (U : ℤ) < n → n < 2 * U →
      (phi u (n + 2) - phi u (n + 1)) - (phi u (n + 1) - phi u n) ≤ 4 * μ := by
    intro n hlo hhi
    rw [hd2 n]
    have hnR1 : (U : ℝ) + 1 ≤ (n : ℝ) := by
      have : (U : ℤ) + 1 ≤ n := by omega
      exact_mod_cast this
    have hmpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlu := Salt.Vk.log_2diff_upper hmpos
    have hUsq : (U : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 2) := by nlinarith [hnR1, hU0R]
    have heq2 : A / ((n : ℝ) * ((n : ℝ) + 2)) = A * (1 / ((n : ℝ) * ((n : ℝ) + 2))) := by ring
    have hstep1 : A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ))
        ≤ A / ((n : ℝ) * ((n : ℝ) + 2)) := by
      rw [heq2]; exact mul_le_mul_of_nonneg_left hlu hA0.le
    have h4μ : 4 * μ = A / (U : ℝ) ^ 2 := by rw [hμ]; ring
    have hstep2 : A / ((n : ℝ) * ((n : ℝ) + 2)) ≤ 4 * μ := by
      rw [h4μ, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hUsq, hA0.le]
    linarith [hstep1, hstep2]
  -- the vdC second-derivative test, then the sqrt algebra (no regime needed)
  have hab : (U : ℤ) ≤ 2 * U := by omega
  have hvdc := Salt.ExpSum.vdC_2nd_ZR (phi u) (U : ℤ) (2 * U) μ 4 hab hμ0 (by norm_num) hlb hub
  refine le_trans hvdc (le_of_eq ?_)
  have hsm : Real.sqrt μ = Real.sqrt A / (2 * (U : ℝ)) := by
    rw [hμ, show A / (4 * (U : ℝ) ^ 2) = A * (1 / (2 * (U : ℝ))) ^ 2 from by field_simp; ring,
      Real.sqrt_mul hA0.le, Real.sqrt_sq (by positivity)]
    ring
  have hsApos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA0
  have hterm1 : 4 * (U : ℝ) * Real.sqrt μ = 2 * Real.sqrt A := by rw [hsm]; field_simp; ring
  have hterm2 : 1 / Real.sqrt μ = 2 * (U : ℝ) / Real.sqrt A := by rw [hsm, one_div, inv_div]
  have hc : ((2 * (U : ℤ) : ℤ) : ℝ) - ((U : ℤ) : ℝ) = (U : ℝ) := by push_cast; ring
  rw [hc, hterm1, hterm2]
  field_simp
  ring

/-- **STONE 4 (socket form).**  The general second-derivative block tile in the
socket's `exp(i·u·log n)` shape. -/
theorem socketBlock_secondDeriv {u : ℝ} {U : ℕ} (hU1 : 1 ≤ U) (hu : 0 < u) :
    ‖∑ n ∈ Finset.Ioc (U : ℤ) (2 * U),
        Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ 16 * Real.sqrt (u / (2 * π)) + 16 * (U : ℝ) / Real.sqrt (u / (2 * π)) := by
  rw [norm_socketSum_eq_eR_int]
  exact zeta_block_secondDeriv hU1 hu

/-! ### STONE 4b — the general-endpoint second-derivative tile

The partial **top** dyadic block of `[1,N]` is `Ioc (2^J) N` with `2^J ≤ N <
2^{J+1}`, i.e. `Ioc U M` with `U ≤ M ≤ 2U` — not exactly `Ioc U (2U)`.  The
`vdC_2nd_ZR` engine is endpoint-general, so the same `16√A + 16U/√A` bound holds
for any such truncated block (`M − U ≤ U`). -/

/-- **STONE 4b (corpus form).**  General-endpoint second-derivative block bound:
for `U ≤ M ≤ 2U` (`U ≥ 1`, `u > 0`),
`‖∑_{U<n≤M} eR(phi u n)‖ ≤ 16√A + 16·U/√A` (`A = u/2π`). -/
theorem zeta_block_secondDeriv_gen {u : ℝ} {U M : ℕ}
    (hU1 : 1 ≤ U) (hUM : U ≤ M) (hM2U : M ≤ 2 * U) (hu : 0 < u) :
    ‖∑ n ∈ Finset.Ioc (U : ℤ) (M : ℤ), eR (phi u n)‖
      ≤ 16 * Real.sqrt (u / (2 * π)) + 16 * (U : ℝ) / Real.sqrt (u / (2 * π)) := by
  have hUR1 : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU1
  have hU0R : (0 : ℝ) < (U : ℝ) := by linarith
  have hπpos : 0 < π := Real.pi_pos
  set A : ℝ := u / (2 * π) with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  set μ : ℝ := A / (4 * (U : ℝ) ^ 2) with hμ
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hd2 : ∀ n : ℤ, (phi u (n + 2) - phi u (n + 1)) - (phi u (n + 1) - phi u n)
      = A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ)) := by
    intro n; simp only [Salt.ExpSum.phi, ← hA]; push_cast; ring
  have hlb : ∀ n : ℤ, (U : ℤ) < n → n < (M : ℤ) →
      μ ≤ (phi u (n + 2) - phi u (n + 1)) - (phi u (n + 1) - phi u n) := by
    intro n hlo hhi
    rw [hd2 n]
    have hnR1 : (U : ℝ) + 1 ≤ (n : ℝ) := by
      have : (U : ℤ) + 1 ≤ n := by omega
      exact_mod_cast this
    have hmpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hll := Salt.Vk.log_2diff_lower hmpos
    have hnu : (n : ℝ) + 1 ≤ 2 * (U : ℝ) := by
      have hn1 : n + 1 ≤ (M : ℤ) := by omega
      have hM2 : (M : ℤ) ≤ 2 * U := by exact_mod_cast hM2U
      have : n + 1 ≤ 2 * (U : ℤ) := le_trans hn1 hM2
      exact_mod_cast this
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ 4 * (U : ℝ) ^ 2 := by nlinarith [hnu, hU0R]
    have hstep1 : μ ≤ A / ((n : ℝ) + 1) ^ 2 := by
      rw [hμ, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hsq, hA0.le]
    have heq2 : A / ((n : ℝ) + 1) ^ 2 = A * (1 / ((n : ℝ) + 1) ^ 2) := by ring
    have hstep2 : A / ((n : ℝ) + 1) ^ 2
        ≤ A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ)) := by
      rw [heq2]; exact mul_le_mul_of_nonneg_left hll hA0.le
    linarith [hstep1, hstep2]
  have hub : ∀ n : ℤ, (U : ℤ) < n → n < (M : ℤ) →
      (phi u (n + 2) - phi u (n + 1)) - (phi u (n + 1) - phi u n) ≤ 4 * μ := by
    intro n hlo hhi
    rw [hd2 n]
    have hnR1 : (U : ℝ) + 1 ≤ (n : ℝ) := by
      have : (U : ℤ) + 1 ≤ n := by omega
      exact_mod_cast this
    have hmpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlu := Salt.Vk.log_2diff_upper hmpos
    have hUsq : (U : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 2) := by nlinarith [hnR1, hU0R]
    have heq2 : A / ((n : ℝ) * ((n : ℝ) + 2)) = A * (1 / ((n : ℝ) * ((n : ℝ) + 2))) := by ring
    have hstep1 : A * (2 * Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) + 2) - Real.log (n : ℝ))
        ≤ A / ((n : ℝ) * ((n : ℝ) + 2)) := by
      rw [heq2]; exact mul_le_mul_of_nonneg_left hlu hA0.le
    have h4μ : 4 * μ = A / (U : ℝ) ^ 2 := by rw [hμ]; ring
    have hstep2 : A / ((n : ℝ) * ((n : ℝ) + 2)) ≤ 4 * μ := by
      rw [h4μ, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hUsq, hA0.le]
    linarith [hstep1, hstep2]
  have hab : (U : ℤ) ≤ (M : ℤ) := by exact_mod_cast hUM
  have hvdc := Salt.ExpSum.vdC_2nd_ZR (phi u) (U : ℤ) (M : ℤ) μ 4 hab hμ0 (by norm_num) hlb hub
  refine le_trans hvdc ?_
  have hsm : Real.sqrt μ = Real.sqrt A / (2 * (U : ℝ)) := by
    rw [hμ, show A / (4 * (U : ℝ) ^ 2) = A * (1 / (2 * (U : ℝ))) ^ 2 from by field_simp; ring,
      Real.sqrt_mul hA0.le, Real.sqrt_sq (by positivity)]
    ring
  have hsApos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA0
  have hsμnn : 0 ≤ Real.sqrt μ := Real.sqrt_nonneg _
  -- M − U ≤ U, so 8(4(M−U)√μ + 1/√μ) ≤ 8(4U√μ + 1/√μ) = 16√A + 16U/√A
  have hMU : ((M : ℤ) : ℝ) - ((U : ℤ) : ℝ) ≤ (U : ℝ) := by
    have : (M : ℝ) ≤ 2 * (U : ℝ) := by exact_mod_cast hM2U
    push_cast; linarith
  have hstep : 8 * (4 * (((M : ℤ) : ℝ) - ((U : ℤ) : ℝ)) * Real.sqrt μ + 1 / Real.sqrt μ)
      ≤ 8 * (4 * (U : ℝ) * Real.sqrt μ + 1 / Real.sqrt μ) := by
    have := mul_le_mul_of_nonneg_right hMU hsμnn
    nlinarith [this, hsμnn]
  refine le_trans hstep (le_of_eq ?_)
  have hterm1 : 4 * (U : ℝ) * Real.sqrt μ = 2 * Real.sqrt A := by rw [hsm]; field_simp; ring
  have hterm2 : 1 / Real.sqrt μ = 2 * (U : ℝ) / Real.sqrt A := by rw [hsm, one_div, inv_div]
  rw [hterm1, hterm2]
  field_simp
  ring

/-- **STONE 4b (socket form).**  General-endpoint second-derivative block tile in
the socket's `exp(i·u·log n)` shape. -/
theorem socketBlock_secondDeriv_gen {u : ℝ} {U M : ℕ}
    (hU1 : 1 ≤ U) (hUM : U ≤ M) (hM2U : M ≤ 2 * U) (hu : 0 < u) :
    ‖∑ n ∈ Finset.Ioc (U : ℤ) (M : ℤ),
        Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ 16 * Real.sqrt (u / (2 * π)) + 16 * (U : ℝ) / Real.sqrt (u / (2 * π)) := by
  rw [norm_socketSum_eq_eR_int]
  exact zeta_block_secondDeriv_gen hU1 hUM hM2U hu

/-! ### STONE 5 — the pure second-derivative dyadic assembly (`N ≤ u`)

On the high-frequency half of the middle band, `N ≤ u`, every dyadic block
`(2^j, 2^{j+1}]` has `2^j ≤ N ≤ u`, so **every** block is a second-derivative
block (STONE 4).  No Kušmin term, no regime mixing: the socket closes from
STONE 4/4b alone.  This is the clean half of the dissolution. -/

/-- ℕ→ℤ reindex for an `eR ∘ phi` block sum (the tiles are `ℤ`-indexed; the
dyadic split machine `dyadic_sum_split_gen` is `ℕ`-indexed). -/
lemma sum_Ioc_eR_natCast (u : ℝ) (a b : ℕ) :
    ∑ n ∈ Finset.Ioc a b, eR (phi u (n : ℤ))
      = ∑ m ∈ Finset.Ioc (a : ℤ) (b : ℤ), eR (phi u m) := by
  apply Finset.sum_nbij' (i := fun n : ℕ => (n : ℤ)) (j := fun m : ℤ => m.toNat)
  · intro n hn; rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
  · intro m hm; rw [Finset.mem_Ioc] at hm ⊢; omega
  · intro n _; exact Int.toNat_natCast n
  · intro m hm; rw [Finset.mem_Ioc] at hm; omega
  · intro n _; rfl

/-- ℕ-indexed exact second-derivative block bound. -/
lemma zeta_block_secondDeriv_nat {u : ℝ} {U : ℕ} (hU1 : 1 ≤ U) (hu : 0 < u) :
    ‖∑ n ∈ Finset.Ioc U (2 * U), eR (phi u (n : ℤ))‖
      ≤ 16 * Real.sqrt (u / (2 * π)) + 16 * (U : ℝ) / Real.sqrt (u / (2 * π)) := by
  rw [sum_Ioc_eR_natCast]
  have hcast : ((2 * U : ℕ) : ℤ) = 2 * (U : ℤ) := by push_cast; ring
  rw [hcast]
  exact zeta_block_secondDeriv hU1 hu

/-- ℕ-indexed general-endpoint second-derivative block bound. -/
lemma zeta_block_secondDeriv_gen_nat {u : ℝ} {U M : ℕ}
    (hU1 : 1 ≤ U) (hUM : U ≤ M) (hM2U : M ≤ 2 * U) (hu : 0 < u) :
    ‖∑ n ∈ Finset.Ioc U M, eR (phi u (n : ℤ))‖
      ≤ 16 * Real.sqrt (u / (2 * π)) + 16 * (U : ℝ) / Real.sqrt (u / (2 * π)) := by
  rw [sum_Ioc_eR_natCast]
  exact zeta_block_secondDeriv_gen hU1 hUM hM2U hu

/-- `Nat.log 2 N ≤ log N / log 2` (the block count is `log`-grade). -/
lemma natLog2_le_log_div (N : ℕ) (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
  have h2 : (2 : ℕ) ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2pos]
  have hle : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log N := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast h2
  rwa [Real.log_pow] at hle

/-- **STONE 5 (eR core).**  The pure second-derivative dyadic assembly, `eR` form:
on `N ≤ u` (`u ≥ 1`), `‖∑_{n≤N} eR(phi u n)‖ ≤ 137·√(1+u)·(1+log(2+u))` — the
Montgomery (33) middle term, unconditionally, from STONE 4/4b alone. -/
theorem halasz_socketEr_midHigh (N : ℕ) (u : ℝ)
    (hN1 : 1 ≤ N) (hu1 : 1 ≤ u) (hNu : (N : ℝ) ≤ u) :
    ‖∑ n ∈ Finset.Icc 1 N, eR (phi u (n : ℤ))‖
      ≤ 137 * (Real.sqrt (1 + u) * (1 + Real.log (2 + u))) := by
  have hupos : 0 < u := by linarith
  have hπpos : 0 < π := Real.pi_pos
  set S : ℝ := Real.sqrt (u / (2 * π)) with hS
  have hS0 : 0 < S := by rw [hS]; exact Real.sqrt_pos.mpr (div_pos hupos (by positivity))
  set T : ℝ := Real.sqrt (1 + u) * (1 + Real.log (2 + u)) with hT
  set J : ℕ := Nat.log 2 N with hJdef
  have hN0 : N ≠ 0 := by omega
  have hJN : 2 ^ J ≤ N := by rw [hJdef]; exact Nat.pow_log_le_self 2 hN0
  have hNJ : N < 2 ^ (J + 1) := by rw [hJdef]; exact Nat.lt_pow_succ_log_self (by norm_num) N
  have hpow : (2 : ℕ) ^ (J + 1) = 2 * 2 ^ J := by rw [pow_succ]; ring
  have hlognn : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
  -- Sub-bound A: S = √(u/2π) ≤ √(1+u)
  have hSle : S ≤ Real.sqrt (1 + u) := by
    rw [hS]; apply Real.sqrt_le_sqrt
    have h2pi1 : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    have hdiv : u / (2 * π) ≤ u := div_le_self (by linarith) h2pi1
    linarith
  -- Sub-bound B: 1 ≤ T
  have h_one : (1 : ℝ) ≤ T := by
    rw [hT]
    have h1 : (1 : ℝ) ≤ Real.sqrt (1 + u) := by
      have hh : Real.sqrt 1 ≤ Real.sqrt (1 + u) := Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_one] at hh
    have h2 : (1 : ℝ) ≤ 1 + Real.log (2 + u) := by linarith
    have hm := mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg (1 + u))
    linarith [hm]
  -- Sub-bound C: the block count J+1 is log-grade
  have hJ1 : (J : ℝ) + 1 ≤ 2.5 * (1 + Real.log (2 + u)) := by
    have hJlog' : (J : ℝ) * Real.log 2 ≤ Real.log (2 + u) := by
      have hstep : Real.log ((2 : ℝ) ^ J) ≤ Real.log (2 + u) := by
        apply Real.log_le_log (by positivity)
        calc ((2 : ℝ) ^ J) = ((2 ^ J : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (N : ℝ) := by exact_mod_cast hJN
          _ ≤ 2 + u := by linarith
      rwa [Real.log_pow] at hstep
    have hlog2big : (2 / 3 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    nlinarith [hJlog', hlognn,
      mul_nonneg (show (0 : ℝ) ≤ (J : ℝ) by positivity)
        (show (0 : ℝ) ≤ Real.log 2 - 2 / 3 by linarith [hlog2big])]
  -- Sub-bound D: N/S ≤ 3√(1+u)
  have hNSle : (N : ℝ) / S ≤ 3 * Real.sqrt (1 + u) := by
    have hS2 : S ^ 2 = u / (2 * π) := by
      rw [hS]; exact Real.sq_sqrt (div_nonneg hupos.le (by positivity))
    have h2pi9 : 2 * π ≤ 9 := by nlinarith [Real.pi_le_four]
    have hN2u2 : (N : ℝ) ^ 2 ≤ u ^ 2 := by
      nlinarith [hNu, Nat.cast_nonneg (α := ℝ) N, hupos.le]
    have key : 2 * π * (N : ℝ) ^ 2 ≤ 9 * (1 + u) * u := by
      nlinarith [hN2u2, hupos, Real.pi_pos, h2pi9,
        mul_nonneg (show (0 : ℝ) ≤ 2 * π by positivity)
          (show (0 : ℝ) ≤ u ^ 2 - (N : ℝ) ^ 2 by linarith [hN2u2]),
        mul_nonneg (show (0 : ℝ) ≤ 9 - 2 * π by linarith [h2pi9]) (sq_nonneg u)]
    have hsq : ((N : ℝ) / S) ^ 2 ≤ (3 * Real.sqrt (1 + u)) ^ 2 := by
      rw [div_pow, hS2, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + u),
        div_le_iff₀ (div_pos hupos (by positivity))]
      have hrw : (3 : ℝ) ^ 2 * (1 + u) * (u / (2 * π)) = 9 * (1 + u) * u / (2 * π) := by ring
      rw [hrw, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)]
      nlinarith [key]
    have h1 : (0 : ℝ) ≤ (N : ℝ) / S := div_nonneg (Nat.cast_nonneg N) hS0.le
    have h2 : (0 : ℝ) ≤ 3 * Real.sqrt (1 + u) := by positivity
    calc (N : ℝ) / S = Real.sqrt (((N : ℝ) / S) ^ 2) := (Real.sqrt_sq h1).symm
      _ ≤ Real.sqrt ((3 * Real.sqrt (1 + u)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 3 * Real.sqrt (1 + u) := Real.sqrt_sq h2
  -- Sub-bound E: the √A-count contribution
  have h_sj : 16 * S * ((J : ℝ) + 1) ≤ 40 * T := by
    have hprod : S * ((J : ℝ) + 1) ≤ Real.sqrt (1 + u) * (2.5 * (1 + Real.log (2 + u))) :=
      mul_le_mul hSle hJ1 (by positivity) (Real.sqrt_nonneg _)
    have h16 := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 16)
    have hTdef : 40 * T = 16 * (Real.sqrt (1 + u) * (2.5 * (1 + Real.log (2 + u)))) := by
      rw [hT]; ring
    have e : 16 * S * ((J : ℝ) + 1) = 16 * (S * ((J : ℝ) + 1)) := by ring
    rw [hTdef, e]; exact h16
  -- Sub-bound F: the geometric contribution
  have h_geo : 32 * (2 : ℝ) ^ J / S ≤ 96 * T := by
    have h2JN : (2 : ℝ) ^ J ≤ (N : ℝ) := by exact_mod_cast hJN
    have step1 : 32 * (2 : ℝ) ^ J / S ≤ 32 * (N : ℝ) / S := by
      rw [div_eq_mul_one_div (32 * (2 : ℝ) ^ J) S, div_eq_mul_one_div (32 * (N : ℝ)) S]
      exact mul_le_mul_of_nonneg_right (by linarith [h2JN]) (le_of_lt (one_div_pos.mpr hS0))
    have step2 : 32 * (N : ℝ) / S ≤ 96 * Real.sqrt (1 + u) := by
      have h := mul_le_mul_of_nonneg_left hNSle (by norm_num : (0 : ℝ) ≤ 32)
      have e1 : 32 * (N : ℝ) / S = 32 * ((N : ℝ) / S) := by ring
      have e2 : 32 * (3 * Real.sqrt (1 + u)) = 96 * Real.sqrt (1 + u) := by ring
      rw [e1, ← e2]; exact h
    have hTge : Real.sqrt (1 + u) ≤ T := by
      rw [hT]; exact le_mul_of_one_le_right (Real.sqrt_nonneg _) (by linarith)
    have step3 : 96 * Real.sqrt (1 + u) ≤ 96 * T := mul_le_mul_of_nonneg_left hTge (by norm_num)
    linarith [step1, step2, step3]
  -- Per-block bounds
  have hblock : ∀ j ∈ Finset.range J,
      ‖∑ n ∈ Finset.Ioc (2 ^ j : ℕ) (2 ^ (j + 1)), eR (phi u (n : ℤ))‖
        ≤ 16 * S + 16 * (2 : ℝ) ^ j / S := by
    intro j _
    have hpj : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    have hb := zeta_block_secondDeriv_gen_nat (U := 2 ^ j) (M := 2 ^ (j + 1))
      (Nat.one_le_pow j 2 (by norm_num))
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)) hpj.le hupos
    rw [← hS] at hb
    have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
    rw [hcast] at hb; exact hb
  have hPp : ‖∑ n ∈ Finset.Ioc (2 ^ J) N, eR (phi u (n : ℤ))‖
      ≤ 16 * S + 16 * (2 : ℝ) ^ J / S := by
    have hM2U : N ≤ 2 * 2 ^ J := by have h := hNJ; rw [hpow] at h; omega
    have hb := zeta_block_secondDeriv_gen_nat (U := 2 ^ J) (M := N)
      (Nat.one_le_pow J 2 (by norm_num)) hJN hM2U hupos
    rw [← hS] at hb
    have hcast : ((2 ^ J : ℕ) : ℝ) = (2 : ℝ) ^ J := by push_cast; ring
    rw [hcast] at hb; exact hb
  have hP0 : ‖∑ n ∈ Finset.Ioc 0 1, eR (phi u (n : ℤ))‖ ≤ 1 := by
    refine le_trans (norm_sum_le _ _) ?_
    have hval : ∑ n ∈ Finset.Ioc 0 1, ‖eR (phi u (n : ℤ))‖ = 1 := by
      rw [Finset.sum_congr rfl (fun n _ => Salt.ExpSum.norm_eR _)]; simp
    exact le_of_eq hval
  have hPb : ‖∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ioc (2 ^ j : ℕ) (2 ^ (j + 1)), eR (phi u (n : ℤ))‖
      ≤ (J : ℝ) * (16 * S) + 16 * (2 : ℝ) ^ J / S := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum hblock) ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsm : ∑ j ∈ Finset.range J, 16 * (2 : ℝ) ^ j / S
        = 16 / S * ∑ j ∈ Finset.range J, (2 : ℝ) ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    have hgeb : ∑ j ∈ Finset.range J, (2 : ℝ) ^ j ≤ (2 : ℝ) ^ J := by
      have hg := geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) J
      rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, div_one]
      have h1J : (1 : ℝ) ≤ (2 : ℝ) ^ J := by exact_mod_cast Nat.one_le_pow J 2 (by norm_num)
      linarith
    have hfin : ∑ j ∈ Finset.range J, 16 * (2 : ℝ) ^ j / S ≤ 16 * (2 : ℝ) ^ J / S := by
      rw [hsm]
      have h16S : (0 : ℝ) ≤ 16 / S := le_of_lt (div_pos (by norm_num) hS0)
      have hmul := mul_le_mul_of_nonneg_left hgeb h16S
      calc 16 / S * ∑ j ∈ Finset.range J, (2 : ℝ) ^ j ≤ 16 / S * (2 : ℝ) ^ J := hmul
        _ = 16 * (2 : ℝ) ^ J / S := by ring
    linarith [hfin]
  -- Assemble: {1} + dyadic blocks + partial top block
  rw [show Finset.Icc 1 N = Finset.Ioc 0 N from by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
  have hsplit1 : ∑ n ∈ Finset.Ioc 0 N, eR (phi u (n : ℤ))
      = (∑ n ∈ Finset.Ioc 0 1, eR (phi u (n : ℤ)))
        + (∑ n ∈ Finset.Ioc 1 N, eR (phi u (n : ℤ))) :=
    (Finset.sum_Ioc_consecutive _ (show (0 : ℕ) ≤ 1 by omega) (show (1 : ℕ) ≤ N by omega)).symm
  have hsplit2 : ∑ n ∈ Finset.Ioc 1 N, eR (phi u (n : ℤ))
      = (∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ J), eR (phi u (n : ℤ)))
        + (∑ n ∈ Finset.Ioc (2 ^ J) N, eR (phi u (n : ℤ))) :=
    (Finset.sum_Ioc_consecutive _ (Nat.one_le_pow J 2 (by norm_num)) hJN).symm
  have hsplit3 : ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ J), eR (phi u (n : ℤ))
      = ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2 ^ j : ℕ) (2 ^ (j + 1)), eR (phi u (n : ℤ)) := by
    have hd := Salt.ExpSum.dyadic_sum_split_gen (fun n => eR (phi u (n : ℤ))) 1 J
    simpa only [mul_one] using hd
  rw [hsplit1, hsplit2, hsplit3]
  set A0 := ∑ n ∈ Finset.Ioc 0 1, eR (phi u (n : ℤ)) with hA0def
  set Ab := ∑ j ∈ Finset.range J,
    ∑ n ∈ Finset.Ioc (2 ^ j : ℕ) (2 ^ (j + 1)), eR (phi u (n : ℤ)) with hAbdef
  set Ap := ∑ n ∈ Finset.Ioc (2 ^ J) N, eR (phi u (n : ℤ)) with hApdef
  calc ‖A0 + (Ab + Ap)‖
      ≤ ‖A0‖ + ‖Ab + Ap‖ := norm_add_le _ _
    _ ≤ ‖A0‖ + (‖Ab‖ + ‖Ap‖) := by linarith [norm_add_le Ab Ap]
    _ ≤ 1 + (((J : ℝ) * (16 * S) + 16 * (2 : ℝ) ^ J / S) + (16 * S + 16 * (2 : ℝ) ^ J / S)) :=
        add_le_add hP0 (add_le_add hPb hPp)
    _ = 1 + 16 * S * ((J : ℝ) + 1) + 32 * (2 : ℝ) ^ J / S := by ring
    _ ≤ 137 * T := by linarith [h_one, h_sj, h_geo]

/-- **STONE 5 (socket form).**  The middle-band socket, discharged **unconditionally**
on the high-frequency half `N ≤ u` (`u ≥ 1`): the socket's honest-log RHS holds
with `Cvdc = 137`, from the second-derivative tiles alone (no LITT-COVER).  Together
with `halasz_socket_small` (`|u| ≤ 1`) and `halasz_socket_large` (`|u| ≥ N²`) this
closes the entire `|u| ≥ N` regime; the mixed low band `1 ≤ u < N` (which adds the
geometric Kušmin sum) is the remaining residual. -/
theorem halasz_socket_midHigh (N : ℕ) (u : ℝ)
    (hN1 : 1 ≤ N) (hu1 : 1 ≤ u) (hNu : (N : ℝ) ≤ u) :
    ‖∑ n ∈ Finset.Icc 1 N, Complex.exp (Complex.I * (u : ℂ) * (Real.log (n : ℝ) : ℂ))‖
      ≤ 137 * ((N : ℝ) / Real.sqrt (1 + u ^ 2)
          + Real.sqrt (1 + u) * (1 + Real.log (2 + u))) := by
  rw [norm_socketSum_eq_eR]
  refine le_trans (halasz_socketEr_midHigh N u hN1 hu1 hNu) ?_
  have hhead : 0 ≤ (N : ℝ) / Real.sqrt (1 + u ^ 2) :=
    div_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _)
  linarith [hhead]

end Salt.MR
