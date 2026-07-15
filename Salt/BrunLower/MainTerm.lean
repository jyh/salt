/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Defs

/-!
# The truncation main-term comparison (blueprint `p0`, node B3)

The `L_ν(z)` half of Halberstam–Richert's Théorème 2, *A new look at Brun's sieve*,
Mém. SMF **25** (1971) 97–106 (numdam `10.24033/msmf.39`): the derivation (2.11)→(2.17)
that turns the block-truncated main sum

  `mainSum = Σ_{d ∣ P(z)} μ(d) χ_ν(d) ω(d)/d = L_ν(z)`   (H-R (2.7); `s.nu = ω/·`)

into the frozen comparison `W(z)·(1 ± 2λ^{2b−ν+2}e^{2λ}/(1 − λ²e^{2+2λ}))`.

## The #16-critical arithmetic (the reason this node exists)

After the block partition (2.13)–(2.14) and the density inputs (2.16), the paper reaches
(top of p.105)

  `L_ν(z) = W(z)·(1 + θ·Σ_{n=1}^{r} e^{2nλ}(2nλ)^{2b−ν+2n}/(2b−ν+2n)!)`,  `|θ| ≤ 1`.

`blockTail_le` bounds that sum by `2λ^{k+2}e^{2λ}/(1 − λ²e^{2+2λ})` (`k = 2b−ν`) via:

* the factorial floor `(k+2n)! ≥ (2n)!·(2n)^k`  (`Nat.factorial_mul_pow_le_factorial`);
* the **decreasing** Stirling factor `stir m := (m/e)^m/m!`, `stir(2n) ≤ stir 2 = 2e^{-2}`
  (`stir_antitone`, from `(1+1/m)^m ≤ e`);
* the **geometric close** at ratio `q = λ²e^{2+2λ} = (λe^{1+λ})²`, which is `< 1` **exactly**
  under condition (1.2) `λe^{1+λ} < 1` — this is error #16: the ratio carries `e²` in the
  denominator (`e^{2+2λ}`, not `e^{2λ}`) and the numerator is `e^{2λ}`.

Endpoint exponents (load-bearing): upper `ν=1` gives `λ^{2b+1}`, lower `ν=2` gives `λ^{2b}`.
`mainSum` is stated with B2's coefficient system `fun d => μ d · [χ_ν d]`, so B5 consumes
these and B1/B2's plumbing without glue.

## ⚠️ Frozen-set mismatch (an #18-candidate — reported, not improvised)

The paper's (2.11)→(2.17) needs **two inputs that are NOT in `p0.md`'s frozen hypothesis set**
`{(Ω), (Ω₁), (R), the ladder, (1.2)}`, and are not free from mathlib:

1. **(2.16)** the density-ratio bound `W(z_n)/W(z) ≤ e^{2nλ}` (`n = 1,…,r`);
2. the per-block prime-sum bound `Σ_{z_n ≤ p < z} ω(p)/p ≤ 2nλ` (H-R derive it from (2.16)).

H-R discharge (2.16) on pp.104–106 from a Mertens-type estimate
`Σ_{w≤p<z} ω(p)·log p/p ≤ A(log(z/w)+1)` — a "well-known result" — together with (Ω₁), and a
final choice `Λ` (2.18) that only holds for `z` sufficiently large.  The ladder scale
`Λ = 2λ/A` (B0) is tuned precisely so `(log z/log z_n)^A = e^{nAΛ} = e^{2nλ}` comes out clean.

`p0.md`'s "frozen mathematics" section lists neither (2.16) nor its Mertens input among the
frozen hypotheses (it defers only the *W lower bound* to P1's Maynard-Mertens, not this
*W-ratio* bound).  Per Iron Rule 1 this node does NOT alter the frozen statement: it takes the
two quantities as **explicit hypotheses** (`Wr`, `ps` with `hWr`, `hps`) — an honest interface
node — and proves the #16-critical close.  **P1 must discharge `hWr`/`hps` at the twin instance
via a concrete Mertens estimate**; see `docs/blueprints/flags.md`.  (Everything upstream of the
block form — the Lemma 3 reduction / elementary-symmetric bound of (2.11) — is likewise supplied
as the decomposition hypothesis `hdecomp`; it is B2/B5 combinatorics, not tail arithmetic.)
-/

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Salt.BrunLower

open BoundingSieve

/-! ## Stirling floor block -/

/-- `stir m = (m/e)^m / m!` = `m^m e^{-m}/m!`; H-R's decreasing Stirling factor. -/
noncomputable def stir (m : ℕ) : ℝ := (m : ℝ) ^ m * Real.exp (-(m : ℝ)) / (m ! : ℝ)

lemma stir_nonneg (m : ℕ) : 0 ≤ stir m := by
  unfold stir; positivity

lemma stir_two : stir 2 = 2 * Real.exp (-2) := by
  unfold stir
  norm_num [Nat.factorial]
  ring

lemma stir_succ_le (m : ℕ) (hpos : 0 < m) : stir (m + 1) ≤ stir m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hpos
  have h1 : (1 : ℝ) + 1 / (m : ℝ) ≤ Real.exp (1 / (m : ℝ)) := by
    have := Real.add_one_le_exp (1 / (m : ℝ)); linarith
  have hstep : (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp 1 := by
    calc (1 + 1 / (m : ℝ)) ^ m ≤ (Real.exp (1 / (m : ℝ))) ^ m := by
          have hb : (0 : ℝ) ≤ 1 + 1 / (m : ℝ) := by positivity
          exact pow_le_pow_left₀ hb h1 m
      _ = Real.exp ((m : ℝ) * (1 / (m : ℝ))) := (Real.exp_nat_mul (1 / (m : ℝ)) m).symm
      _ = Real.exp 1 := by rw [mul_one_div, div_self (ne_of_gt hmpos)]
  have hfac : ((m : ℝ) + 1) ^ m = (m : ℝ) ^ m * (1 + 1 / (m : ℝ)) ^ m := by
    rw [← mul_pow]; congr 1; field_simp
  have key : ((m : ℝ) + 1) ^ m * Real.exp (-1) ≤ (m : ℝ) ^ m := by
    rw [hfac]
    calc (m : ℝ) ^ m * (1 + 1 / (m : ℝ)) ^ m * Real.exp (-1)
        ≤ (m : ℝ) ^ m * Real.exp 1 * Real.exp (-1) := by
          have hprod := mul_le_mul_of_nonneg_left hstep
            (mul_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ m) (Real.exp_pos (-1)).le)
          nlinarith [hprod]
      _ = (m : ℝ) ^ m := by
          rw [mul_assoc, ← Real.exp_add, show (1 : ℝ) + -1 = 0 by norm_num,
            Real.exp_zero, mul_one]
  -- ratio ≤ 1 and identity stir(m+1) = stir m * ratio
  have hid : stir (m + 1) = stir m * (((m : ℝ) + 1) ^ m * Real.exp (-1) / (m : ℝ) ^ m) := by
    unfold stir
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have hfacS : ((m + 1)! : ℝ) = ((m : ℝ) + 1) * (m ! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hexp : Real.exp (-((m : ℝ) + 1)) = Real.exp (-(m : ℝ)) * Real.exp (-1) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hcast, hfacS, hexp, pow_succ]
    have hmm : (m : ℝ) ^ m ≠ 0 := by positivity
    have hmf : (m ! : ℝ) ≠ 0 := by positivity
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [hid]
  have hratio : ((m : ℝ) + 1) ^ m * Real.exp (-1) / (m : ℝ) ^ m ≤ 1 :=
    (div_le_one (by positivity : (0 : ℝ) < (m : ℝ) ^ m)).mpr key
  calc stir m * (((m : ℝ) + 1) ^ m * Real.exp (-1) / (m : ℝ) ^ m)
      ≤ stir m * 1 := by apply mul_le_mul_of_nonneg_left hratio (stir_nonneg m)
    _ = stir m := mul_one _

lemma stir_antitone : Antitone stir := by
  apply antitone_nat_of_succ_le
  intro m
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    -- stir 1 ≤ stir 0
    have : stir 1 = Real.exp (-1) := by unfold stir; norm_num
    rw [this]
    have : stir 0 = 1 := by unfold stir; norm_num
    rw [this]
    exact (Real.exp_le_one_iff).mpr (by norm_num)
  · exact stir_succ_le m hpos

lemma stir_two_n_le (n : ℕ) (hn : 1 ≤ n) : stir (2 * n) ≤ 2 * Real.exp (-2) := by
  rw [← stir_two]
  exact stir_antitone (by omega : 2 ≤ 2 * n)

/-! ## Geometric tail -/

lemma geom_Icc_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ℕ) :
    ∑ n ∈ Finset.Icc 1 r, q ^ n ≤ q / (1 - q) := by
  have hIcc : Finset.Icc 1 r = Finset.Ico 1 (r + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ico]
  rw [hIcc]
  have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := r + 1) hq0 hq1
  simpa using h

/-! ## The summand bound (Stirling floor + geometric shape) -/

/-- Each block-tail summand `e^{2nλ}(2nλ)^{k+2n}/(k+2n)!` is bounded by
`2e^{-2}λ^k (λ²e^{2+2λ})^n`, via the factorial floor `(k+2n)! ≥ (2n)!(2n)^k` and the
decreasing Stirling factor `stir(2n) ≤ 2e^{-2}`.  This is H-R's step at the top of p.105. -/
lemma summand_le (k n : ℕ) (hn : 1 ≤ n) (lam : ℝ) (hlam : 0 ≤ lam) :
    Real.exp (2 * (n : ℝ) * lam) * (2 * (n : ℝ) * lam) ^ (k + 2 * n) / ((k + 2 * n)! : ℝ)
      ≤ 2 * Real.exp (-2) * lam ^ k * (lam ^ 2 * Real.exp (2 + 2 * lam)) ^ n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmRpos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  -- factorial floor, cast to ℝ
  have hfloorN : (2 * n)! * (2 * n) ^ k ≤ (k + 2 * n)! := by
    calc (2 * n)! * (2 * n) ^ k
        ≤ (2 * n)! * (2 * n + 1) ^ k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) k)
      _ ≤ (2 * n + k)! := Nat.factorial_mul_pow_le_factorial
      _ = (k + 2 * n)! := by rw [Nat.add_comm]
  have hfloor : ((2 * n)! : ℝ) * (2 * (n : ℝ)) ^ k ≤ ((k + 2 * n)! : ℝ) := by
    have : (((2 * n)! * (2 * n) ^ k : ℕ) : ℝ) ≤ (((k + 2 * n)! : ℕ) : ℝ) := by
      exact_mod_cast hfloorN
    calc ((2 * n)! : ℝ) * (2 * (n : ℝ)) ^ k
        = (((2 * n)! * (2 * n) ^ k : ℕ) : ℝ) := by push_cast [hc]; ring
      _ ≤ ((k + 2 * n)! : ℝ) := this
  have hDpos : (0 : ℝ) < ((2 * n)! : ℝ) * (2 * (n : ℝ)) ^ k := by positivity
  -- expand q^n and combine exponentials
  have hqn : (lam ^ 2 * Real.exp (2 + 2 * lam)) ^ n
      = lam ^ (2 * n) * Real.exp ((n : ℝ) * (2 + 2 * lam)) := by
    rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
  have hexp : Real.exp (-(2 * (n : ℝ))) * Real.exp ((n : ℝ) * (2 + 2 * lam))
      = Real.exp (2 * (n : ℝ) * lam) := by
    rw [← Real.exp_add]; congr 1; ring
  -- the algebraic identity after applying the floor
  have hmid : Real.exp (2 * (n : ℝ) * lam) * (2 * (n : ℝ) * lam) ^ (k + 2 * n)
        / (((2 * n)! : ℝ) * (2 * (n : ℝ)) ^ k)
      = lam ^ k * (stir (2 * n) * (lam ^ 2 * Real.exp (2 + 2 * lam)) ^ n) := by
    rw [hqn, stir, hc, ← hexp]
    have hmf : ((2 * n)! : ℝ) ≠ 0 := by positivity
    have hmk : (2 * (n : ℝ)) ^ k ≠ 0 := by positivity
    field_simp
    ring
  calc Real.exp (2 * (n : ℝ) * lam) * (2 * (n : ℝ) * lam) ^ (k + 2 * n) / ((k + 2 * n)! : ℝ)
      ≤ Real.exp (2 * (n : ℝ) * lam) * (2 * (n : ℝ) * lam) ^ (k + 2 * n)
          / (((2 * n)! : ℝ) * (2 * (n : ℝ)) ^ k) := by
        apply div_le_div_of_nonneg_left (by positivity) hDpos hfloor
    _ = lam ^ k * (stir (2 * n) * (lam ^ 2 * Real.exp (2 + 2 * lam)) ^ n) := hmid
    _ ≤ lam ^ k * (2 * Real.exp (-2) * (lam ^ 2 * Real.exp (2 + 2 * lam)) ^ n) := by
        gcongr
        · exact stir_two_n_le n hn
    _ = 2 * Real.exp (-2) * lam ^ k * (lam ^ 2 * Real.exp (2 + 2 * lam)) ^ n := by ring

/-- **The block-tail estimate** (H-R (2.11)→(2.17), the #16-critical geometric close):
the truncation block sum closes geometrically at ratio `λ²e^{2+2λ} = (λe^{1+λ})² < 1` under
condition (1.2), yielding the closed form `2λ^{k+2}e^{2λ}/(1 − λ²e^{2+2λ})`.  Here `k = 2b−ν`
(so `k+2 = 2b−ν+2`: upper `2b+1`, lower `2b`). -/
lemma blockTail_le (k r : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (h12 : lam * Real.exp (1 + lam) < 1) :
    ∑ n ∈ Finset.Icc 1 r,
        Real.exp (2 * (n : ℝ) * lam) * (2 * (n : ℝ) * lam) ^ (k + 2 * n) / ((k + 2 * n)! : ℝ)
      ≤ 2 * lam ^ (k + 2) * Real.exp (2 * lam) / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)) := by
  set q := lam ^ 2 * Real.exp (2 + 2 * lam) with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    have h0 : (0 : ℝ) ≤ lam * Real.exp (1 + lam) := by positivity
    have hlt := pow_lt_one₀ h0 h12 (two_ne_zero)
    have hsq : Real.exp (1 + lam) ^ 2 = Real.exp (2 + 2 * lam) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have heq : (lam * Real.exp (1 + lam)) ^ 2 = q := by rw [hq, mul_pow, hsq]
    rwa [heq] at hlt
  have hterm : ∀ n ∈ Finset.Icc 1 r,
      Real.exp (2 * (n : ℝ) * lam) * (2 * (n : ℝ) * lam) ^ (k + 2 * n) / ((k + 2 * n)! : ℝ)
        ≤ 2 * Real.exp (-2) * lam ^ k * q ^ n := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [hq]
    exact summand_le k n hn1 lam hlam.le
  calc ∑ n ∈ Finset.Icc 1 r,
        Real.exp (2 * (n : ℝ) * lam) * (2 * (n : ℝ) * lam) ^ (k + 2 * n) / ((k + 2 * n)! : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 r, 2 * Real.exp (-2) * lam ^ k * q ^ n := Finset.sum_le_sum hterm
    _ = 2 * Real.exp (-2) * lam ^ k * ∑ n ∈ Finset.Icc 1 r, q ^ n := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.exp (-2) * lam ^ k * (q / (1 - q)) := by
        apply mul_le_mul_of_nonneg_left (geom_Icc_le hq0.le hq1 r) (by positivity)
    _ = 2 * lam ^ (k + 2) * Real.exp (2 * lam) / (1 - q) := by
        rw [← mul_div_assoc]
        congr 1
        have he : Real.exp (-2) * Real.exp (2 + 2 * lam) = Real.exp (2 * lam) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hq]
        calc 2 * Real.exp (-2) * lam ^ k * (lam ^ 2 * Real.exp (2 + 2 * lam))
            = 2 * (lam ^ k * lam ^ 2) * (Real.exp (-2) * Real.exp (2 + 2 * lam)) := by ring
          _ = 2 * lam ^ (k + 2) * Real.exp (2 * lam) := by rw [← pow_add, he]

/-! ## The endpoint: the truncation main-term comparison (B3)

`mainSum = Σ_{d|P(z)} μ(d)χ_ν(d)ω(d)/d = L_ν(z)` (H-R (2.7); `s.nu = ω/·`).  The paper
compares `L_ν(z)` with `W(z)(1 ± tail)`.  The reduction of `L_ν(z)` to the block form
(Lemma 3 + the elementary-symmetric bound, (2.11)) and the density-ratio input
`W(z_n)/W(z) ≤ e^{2nλ}` ((2.16), discharged by Mertens on pp.104–106) are supplied as
EXPLICIT hypotheses — see the module note on the frozen-set mismatch.  What B3 proves is the
#16-critical geometric close of the block tail. -/

/-- **Upper main-term comparison** (H-R (2.17), `ν = 1`, exponent `2b+1`). -/
theorem mainSum_le_of_upper (s : BoundingSieve) {Lam z lam : ℝ} {b r : ℕ}
    (hb : 1 ≤ b) (hlam : 0 < lam) (h12 : lam * Real.exp (1 + lam) < 1)
    (Wr ps : ℕ → ℝ) (hps0 : ∀ n, 0 ≤ ps n)
    (hWr : ∀ n ∈ Finset.Icc 1 r, Wr n ≤ Real.exp (2 * (n : ℝ) * lam))
    (hps : ∀ n ∈ Finset.Icc 1 r, ps n ≤ 2 * (n : ℝ) * lam)
    (hdecomp : s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 1 b d then (1 : ℝ) else 0))
        ≤ W s * (1 + ∑ n ∈ Finset.Icc 1 r,
            Wr n * ps n ^ (2 * b - 1 + 2 * n) / ((2 * b - 1 + 2 * n)! : ℝ))) :
    s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 1 b d then (1 : ℝ) else 0))
      ≤ W s * (1 + 2 * lam ^ (2 * b + 1) * Real.exp (2 * lam)
          / (1 - lam ^ 2 * Real.exp (2 + 2 * lam))) := by
  have hk : 2 * b - 1 + 2 = 2 * b + 1 := by omega
  have hblock : ∑ n ∈ Finset.Icc 1 r,
        Wr n * ps n ^ (2 * b - 1 + 2 * n) / ((2 * b - 1 + 2 * n)! : ℝ)
      ≤ 2 * lam ^ (2 * b + 1) * Real.exp (2 * lam) / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)) := by
    calc ∑ n ∈ Finset.Icc 1 r, Wr n * ps n ^ (2 * b - 1 + 2 * n) / ((2 * b - 1 + 2 * n)! : ℝ)
        ≤ ∑ n ∈ Finset.Icc 1 r,
            Real.exp (2 * (n : ℝ) * lam) * (2 * (n : ℝ) * lam) ^ (2 * b - 1 + 2 * n)
              / ((2 * b - 1 + 2 * n)! : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have h1 := hWr n hn
          have h2 := hps n hn
          have h4 := hps0 n
          gcongr
      _ ≤ 2 * lam ^ (2 * b - 1 + 2) * Real.exp (2 * lam)
            / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)) := blockTail_le (2 * b - 1) r lam hlam h12
      _ = 2 * lam ^ (2 * b + 1) * Real.exp (2 * lam)
            / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)) := by rw [hk]
  have hWpos : 0 ≤ W s := (W_pos s).le
  calc s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 1 b d then (1 : ℝ) else 0))
      ≤ W s * (1 + ∑ n ∈ Finset.Icc 1 r,
          Wr n * ps n ^ (2 * b - 1 + 2 * n) / ((2 * b - 1 + 2 * n)! : ℝ)) := hdecomp
    _ ≤ W s * (1 + 2 * lam ^ (2 * b + 1) * Real.exp (2 * lam)
          / (1 - lam ^ 2 * Real.exp (2 + 2 * lam))) := by gcongr

/-- **Lower main-term comparison** (H-R (2.17), `ν = 2`, exponent `2b`). -/
theorem mainSum_ge_of_lower (s : BoundingSieve) {Lam z lam : ℝ} {b r : ℕ}
    (hb : 1 ≤ b) (hlam : 0 < lam) (h12 : lam * Real.exp (1 + lam) < 1)
    (Wr ps : ℕ → ℝ) (hps0 : ∀ n, 0 ≤ ps n)
    (hWr : ∀ n ∈ Finset.Icc 1 r, Wr n ≤ Real.exp (2 * (n : ℝ) * lam))
    (hps : ∀ n ∈ Finset.Icc 1 r, ps n ≤ 2 * (n : ℝ) * lam)
    (hdecomp : W s * (1 - ∑ n ∈ Finset.Icc 1 r,
            Wr n * ps n ^ (2 * b - 2 + 2 * n) / ((2 * b - 2 + 2 * n)! : ℝ))
        ≤ s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 2 b d then (1 : ℝ) else 0))) :
    W s * (1 - 2 * lam ^ (2 * b) * Real.exp (2 * lam)
          / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
      ≤ s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 2 b d then (1 : ℝ) else 0)) := by
  have hk : 2 * b - 2 + 2 = 2 * b := by omega
  have hblock : ∑ n ∈ Finset.Icc 1 r,
        Wr n * ps n ^ (2 * b - 2 + 2 * n) / ((2 * b - 2 + 2 * n)! : ℝ)
      ≤ 2 * lam ^ (2 * b) * Real.exp (2 * lam) / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)) := by
    calc ∑ n ∈ Finset.Icc 1 r, Wr n * ps n ^ (2 * b - 2 + 2 * n) / ((2 * b - 2 + 2 * n)! : ℝ)
        ≤ ∑ n ∈ Finset.Icc 1 r,
            Real.exp (2 * (n : ℝ) * lam) * (2 * (n : ℝ) * lam) ^ (2 * b - 2 + 2 * n)
              / ((2 * b - 2 + 2 * n)! : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have h1 := hWr n hn
          have h2 := hps n hn
          have h4 := hps0 n
          gcongr
      _ ≤ 2 * lam ^ (2 * b - 2 + 2) * Real.exp (2 * lam)
            / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)) := blockTail_le (2 * b - 2) r lam hlam h12
      _ = 2 * lam ^ (2 * b) * Real.exp (2 * lam)
            / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)) := by rw [hk]
  have hWpos : 0 ≤ W s := (W_pos s).le
  calc W s * (1 - 2 * lam ^ (2 * b) * Real.exp (2 * lam)
          / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
      ≤ W s * (1 - ∑ n ∈ Finset.Icc 1 r,
          Wr n * ps n ^ (2 * b - 2 + 2 * n) / ((2 * b - 2 + 2 * n)! : ℝ)) := by gcongr
    _ ≤ s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 2 b d then (1 : ℝ) else 0)) := hdecomp

end Salt.BrunLower
