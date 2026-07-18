/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.TwistChainC

/-!
# Heath-Brown's Lemma 2: the `S⁽¹⁾ → S⁽²⁾` transfer (HB-ENGINE, WP1, node HB-L2)

Formalizes the twin-specialized transfer step of Heath-Brown 1983 §3 (Lemma 2,
statement p.198, proof pp.201-203).  With `l₁ = n`, `l₂ = n + 2`, `q` the character
modulus, and a support set `A` of integers `n` with `n` and `n + 2` both coprime to
`q`, the two sums are

* `S⁽¹⁾ = Σ_{n ∈ A} Λ(n)·Λ(n+2)`  (`S1`), and
* `S⁽²⁾ = Σ_{n ∈ A} Λ̃(n)·Λ̃(n+2)` (`S2 χ`),

built from the genuine and the twisted von Mangoldt functions of `Salt.HB.TwistChain`.

## The transfer (rung 1 — the termwise stone)

The engine is the elementary termwise algebra
`Λ̃(n)Λ̃(n+2) − Λ(n)Λ(n+2) = (Λ̃−Λ)(n)·Λ̃(n+2) + Λ(n)·(Λ̃−Λ)(n+2)` together with the
two landed halves of Lemma 1:

* **Lemma 1(b)** `Λ ≤ Λ̃` (`vonMangoldt_le_LamTilde`), giving `0 ≤ Λ̃` and the
  termwise nonnegativity `Λ(n)Λ(n+2) ≤ Λ̃(n)Λ̃(n+2)`, hence `S⁽¹⁾ ≤ S⁽²⁾`; and
* **Lemma 1(c)** `Λ̃(n) − Λ(n) ≤ 2( f(n)·log n + (f(n₊) − 1)·Λ(n₋) )`
  (`LamTilde_sub_vonMangoldt_le`), the **overshoot** majorant `D(n)` (`overshoot`).

Combining them yields the one-sided-both-ways transfer inequality
`0 ≤ S⁽²⁾ − S⁽¹⁾ ≤ Σ_{n ∈ A} ( D(n)·Λ̃(n+2) + Λ(n)·D(n+2) )` — the honest Lean
target of the freeze (`S1_le_S2`, `S2_sub_S1_le`).  The overshoot splits into the
`log`-part `2 f(n) log n` (`overshootLog`) and the prime-power part
`2 (f(n₊) − 1) Λ(n₋)` (`overshootPP`); these are the two objects the WP1/WP2
exceptional-set analysis and the pair-sieve (Lemma 8) must consume — see the
roughness note in the module tail.

## Scope

This file is **rung 1**: the transfer inequality reducing Lemma 2 to bounding the
overshoot sum.  The exceptional-set decomposition (HB's `L₁`–`L₄`) and the pair-sum
consumption via `Salt.HB.hb_lemma8` (rung 2, with the `φ(d₁d₂)`/roughness residual)
are downstream; the roughness-hypothesis finding is recorded in the tail comment.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — the overshoot majorant `D(n)` and its pieces -/

/-- The `log`-part of the Lemma-1(c) overshoot: `2·f(n)·log n`.  Nonzero only on
    `χ = +1` numbers (`n₋ = 1`), since `f(n) = 0` once a `χ(p) = −1` prime divides `n`. -/
noncomputable def overshootLog (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  2 * fChiSum χ n * Real.log n

/-- The prime-power part of the Lemma-1(c) overshoot: `2·(f(n₊) − 1)·Λ(n₋)`.  Nonzero
    only when `n₋` is a prime power (`Λ(n₋) ≠ 0`) and `n₊ > 1` (`f(n₊) > 1`). -/
noncomputable def overshootPP (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  2 * (fChiSum χ (nPlus χ n) - 1) * Λ (nMinus χ n)

/-- The Lemma-1(c) overshoot majorant `D(n) = 2·( f(n)·log n + (f(n₊) − 1)·Λ(n₋) )`,
    i.e. `overshootLog + overshootPP`. -/
noncomputable def overshoot (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  overshootLog χ n + overshootPP χ n

lemma overshoot_eq (χ : DirichletCharacter ℂ q) (n : ℕ) :
    overshoot χ n
      = 2 * (fChiSum χ n * Real.log n + (fChiSum χ (nPlus χ n) - 1) * Λ (nMinus χ n)) := by
  unfold overshoot overshootLog overshootPP; ring

lemma overshootLog_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ overshootLog χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [overshootLog]
  · have hlogn : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    have hFn : 0 ≤ fChiSum χ n := by rw [← fChiArith_eq_fChiSum]; exact fChiArith_nonneg χ hsq n
    unfold overshootLog
    rw [mul_assoc]
    exact mul_nonneg (by norm_num) (mul_nonneg hFn hlogn)

lemma overshootPP_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ overshootPP χ n := by
  have hFP1 : 0 ≤ fChiSum χ (nPlus χ n) - 1 := by linarith [one_le_fChiSum_nPlus χ hsq n]
  unfold overshootPP
  rw [mul_assoc]
  exact mul_nonneg (by norm_num) (mul_nonneg hFP1 vonMangoldt_nonneg)

lemma overshoot_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ overshoot χ n :=
  add_nonneg (overshootLog_nonneg χ hsq n) (overshootPP_nonneg χ hsq n)

/-- Restatement of Lemma 1(c) in terms of the `overshoot` majorant. -/
lemma LamTilde_sub_le_overshoot (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n ≠ 0) (hcop : Nat.Coprime n q) : LamTilde χ n - Λ n ≤ overshoot χ n := by
  rw [overshoot_eq]; exact LamTilde_sub_vonMangoldt_le χ hsq hn hcop

/-- `Λ̃ ≥ 0` everywhere (from Lemma 1(b) `Λ ≤ Λ̃` and `Λ ≥ 0`). -/
lemma LamTilde_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ LamTilde χ n :=
  le_trans vonMangoldt_nonneg (vonMangoldt_le_LamTilde χ hsq n)

/-! ## §1 — support analysis of the overshoot (the decomposition: which `n` contribute)

The two overshoot pieces are supported on structured factorizations, so the overshoot
sum of §3 is really indexed by the exceptional `n`:

* `overshootLog(n) = 2 f(n) log n` vanishes once any `χ(p) = −1` prime divides `n`
  (`f(n) = 0`), so it is carried only by the `χ = +1` numbers `n = n₊`;
* `overshootPP(n) = 2(f(n₊) − 1)·Λ(n₋)` vanishes unless `n₋` is a prime power, so it is
  carried only by `n = n₊·n₋` with `n₋` a `χ = −1` prime power — the shape of HB's
  `L₂`–`L₄` exceptional sets (p.202). -/

/-- **Support of `overshootLog`.**  `overshootLog(n) = 0` whenever `n₋ ≠ 1`, i.e. whenever
    some prime factor of `n` has `χ(p) = −1` (then `f(n) = 0`).  So the `log`-part of the
    overshoot is carried only by `χ = +1` numbers. -/
lemma overshootLog_eq_zero_of_nMinus_ne_one (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {n : ℕ} (hn : n ≠ 0) (hcop : Nat.Coprime n q) (hM : nMinus χ n ≠ 1) :
    overshootLog χ n = 0 := by
  unfold overshootLog
  rw [fChiSum_n_eq_zero χ hsq hn hcop hM]; ring

/-- **Support of `overshootPP`.**  `overshootPP(n) = 0` whenever `n₋` is not a prime power
    (then `Λ(n₋) = 0`).  So the prime-power part of the overshoot is carried only by
    `n` whose `χ = −1` part `n₋` is a single prime power — HB's `L₂`–`L₄` shapes. -/
lemma overshootPP_eq_zero_of_not_isPrimePow (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hM : ¬ IsPrimePow (nMinus χ n)) : overshootPP χ n = 0 := by
  unfold overshootPP
  rw [vonMangoldt_eq_zero_iff.mpr hM, mul_zero]

/-! ## §2 — the termwise transfer bound -/

/-- **Termwise nonnegativity.**  `Λ(n)Λ(n+2) ≤ Λ̃(n)Λ̃(n+2)` for `n, n+2` coprime to `q`
    (in fact from Lemma 1(b) alone; the coprimality is not needed but is threaded to
    match the summed form). -/
lemma twin_termwise_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    Λ n * Λ (n + 2) ≤ LamTilde χ n * LamTilde χ (n + 2) := by
  have hid : LamTilde χ n * LamTilde χ (n + 2) - Λ n * Λ (n + 2)
      = (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
        + Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) := by ring
  have h1 : 0 ≤ (LamTilde χ n - Λ n) * LamTilde χ (n + 2) :=
    mul_nonneg (by linarith [vonMangoldt_le_LamTilde χ hsq n]) (LamTilde_nonneg χ hsq (n + 2))
  have h2 : 0 ≤ Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) :=
    mul_nonneg vonMangoldt_nonneg (by linarith [vonMangoldt_le_LamTilde χ hsq (n + 2)])
  linarith [hid, h1, h2]

/-- **The termwise transfer bound (HB §3, step (ii)).**  For `n` and `n + 2` both coprime
    to `q`,
    `Λ̃(n)Λ̃(n+2) − Λ(n)Λ(n+2) ≤ D(n)·Λ̃(n+2) + Λ(n)·D(n+2)`,
    where `D = overshoot` is the Lemma-1(c) majorant. -/
lemma twin_termwise_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n ≠ 0) (hcop : Nat.Coprime n q) (hcop2 : Nat.Coprime (n + 2) q) :
    LamTilde χ n * LamTilde χ (n + 2) - Λ n * Λ (n + 2)
      ≤ overshoot χ n * LamTilde χ (n + 2) + Λ n * overshoot χ (n + 2) := by
  have hn2 : n + 2 ≠ 0 := by omega
  have hid : LamTilde χ n * LamTilde χ (n + 2) - Λ n * Λ (n + 2)
      = (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
        + Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) := by ring
  rw [hid]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (LamTilde_sub_le_overshoot χ hsq hn hcop)
      (LamTilde_nonneg χ hsq (n + 2))
  · exact mul_le_mul_of_nonneg_left (LamTilde_sub_le_overshoot χ hsq hn2 hcop2)
      vonMangoldt_nonneg

/-! ## §3 — the summed transfer inequality (Lemma 2, rung 1) -/

/-- `S⁽¹⁾ = Σ_{n ∈ A} Λ(n)·Λ(n+2)` — the genuine twin von-Mangoldt sum. -/
noncomputable def S1 (A : Finset ℕ) : ℝ := ∑ n ∈ A, Λ n * Λ (n + 2)

/-- `S⁽²⁾ = Σ_{n ∈ A} Λ̃(n)·Λ̃(n+2)` — the twisted twin von-Mangoldt sum. -/
noncomputable def S2 (χ : DirichletCharacter ℂ q) (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, LamTilde χ n * LamTilde χ (n + 2)

/-- The support-coprimality predicate: every `n ∈ A` is nonzero with `n` and `n + 2`
    both coprime to `q`.  The honest hypothesis under which Lemma 1(c) applies to both
    `n` and `n + 2`; supplied by HB's `(n(n+2), qP) = 1` support (`coprimeSupport_window`). -/
def CoprimeSupport (q : ℕ) (A : Finset ℕ) : Prop :=
  ∀ n ∈ A, n ≠ 0 ∧ Nat.Coprime n q ∧ Nat.Coprime (n + 2) q

/-- **Lemma 2, lower half.**  `S⁽¹⁾ ≤ S⁽²⁾` (termwise, from Lemma 1(b)). -/
theorem S1_le_S2 (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (A : Finset ℕ) :
    S1 A ≤ S2 χ A := by
  unfold S1 S2
  exact Finset.sum_le_sum fun n _ => twin_termwise_nonneg χ hsq n

/-- **Lemma 2, the transfer inequality (rung 1).**  Under `CoprimeSupport q A`,
    `S⁽²⁾ − S⁽¹⁾ ≤ Σ_{n ∈ A} ( D(n)·Λ̃(n+2) + Λ(n)·D(n+2) )`, `D = overshoot`.
    Together with `S1_le_S2` this is the one-sided-both-ways honest target of the
    freeze; the RHS overshoot sum is what rung 2 (the exceptional-set decomposition
    + the pair sieve `hb_lemma8`) must bound. -/
theorem S2_sub_S1_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {A : Finset ℕ}
    (hA : CoprimeSupport q A) :
    S2 χ A - S1 A
      ≤ ∑ n ∈ A, (overshoot χ n * LamTilde χ (n + 2) + Λ n * overshoot χ (n + 2)) := by
  unfold S1 S2
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨hn0, hc1, hc2⟩ := hA n hn
  exact twin_termwise_le χ hsq hn0 hc1 hc2

/-- The overshoot sum is itself nonnegative, so the transfer error is genuinely a
    one-sided majorant: `0 ≤ S⁽²⁾ − S⁽¹⁾ ≤ (overshoot sum)`. -/
theorem overshoot_sum_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (A : Finset ℕ) :
    0 ≤ ∑ n ∈ A, (overshoot χ n * LamTilde χ (n + 2) + Λ n * overshoot χ (n + 2)) := by
  refine Finset.sum_nonneg fun n hn => ?_
  exact add_nonneg (mul_nonneg (overshoot_nonneg χ hsq n) (LamTilde_nonneg χ hsq (n + 2)))
    (mul_nonneg vonMangoldt_nonneg (overshoot_nonneg χ hsq (n + 2)))

/-! ## §4 — the concrete HB support feeds `CoprimeSupport` -/

/-- Any window `(x, 2x]` filtered by coprimality of `n(n+2)` to a multiple `m` of `q`
    is a `CoprimeSupport`.  This is exactly how HB's support condition `(n(n+2), qP) = 1`
    (with `m = q·P`) feeds the transfer: coprimality to `q·P` forces coprimality to `q`,
    hence to each of `n` and `n + 2`. -/
lemma coprimeSupport_window (x m : ℕ) (hqm : q ∣ m) :
    CoprimeSupport q ((Finset.Ioc x (2 * x)).filter (fun n => Nat.Coprime (n * (n + 2)) m)) := by
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Ioc] at hn
  obtain ⟨⟨hlt, _⟩, hcop⟩ := hn
  have hn0 : n ≠ 0 := by omega
  have hcq : Nat.Coprime (n * (n + 2)) q := Nat.Coprime.coprime_dvd_right hqm hcop
  exact ⟨hn0, Nat.Coprime.coprime_dvd_left (dvd_mul_right n (n + 2)) hcq,
    Nat.Coprime.coprime_dvd_left (dvd_mul_left (n + 2) n) hcq⟩

end Salt.HB
