/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Transfer
import Salt.HB.MixedCount

/-!
# Heath-Brown's Lemma 2, the assembly (HB-ENGINE, WP1, node HB-L2)

The transfer step `S⁽¹⁾ → S⁽²⁾` completed on the freshly-unconditional pair sieve.
`Salt.HB.Transfer` reduced Lemma 2 to bounding the **overshoot sum**
`Σ_{n∈A} ( D(n)·Λ̃(n+2) + Λ(n)·D(n+2) )` (`S2_sub_S1_le`, `D = overshoot`).  This
file consumes the `Λ̃` factor with a crude divisor bound, reorganizes the overshoot
sum into an explicit **majorant**, and states HB's (3.3) target parametrically with
the symbolic Lemma-3 **`PretenseSum`** slot.

## The three rungs (HB §3, pp.202-203)

* **Rung 1 (stone).** The crude twisted-von-Mangoldt bound
  `Λ̃(m) ≤ τ(m)·log m` (`LamTilde_le_tau_log`), read off the divisor-sum
  definition `Λ̃(m) = Σ_{d∣m} μ²(d)χ(d)log(m/d)` via `μ²(d)χ(d) ≤ 1` and
  `log(m/d) ≤ log m`.  This is the honest crude weight on the `Λ̃(n+2)` factor.

* **Rung 2 (the reorganization).** Feeding the crude bound into `S2_sub_S1_le`
  and `Λ(n) ≤ log n` gives the master transfer inequality
  `S⁽²⁾ − S⁽¹⁾ ≤ overshootMajorant χ A` (`hb_lemma2_transfer_bound`), where
  `overshootMajorant` is the explicit sum
  `Σ_{n∈A} ( D(n)·τ(n+2)log(n+2) + log n·D(n+2) )`.  Splitting `D = overshootLog +
  overshootPP` (`overshootMajorant_split`) exposes the four HB sub-sums, each
  supported on the structured exceptional `n` (the vanishing lemmas of
  `Salt.HB.Transfer`): the `log`-parts on the `χ = +1` numbers, the `PP`-parts on
  the `χ = −1` prime-power moduli `v`.

* **Rung 3 (the node).** `hb_lemma2`: the assembled transfer with HB's (3.3)-shaped
  target `C·(x/z₀ + x·(log x)⁻¹·exp(A·z₀)·PretenseSum + x^{1−δ}-junk)`, where the
  `PretenseSum χ N = Σ_{p ≤ N, χ(p)=1} log p/p` is the **symbolic Lemma-3 slot**
  (a definition, not bounded here — the `χ(p) = +1` primes enter exactly through
  the `f(n₊)` cofactor structure).  Stated as the honest reduction: the residual
  §3 estimate on `overshootMajorant` is the single named hypothesis.

## The resisting sum (named, for the next node)

The one estimate this file does NOT discharge is the analytic bound
`overshootMajorant χ A ≤ (HB (3.3) shape)`.  Its content is HB's (3.4)-(3.5): the
**fibration** of the `PP`-part by the `χ = −1` prime power `v = n₋`, the inner
pair-count via `Salt.HB.hb_lemma8'_unconditional` (at `d₁ = v`, `d₂ = 1`), and the
Mertens-grade `Σ_v Λ(v)/v`-sums producing the `exp(A z₀)·PretenseSum` factor.  That
is the campaign's remaining WP1 work (then Lemma 4 + the `S⁽³⁾` step).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the crude twisted-von-Mangoldt bound `Λ̃(m) ≤ τ(m)·log m` (rung 1) -/

/-- `μ(d)² ≤ 1` (in `ℝ`): the Möbius function is `0` or `±1`. -/
lemma moebius_sq_le_one (d : ℕ) : ((μ d : ℝ)) ^ 2 ≤ 1 := by
  rcases eq_or_ne (μ d) 0 with h | h
  · rw [h]; norm_num
  · have hsf : Squarefree d := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h
    have h1 : (μ d) ^ 2 = 1 := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
    have hcast : ((μ d : ℝ)) ^ 2 = (((μ d) ^ 2 : ℤ) : ℝ) := by push_cast; ring
    rw [hcast, h1]; norm_num

/-- The single-term bound behind the crude estimate: for `d ∣ n` (`n ≠ 0`),
    `μ²(d)·χ(d)·log(n/d) ≤ log n`. -/
lemma LamTilde_term_le (χ : DirichletCharacter ℂ q) {n d : ℕ} (hn : n ≠ 0)
    (hd : d ∈ n.divisors) :
    ((μ d : ℝ)) ^ 2 * chiRe χ d * Real.log ((n / d : ℕ) : ℝ) ≤ Real.log n := by
  obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hd
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hnd_pos : 1 ≤ n / d := Nat.one_le_div_iff hd_pos |>.mpr (Nat.le_of_dvd hn_pos hdvd)
  have hL_nonneg : 0 ≤ Real.log ((n / d : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnd_pos)
  have hL_le : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hnd_pos)
      (by exact_mod_cast Nat.div_le_self n d)
  -- `μ²(d)·χ(d) ≤ 1`
  have ha0 : 0 ≤ ((μ d : ℝ)) ^ 2 := sq_nonneg _
  have hb1 : chiRe χ d ≤ 1 := le_trans (le_abs_self _) (chiRe_abs_le_one χ d)
  have hab : ((μ d : ℝ)) ^ 2 * chiRe χ d ≤ 1 :=
    calc ((μ d : ℝ)) ^ 2 * chiRe χ d ≤ ((μ d : ℝ)) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hb1 ha0
      _ = ((μ d : ℝ)) ^ 2 := mul_one _
      _ ≤ 1 := moebius_sq_le_one d
  calc ((μ d : ℝ)) ^ 2 * chiRe χ d * Real.log ((n / d : ℕ) : ℝ)
      ≤ 1 * Real.log ((n / d : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hab hL_nonneg
    _ = Real.log ((n / d : ℕ) : ℝ) := one_mul _
    _ ≤ Real.log n := hL_le

/-- **Rung 1 — the crude bound.** `Λ̃(m) ≤ τ(m)·log m` for `m ≠ 0`, where
    `τ(m) = #divisors m`.  Read off the divisor-sum definition of `Λ̃`: every term
    `μ²(d)χ(d)log(m/d)` is `≤ log m`. -/
theorem LamTilde_le_tau_log (χ : DirichletCharacter ℂ q) {m : ℕ} (hm : m ≠ 0) :
    LamTilde χ m ≤ (m.divisors.card : ℝ) * Real.log m := by
  rw [LamTilde]
  calc ∑ d ∈ m.divisors, ((μ d : ℝ)) ^ 2 * chiRe χ d * Real.log ((m / d : ℕ) : ℝ)
      ≤ ∑ _d ∈ m.divisors, Real.log m :=
        Finset.sum_le_sum fun d hd => LamTilde_term_le χ hm hd
    _ = (m.divisors.card : ℝ) * Real.log m := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## §2 — the overshoot majorant and the master transfer inequality (rung 2) -/

/-- The crude divisor weight on the `n+2` side: `W(n) = τ(n)·log n`. -/
noncomputable def tauLog (n : ℕ) : ℝ := (n.divisors.card : ℝ) * Real.log (n : ℝ)

/-- **The overshoot majorant.**  `Σ_{n∈A} ( D(n)·τ(n+2)log(n+2) + log n·D(n+2) )`,
    `D = overshoot`.  Obtained from the transfer RHS of `S2_sub_S1_le` by the crude
    bound `Λ̃(n+2) ≤ τ(n+2)log(n+2)` (`LamTilde_le_tau_log`) and `Λ(n) ≤ log n`. -/
noncomputable def overshootMajorant (χ : DirichletCharacter ℂ q) (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (overshoot χ n * tauLog (n + 2) + Real.log (n : ℝ) * overshoot χ (n + 2))

/-- **Rung 2 — the master transfer inequality.**  Under `CoprimeSupport q A`,
    `S⁽²⁾ − S⁽¹⁾ ≤ overshootMajorant χ A`.  Combined with `S1_le_S2` this brackets the
    transfer error by an explicit sum of `overshoot` weights — the honest object HB's
    (3.3)-(3.5) then estimate. -/
theorem hb_lemma2_transfer_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {A : Finset ℕ} (hA : CoprimeSupport q A) :
    S2 χ A - S1 A ≤ overshootMajorant χ A := by
  refine le_trans (S2_sub_S1_le χ hsq hA) ?_
  refine Finset.sum_le_sum fun n _ => ?_
  have hn2 : (n + 2) ≠ 0 := by omega
  have h1 : overshoot χ n * LamTilde χ (n + 2) ≤ overshoot χ n * tauLog (n + 2) := by
    rw [tauLog]
    exact mul_le_mul_of_nonneg_left (LamTilde_le_tau_log χ hn2) (overshoot_nonneg χ hsq n)
  have h2 : Λ n * overshoot χ (n + 2) ≤ Real.log (n : ℝ) * overshoot χ (n + 2) :=
    mul_le_mul_of_nonneg_right vonMangoldt_le_log (overshoot_nonneg χ hsq (n + 2))
  exact add_le_add h1 h2

/-! ### The four HB sub-sums (the reorganization by shape)

Splitting `D = overshootLog + overshootPP` (`overshoot`'s definition) fibers the
majorant into the four HB pieces: the `log`-parts `majLog*` (carried by the
`χ = +1` numbers, `n₋ = 1`) and the prime-power parts `majPP*` (carried by the `n`
whose `χ = −1` part `n₋` is a single prime power `v`).  The vanishing lemmas of
`Salt.HB.Transfer` (`overshootLog_eq_zero_of_nMinus_ne_one`,
`overshootPP_eq_zero_of_not_isPrimePow`) are the support facts that turn each into
a sum over the exceptional set. -/

/-- `Σ_{n∈A} overshootLog(n)·τ(n+2)log(n+2)` — the `log`-part on the `n` side. -/
noncomputable def majLogL (χ : DirichletCharacter ℂ q) (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, overshootLog χ n * tauLog (n + 2)

/-- `Σ_{n∈A} overshootPP(n)·τ(n+2)log(n+2)` — the prime-power part on the `n` side. -/
noncomputable def majPPL (χ : DirichletCharacter ℂ q) (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, overshootPP χ n * tauLog (n + 2)

/-- `Σ_{n∈A} log n·overshootLog(n+2)` — the `log`-part on the `n+2` side. -/
noncomputable def majLogR (χ : DirichletCharacter ℂ q) (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, Real.log (n : ℝ) * overshootLog χ (n + 2)

/-- `Σ_{n∈A} log n·overshootPP(n+2)` — the prime-power part on the `n+2` side. -/
noncomputable def majPPR (χ : DirichletCharacter ℂ q) (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, Real.log (n : ℝ) * overshootPP χ (n + 2)

/-- **The reorganization.**  `overshootMajorant = majLogL + majPPL + majLogR + majPPR`.
    Each summand is supported on the structured exceptional `n` — HB's `L₁`-`L₄`. -/
theorem overshootMajorant_split (χ : DirichletCharacter ℂ q) (A : Finset ℕ) :
    overshootMajorant χ A = majLogL χ A + majPPL χ A + majLogR χ A + majPPR χ A := by
  rw [overshootMajorant, majLogL, majPPL, majLogR, majPPR,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [overshoot]
  ring

/-! ## §3 — the Lemma-3 slot `PretenseSum` and the assembled Lemma 2 (rung 3) -/

open Classical in
/-- **The pretense sum** `Σ_{p ≤ N, χ(p) = 1} log p / p` — the symbolic Lemma-3 slot.
    This is a *definition*, not bounded here: it is exactly where the `χ(p) = +1`
    primes enter HB's (3.4)-(3.5) (through the `f(n₊)` cofactor structure of the
    exceptional `n`).  Lemma 3 (a future node) is the estimate of this sum by the
    Siegel-zero pretense; here it is carried symbolically. -/
noncomputable def PretenseSum (χ : DirichletCharacter ℂ q) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ chiRe χ p = 1),
    Real.log (p : ℝ) / p

/-- **Rung 3 — HB 1983, Lemma 2 (assembled, parametric).**  Under `CoprimeSupport q A`,
    if the overshoot majorant obeys HB's (3.3)-shaped bound

      `overshootMajorant χ A ≤ Cmain·(x/z₀)
          + Cmain·(x/log x)·exp(Aexp·z₀)·PretenseSum χ N + junk`

    (the residual §3 estimate — the fibration of the `PP`-part by the `χ = −1` prime
    power `v`, the inner pair-count via `hb_lemma8'_unconditional`, and the
    Mertens-grade `Σ_v Λ(v)/v`-sums producing the `exp(Aexp z₀)·PretenseSum` factor),
    then the twin-sum gap satisfies the same bound:

      `S⁽²⁾ − S⁽¹⁾ ≤ Cmain·(x/z₀)
          + Cmain·(x/log x)·exp(Aexp·z₀)·PretenseSum χ N + junk`.

    The `PretenseSum χ N` factor is the symbolic Lemma-3 slot (`χ(p) = +1` primes).
    This is the honest transfer reduction: the ONLY remaining input is `hres`, the
    named resisting sum. -/
theorem hb_lemma2 (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {A : Finset ℕ}
    (hA : CoprimeSupport q A) (x : ℝ) (N : ℕ) (Cmain z0 Aexp junk : ℝ)
    (hres : overshootMajorant χ A
        ≤ Cmain * (x / z0)
          + Cmain * (x / Real.log x) * Real.exp (Aexp * z0) * PretenseSum χ N
          + junk) :
    S2 χ A - S1 A
      ≤ Cmain * (x / z0)
        + Cmain * (x / Real.log x) * Real.exp (Aexp * z0) * PretenseSum χ N
        + junk :=
  le_trans (hb_lemma2_transfer_bound χ hsq hA) hres

end Salt.HB
