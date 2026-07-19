/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cCore

/-!
# HB-L2c family estimates — Wave 2a (node HB-L2c, Horn A keystone)

The **left overshoot** half of the exact-overshoot surgery.  `Salt.HB.L2cCore`
(Wave 1) landed the exact identity `S⁽²⁾ − S⁽¹⁾ = Σ_{n∈W} overshootExact χ n` and the
per-term split

`overshootExact χ n = (Λ̃−Λ)(n)·Λ̃(n+2) + Λ(n)·(Λ̃−Λ)(n+2)`.

This file (Wave 2a) is the single writer of the **left** family sum

`E_L := Σ_{n∈W} (Λ̃−Λ)(n)·Λ̃(n+2)`

(`EL`).  The right half `E_R` is Wave 2b (`Salt.HB.L2cER`); the master assembly is
Wave 3 (`Salt.HB.L2cMaster`).

## What this file lands (the reduction layer)

The genuinely-provable structural spine that the family analysis plugs into:

* `EL` and its nonnegativity (`EL_nonneg`, `lamTilde_nonneg`) — both factors are `≥ 0`
  by Lemma 1(b) (`vonMangoldt_le_LamTilde`).
* The **window-hypothesis extractors** (`l2cWindow_ne_zero`, `_coprime`,
  `_coprime_add_two`, `_le`, `_add_two_le`, `_rough`, `_rough_add_two`): from
  `n ∈ l2cWindow χ z x` recover exactly the hypothesis packet consumed by the caps and
  by every family fibration.
* The **sharp single-block cap** `lamTilde_single_block_le`: on the window, when
  `(n+2)₋` is a prime power `w`, `Λ̃(n+2) ≤ e^{(log2)z₀}·Λ(w)` — the honest weight that
  keeps the `Λ(w)` block for the `n+2`-side pair-count fibration (the sharp analogue of
  `L2cCore.lamTilde_cap`, which crudely drops `Λ(w) ≤ L'`).
* The **crude `n+2` cap reduction** `EL_le_cap`: `E_L ≤ e^{(log2)z₀}·L'·Σ_{n∈W}(Λ̃−Λ)(n)`
  (the `:293` all-plus route), and the support restriction `leftOvershoot_support`.

See the module NOTES block below for the residual family-budget interface
(`EL_T1_bound` … `EL_corners_bound`) that Wave 3 consumes — those are the frozen
`J1/J2/junkExpr` shapes whose full pair-count fibration is recorded as a named residual.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — the left family sum and its nonnegativity -/

/-- `Λ̃(n) ≥ 0` (Lemma 1(b): `Λ(n) ≤ Λ̃(n)` and `Λ(n) ≥ 0`). -/
lemma lamTilde_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ LamTilde χ n :=
  le_trans vonMangoldt_nonneg (vonMangoldt_le_LamTilde χ hsq n)

/-- `(Λ̃−Λ)(n) ≥ 0` (Lemma 1(b)). -/
lemma lamTilde_sub_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ LamTilde χ n - Λ n :=
  sub_nonneg.mpr (vonMangoldt_le_LamTilde χ hsq n)

/-- **The left family sum** `E_L := Σ_{n∈W} (Λ̃−Λ)(n)·Λ̃(n+2)` — the left half of the
    exact overshoot (`overshootExact`'s first summand), the object Wave 2a prices. -/
noncomputable def EL (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ l2cWindow χ z x, (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

/-- Each left summand is `≥ 0` (both factors `≥ 0` by Lemma 1(b)). -/
lemma EL_summand_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ (LamTilde χ n - Λ n) * LamTilde χ (n + 2) :=
  mul_nonneg (lamTilde_sub_nonneg χ hsq n) (lamTilde_nonneg χ hsq (n + 2))

/-- `E_L ≥ 0`. -/
lemma EL_nonneg (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) : 0 ≤ EL χ z x :=
  Finset.sum_nonneg fun n _ => EL_summand_nonneg χ hsq n

/-! ## §1 — the window-hypothesis extractors

Every family fibration consumes the same packet from `n ∈ l2cWindow χ z x`: `n ≠ 0`,
`(n, q) = 1`, `(n+2, q) = 1`, `n ≤ 2x`, `n+2 ≤ 2x+2`, and the two roughness facts (every
`χ ≠ −1` prime of `n`, resp. `n+2`, is `≥ z`).  These pull the packet once. -/

lemma l2cWindow_ne_zero (χ : DirichletCharacter ℂ q) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : n ≠ 0 :=
  (l2cWindow_coprimeSupport χ z x n hn).1

lemma l2cWindow_coprime (χ : DirichletCharacter ℂ q) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : Nat.Coprime n q :=
  (l2cWindow_coprimeSupport χ z x n hn).2.1

lemma l2cWindow_coprime_add_two (χ : DirichletCharacter ℂ q) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : Nat.Coprime (n + 2) q :=
  (l2cWindow_coprimeSupport χ z x n hn).2.2

lemma l2cWindow_le (χ : DirichletCharacter ℂ q) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : n ≤ 2 * x :=
  (Finset.mem_Ioc.mp (l2cWindow_subset χ z x hn)).2

lemma l2cWindow_lt (χ : DirichletCharacter ℂ q) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : x < n :=
  (Finset.mem_Ioc.mp (l2cWindow_subset χ z x hn)).1

lemma l2cWindow_add_two_le (χ : DirichletCharacter ℂ q) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) : n + 2 ≤ 2 * x + 2 := by
  have := l2cWindow_le χ hn; omega

/-- Roughness on the `n` side: every `χ ≠ −1` prime of `n` is `≥ z`. -/
lemma l2cWindow_rough (χ : DirichletCharacter ℂ q) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) {p : ℕ} (hp : p.Prime) (hpd : p ∣ n)
    (hchi : chiRe χ p ≠ -1) : z ≤ p :=
  l2cWindow_roughness χ z x hn hp (hpd.trans (dvd_mul_right n (n + 2))) hchi

/-- Roughness on the `n+2` side: every `χ ≠ −1` prime of `n+2` is `≥ z`. -/
lemma l2cWindow_rough_add_two (χ : DirichletCharacter ℂ q) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) {p : ℕ} (hp : p.Prime) (hpd : p ∣ (n + 2))
    (hchi : chiRe χ p ≠ -1) : z ≤ p :=
  l2cWindow_roughness χ z x hn hp (hpd.trans (dvd_mul_left (n + 2) n)) hchi

/-- The crude cap specialized to a window element: `Λ̃(n) ≤ e^{(log2)z₀}·L'`. -/
lemma lamTilde_cap_window (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hz2 : 2 ≤ z) (hn : n ∈ l2cWindow χ z x) :
    LamTilde χ n ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x :=
  lamTilde_cap χ hsq z x hz2 (l2cWindow_ne_zero χ hn) (l2cWindow_coprime χ hn)
    (by have := l2cWindow_le χ hn; omega) (fun p hp hpd hchi => l2cWindow_rough χ hn hp hpd hchi)

/-- The crude cap on the `n+2` factor of a window element: `Λ̃(n+2) ≤ e^{(log2)z₀}·L'`. -/
lemma lamTilde_cap_window_add_two (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hz2 : 2 ≤ z) (hn : n ∈ l2cWindow χ z x) :
    LamTilde χ (n + 2) ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x :=
  lamTilde_cap χ hsq z x hz2 (by omega) (l2cWindow_coprime_add_two χ hn)
    (l2cWindow_add_two_le χ hn) (fun p hp hpd hchi => l2cWindow_rough_add_two χ hn hp hpd hchi)

/-! ## §2 — the sharp single-block cap

`L2cCore.lamTilde_cap` crudely drops the `χ = −1` block `Λ(m₋) ≤ L'`.  The family
fibration on the `n+2` side needs the *sharp* form that **keeps** `Λ(m₋)`: when `m₋` is
a single prime power `w`, `Λ̃(m) = f(m₊)·Λ(w) ≤ 2^{ω(m₊)}·Λ(w) ≤ e^{(log2)z₀}·Λ(w)`. -/

/-- **The sharp single-block cap.**  On a window element `m` whose `χ = −1` block `m₋` is a
    prime power `w`, `Λ̃(m) ≤ e^{(log2)z₀}·Λ(w)`.  This is the honest weight that carries the
    `Λ(w)` block into the `n+2`-side pair-count fibration (`L2cCore.lamTilde_cap` weakens it
    to `L'`). -/
lemma lamTilde_single_block_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ)
    (hz2 : 2 ≤ z) {m : ℕ} (hm0 : m ≠ 0) (hcop : Nat.Coprime m q) (hmle : m ≤ 2 * x + 2)
    (hrough : ∀ p, p.Prime → p ∣ m → chiRe χ p ≠ -1 → z ≤ p)
    (hpp : IsPrimePow (nMinus χ m)) :
    LamTilde χ m ≤ Real.exp (Real.log 2 * z0 z x) * Λ (nMinus χ m) := by
  have hmP_dvd : nPlus χ m ∣ m := ⟨nMinus χ m, eq_nPlus_mul_nMinus χ hsq hm0 hcop⟩
  have hroughP : ∀ p ∈ (nPlus χ m).primeFactors, z ≤ p := fun p hp =>
    hrough p (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hmP_dvd) (by rw [nPlus_sign hp]; norm_num)
  have hcap := omega_cap χ hsq z x hz2 hm0 hcop hmle hroughP
  have hfP : fChiSum χ (nPlus χ m) = (2 : ℝ) ^ (nPlus χ m).primeFactors.card := by
    rw [← fChiArith_eq_fChiSum]
    exact fChiArith_eq_two_pow χ hsq (nPlus_pos χ m).ne' (fun p hp => nPlus_sign hp)
  calc LamTilde χ m = fChiSum χ (nPlus χ m) * Λ (nMinus χ m) :=
        LamTilde_eq_single_of_card_one χ hsq hm0 hcop hpp
    _ = (2 : ℝ) ^ (nPlus χ m).primeFactors.card * Λ (nMinus χ m) := by rw [hfP]
    _ ≤ Real.exp (Real.log 2 * z0 z x) * Λ (nMinus χ m) :=
        mul_le_mul_of_nonneg_right hcap vonMangoldt_nonneg

/-! ## §3 — the crude `n+2` cap reduction and the support restriction

`EL_le_cap` performs the `:293` all-plus reduction of the `n+2` factor, leaving the
single-variable left overshoot sum `leftOvershootSum := Σ_{n∈W}(Λ̃−Λ)(n)`, which
`leftOvershoot_support` restricts to the classified `L₂`–`L₄` support.  (This is the
*crude* route: it discards the `n+2` block structure that the sharp family analysis uses
for the `n+2`-side pair count; the sharp family budgets are the residual — see NOTES.) -/

/-- The single-variable left overshoot sum `Σ_{n∈W}(Λ̃−Λ)(n)`. -/
noncomputable def leftOvershootSum (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ l2cWindow χ z x, (LamTilde χ n - Λ n)

/-- **The crude `n+2` cap reduction.**  `E_L ≤ e^{(log2)z₀}·L'·Σ_{n∈W}(Λ̃−Λ)(n)`. -/
lemma EL_le_cap (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ} (hz2 : 2 ≤ z) :
    EL χ z x ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x * leftOvershootSum χ z x := by
  rw [EL, leftOvershootSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  calc (LamTilde χ n - Λ n) * LamTilde χ (n + 2)
      ≤ (LamTilde χ n - Λ n) * (Real.exp (Real.log 2 * z0 z x) * Lwin x) :=
        mul_le_mul_of_nonneg_left (lamTilde_cap_window_add_two χ hsq hz2 hn)
          (lamTilde_sub_nonneg χ hsq n)
    _ = Real.exp (Real.log 2 * z0 z x) * Lwin x * (LamTilde χ n - Λ n) := by ring

open Classical in
/-- **The support restriction.**  `leftOvershootSum` restricts to the classified `L₂`–`L₄`
    support: `n` composite with either `n₋ = 1` or `n₋` a prime power with `n₊ > 1`. -/
lemma leftOvershoot_support (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) :
    leftOvershootSum χ z x
      = ∑ n ∈ (l2cWindow χ z x).filter
          (fun n => ¬ n.Prime ∧ n ≠ 1 ∧
            (nMinus χ n = 1 ∨ (IsPrimePow (nMinus χ n) ∧ 1 < nPlus χ n))),
          (LamTilde χ n - Λ n) := by
  rw [leftOvershootSum]
  refine (Finset.sum_filter_of_ne fun n hn hne => ?_).symm
  exact lamTilde_sub_support_classification χ hsq (l2cWindow_ne_zero χ hn)
    (l2cWindow_coprime χ hn) hne

/-! ## §4 — the window-multiples counting primitive

The junk terms (and every crude fiber) count window elements divisible by a fixed `d`.
The interval `(x,2x]` holds at most `x/d + 1` multiples of `d` — the honest count behind the
`(c)`-junk squarefull sum and the corner estimates. -/

/-- **The window-multiples count.**  `#{n ∈ (x,2x] : d ∣ n} ≤ x/d + 1` for `d ≥ 1`
    (`⌊2x/d⌋ − ⌊x/d⌋`, split over the consecutive halves of `(0,2x]`). -/
lemma window_dvd_count (x d : ℕ) (hd : 0 < d) :
    (((Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)).card : ℝ) ≤ (x : ℝ) / d + 1 := by
  have hx : x ≤ 2 * x := by omega
  have hdisj : Disjoint ((Finset.Ioc 0 x).filter (fun n => d ∣ n))
      ((Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)) :=
    Finset.disjoint_left.mpr fun n hn hn' => by
      rw [Finset.mem_filter, Finset.mem_Ioc] at hn hn'; omega
  have hunion : (Finset.Ioc 0 x).filter (fun n => d ∣ n)
        ∪ (Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)
      = (Finset.Ioc 0 (2 * x)).filter (fun n => d ∣ n) := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le x) hx]
  have hcard : ((Finset.Ioc 0 x).filter (fun n => d ∣ n)).card
        + ((Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)).card = 2 * x / d := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Nat.Ioc_filter_dvd_card_eq_div]
  have hlo : ((Finset.Ioc 0 x).filter (fun n => d ∣ n)).card = x / d :=
    Nat.Ioc_filter_dvd_card_eq_div x d
  have hwin : ((Finset.Ioc x (2 * x)).filter (fun n => d ∣ n)).card = 2 * x / d - x / d := by
    omega
  rw [hwin]
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : ((2 * x / d : ℕ) : ℝ) ≤ 2 * ((x : ℝ) / d) := by
    calc ((2 * x / d : ℕ) : ℝ) ≤ ((2 * x : ℕ) : ℝ) / d := Nat.cast_div_le
      _ = 2 * ((x : ℝ) / d) := by push_cast; ring
  have hB : (x : ℝ) / d - 1 ≤ ((x / d : ℕ) : ℝ) := by
    have hlt : x < (x / d + 1) * d := by
      have h1 : d * (x / d) + x % d = x := Nat.div_add_mod x d
      have h2 : x % d < d := Nat.mod_lt x hd
      calc x = d * (x / d) + x % d := h1.symm
        _ < d * (x / d) + d := by omega
        _ = (x / d + 1) * d := by ring
    have hltR : (x : ℝ) < (((x / d : ℕ) : ℝ) + 1) * d := by exact_mod_cast hlt
    rw [sub_le_iff_le_add, div_le_iff₀ hdr]
    linarith [hltR]
  have hBA : (x / d : ℕ) ≤ 2 * x / d := Nat.div_le_div_right hx
  rw [Nat.cast_sub hBA]
  linarith [hA, hB]

/-! ## §5 — NOTES: the residual family-budget interface (Wave 3 consumes these)

The frozen S4 family budgets (freeze §S4) are the honest *research core* of this rung: each
is a full joint pair-count fibration (fiber by the `χ = −1` blocks `v = n₋`, `w = (n+2)₋`;
count each fiber with `L2cCore.l2c_pair_count_clean` at a family-specific `(d₁,d₂)`; sum the
`Λ(v)Λ(w)`-weights via Mertens / `PretenseSum`).  Wave 2a lands the reduction layer above;
the five family budgets are recorded as **named residuals** (NOT stubbed — no `sorry`).  The
target shapes Wave 3 (`L2cMaster`, `exact_overshoot_bound`) consumes, verbatim from the
freeze, over `W := l2cWindow χ z x` under the master hypotheses
`(hz100 : 100^16 ≤ z) (hz8 : (Lwin x)^8 ≤ z) (hzx : (z:ℝ)^3 ≤ x)`:

* `EL_cJunk_bound` — the `(c)`-junk (priced FIRST): small-base squarefull blocks
  `v = p^e`, `p ≤ Zz`, `e ≥ 2`, `z^{1/4} < p^e`; via `window_dvd_count` over the biUnion of
  `{n : p^e ∣ n}` and the geometric tail `∑_{p≤Zz,e≥2,p^e>z^{1/4}} x/p^e ≤ 4x·z^{-1/8}`:
  `≤ Cmain·exp(2·z0 z x)·(x / (z:ℝ)^(1/8:ℝ))·(Lwin x)^3`.
* `EL_T1_bound` — `n₊=P` prime, `m=U` prime, blocks `v,w<z` (`v>1`, odd): fibers `(v,w)`
  at `Zf`, weights `4Λ(v)Λ(w)`, NO `PretenseSum`: `≤ Cmain·(x / z0 z x)` (the `J1` row).
* `EL_T2_bound` — `n₊` composite, `n₊=p'·c`, `c ≥ z`, `d₁ := v·p' = n/c ≤ 2x/z`, `w` routed
  at `z^{1/4}`: `≤ Cmain·(x / Lwin x)·exp(5·z0 z x)·PretenseSum χ (2x+2)` (the `J2` row).
* `EL_T3_bound` — `n₊=P` prime, `v ≥ z` prime, `d₁ := P ≤ 2x/z`, `w`-routing as T2:
  `≤ Cmain·(x / Lwin x)·exp(5·z0 z x)·PretenseSum χ (2x+2)` (`J2`).
* `EL_Tsw_bound` — NEW swap family (the missing `S₂⁴` block): `n₊=P` prime, `1<v<z`,
  `m=U` prime, `d₂ := U ≤ (2x+2)/z`, `v` routed at `z^{1/4}`:
  `≤ Cmain·(x / Lwin x)·exp(5·z0 z x)·PretenseSum χ (2x+2)` (`J2`).
* `EL_corners_bound` — even-block `e`-split at `√x`, `m=1`, squarefull-`≥z`, `>x^{1/4}`
  corners: `≤ Cmain·exp(2·z0 z x)·((x:ℝ)^(9/10:ℝ))·(Lwin x)^3` (the junkExpr `x^{9/10}` row).

RESIDUAL CATCH (LOUD): the freeze's "~380 ln / R5 [C]" sizing is not realistic for a
sorry-free mathlib-rigor landing of these five — each family (fiber def + `(d₁,d₂)` legality
discharge + `l2c_pair_count_clean` application + Mertens/pretense summation) is on the order of
several hundred lines, and the freeze's own `R5/R6 COVER COMPLETENESS` open risk (a Lean-time
disjoint cover may surface a micro-subclass ⇒ STOP-and-flag, iron rule 1) applies at Lean time.
A focused multi-pass campaign per family is warranted; see the executor report. -/

end Salt.HB
