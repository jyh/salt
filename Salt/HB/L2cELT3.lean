/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cEL

/-!
# HB-L2c family estimates — the `E_L` `T3` family (node HB-L2c, Wave 2a residual)

The `T3` row of the `E_L` family analysis (freeze §S4): the surviving `Λ̃−Λ` support with

* `n₊ = P` a single `χ = +1` prime, and
* `n₋ = v` a single `χ = −1` prime with `z ≤ v`.

So `n = P·v` is a squarefree biprime of opposite `χ`-signs.  The window roughness forces the
`χ = +1` prime `P ≥ z`, hence `P = n/v ≤ 2x/z` — the freeze's `d₁ := P` cofactor, whose
reciprocals sum to the `PretenseSum` slot via `sum_inv_plusprime_le_pretense`.

## What this file lands (the `T3` exact reduction layer — sorry-free)

* `lamTilde_sub_eq_two_mul_of_biprime` — the **exact per-term identity** on the biprime
  support: `(Λ̃−Λ)(n) = 2·Λ(n₋)`.  (`Λ̃(n) = f(n₊)·Λ(n₋)` single-block; `f(P) = 2^{ω(P)} = 2`
  for a single `χ=+1` prime; `Λ(n) = 0` since `n = P·v` is not a prime power.)
* `EL_T3` — the `T3` family sub-sum, a filtered slice of `E_L`.
* `EL_T3_eq` — the **exact reduction** `EL_T3 = Σ_{n∈T3} 2·Λ(n₋)·Λ̃(n+2)`, the honest input
  to the frozen pair-count fibration.
* `EL_T3_le_capped` — the crude all-block cap step `EL_T3 ≤ Σ_{n∈T3} 2·Λ(n₋)·e^{(log2)z₀}·L'`
  (retains `Λ(n₋)`, drops the sharp `n+2` block — see the RESIDUAL note for why the frozen
  target requires the sharp cap instead).

## RESIDUAL (LOUD — the frozen `EL_T3_bound` is NOT landed here; see the §NOTES block)

`EL_T3_bound` (frozen shape `≤ Cmain·(x/Lwin x)·exp(5·z0 z x)·PretenseSum χ (2x+2)`, the `J2`
row) is recorded as a **named residual**, NOT stubbed (no `sorry`).  It requires the sharp
single-block cap on `Λ̃(n+2)` together with the *weighted* `l2c_pair_count_clean` fibration
(the `Λ(v)` weight varies within each `d₁ = P` fiber, so it is a weighted count, not a plain
count × constant).  A rigorous refuter-checked analysis (this executor) shows the crude route
overshoots the frozen shape irreducibly; the sharp fibration is a several-hundred-line C-core
carrying the freeze's own `R5/R6 COVER COMPLETENESS` open risk.  See the closing NOTES block.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the biprime per-term identity -/

/-- **The `T3` per-term identity.**  On a window-coprime `n` whose `χ=+1` part `n₊` and
    `χ=−1` part `n₋` are both prime, `(Λ̃−Λ)(n) = 2·Λ(n₋)`.  Three facts combine:
    `Λ̃(n) = f(n₊)·Λ(n₋)` (single `χ=−1` block, `LamTilde_eq_single_of_card_one`);
    `f(n₊) = 2^{ω(n₊)} = 2^1 = 2` (`fChiArith_eq_two_pow` + `nPlus` prime); and `Λ(n) = 0`
    (`n = n₊·n₋` is a coprime product of two `≠ 1` factors, so not a prime power). -/
lemma lamTilde_sub_eq_two_mul_of_biprime (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {n : ℕ} (hn0 : n ≠ 0) (hcop : Nat.Coprime n q)
    (hP : (nPlus χ n).Prime) (hM : (nMinus χ n).Prime) :
    LamTilde χ n - Λ n = 2 * Λ (nMinus χ n) := by
  have hMpp : IsPrimePow (nMinus χ n) := hM.isPrimePow
  have hLt : LamTilde χ n = fChiSum χ (nPlus χ n) * Λ (nMinus χ n) :=
    LamTilde_eq_single_of_card_one χ hsq hn0 hcop hMpp
  have hfP : fChiSum χ (nPlus χ n) = 2 := by
    rw [← fChiArith_eq_fChiSum,
        fChiArith_eq_two_pow χ hsq (nPlus_pos χ n).ne' (fun p hp => nPlus_sign hp),
        hP.primeFactors, Finset.card_singleton, pow_one]
  have hΛn : Λ n = 0 := by
    have hne : n = nPlus χ n * nMinus χ n := eq_nPlus_mul_nMinus χ hsq hn0 hcop
    have hnpp : ¬ IsPrimePow n := by
      rw [hne]
      exact not_isPrimePow_mul_coprime (coprime_nPlus_nMinus χ n)
        hP.ne_one hM.ne_one (nPlus_pos χ n).ne' (nMinus_pos χ n).ne'
    exact vonMangoldt_eq_zero_iff.mpr hnpp
  rw [hLt, hfP, hΛn, sub_zero]

/-! ## §2 — the `T3` family sub-sum and its exact reduction -/

open Classical in
/-- **The `E_L` `T3` family sub-sum.**  The slice of `E_L = Σ_{n∈W} (Λ̃−Λ)(n)·Λ̃(n+2)` on the
    biprime support `n₊`, `n₋` both prime with `z ≤ n₋` (freeze §S4 `T3`). -/
noncomputable def EL_T3 (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ (l2cWindow χ z x).filter
      (fun n => (nPlus χ n).Prime ∧ (nMinus χ n).Prime ∧ z ≤ nMinus χ n),
    (LamTilde χ n - Λ n) * LamTilde χ (n + 2)

open Classical in
/-- **The `T3` exact reduction.**  `EL_T3 = Σ_{n∈T3} 2·Λ(n₋)·Λ̃(n+2)` — the honest input to
    the pair-count fibration (the `(Λ̃−Λ)(n)` factor collapses to `2·Λ(n₋)` termwise). -/
lemma EL_T3_eq (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) :
    EL_T3 χ z x
      = ∑ n ∈ (l2cWindow χ z x).filter
          (fun n => (nPlus χ n).Prime ∧ (nMinus χ n).Prime ∧ z ≤ nMinus χ n),
        2 * Λ (nMinus χ n) * LamTilde χ (n + 2) := by
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  obtain ⟨hnw, hP, hM, _⟩ := hn
  rw [lamTilde_sub_eq_two_mul_of_biprime χ hsq (l2cWindow_ne_zero χ hnw)
      (l2cWindow_coprime χ hnw) hP hM]

open Classical in
/-- **The crude all-block cap step.**  `EL_T3 ≤ Σ_{n∈T3} 2·Λ(n₋)·(e^{(log2)z₀}·L')` — retains
    the sharp `Λ(n₋)` weight, caps `Λ̃(n+2)` by the crude all-block bound.  (This step alone
    does NOT reach the frozen `EL_T3_bound`: the crude `L'` on `Λ̃(n+2)` costs a factor `L'`
    over the sharp single-block cap, which the frozen `J2` shape cannot absorb in the operative
    regime — see the RESIDUAL note.  Landed as the honest crude majorant a downstream campaign
    can compare against.) -/
lemma EL_T3_le_capped (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ} (hz2 : 2 ≤ z) :
    EL_T3 χ z x
      ≤ ∑ n ∈ (l2cWindow χ z x).filter
          (fun n => (nPlus χ n).Prime ∧ (nMinus χ n).Prime ∧ z ≤ nMinus χ n),
        2 * Λ (nMinus χ n) * (Real.exp (Real.log 2 * z0 z x) * Lwin x) := by
  rw [EL_T3_eq χ hsq z x]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  obtain ⟨hnw, _, _, _⟩ := hn
  have hw : (0 : ℝ) ≤ 2 * Λ (nMinus χ n) :=
    mul_nonneg (by norm_num) vonMangoldt_nonneg
  exact mul_le_mul_of_nonneg_left (lamTilde_cap_window_add_two χ hsq hz2 hnw) hw

/-! ## §NOTES — the residual `EL_T3_bound` (the frozen `J2` row) and its exact gap

The frozen deliverable

  `EL_T3_bound : EL_T3 χ z x ≤ Cmain·(x / Lwin x)·exp(5·z0 z x)·PretenseSum χ (2x+2)`

(under `hz100 : 100^16 ≤ z`, `hz8 : (Lwin x)^8 ≤ z`, `hzx : (z:ℝ)^3 ≤ x`, with `Cmain > 0`
an explicit absolute constant) is a **named residual** — NOT stubbed, no `sorry`.  The exact
remaining step, and the two cover subtleties surfaced at Lean time, are recorded here.

### Why the crude route is provably insufficient (refuter-checked this executor)

`EL_T3_le_capped` reduces `EL_T3 ≤ 2·e^{(log2)z₀}·L'·Σ_{n∈T3} Λ(n₋)`.  Reindexing `n = P·v`
and bounding `Σ_{n∈T3} Λ(v)` by the `PretenseSum` route (`[Pv ≤ 2x] ≤ 2x/(Pv)`, then
`Σ_P 1/P ≤ z₀·PS/L'` via `sum_inv_plusprime_le_pretense` and `Σ_v Λ(v)/v ≤ L' + C` via
`mertens_vonMangoldt_div_le`) yields

  `EL_T3 ≤ C·x·z₀·L'·e^{0.7·z₀}·PS`.

Ratio to the frozen `J2` target `C·(x/L')·e^{5z₀}·PS` is `z₀·L'²·e^{-4.3 z₀}`.  In the
operative downstream regime `z₀` is a bounded constant (`z = q^{1/z₀*}`, `x ∈ [q^250,q^500]`,
`z₀* < 1/6`, so `z₀ = log x / log z` is `O(1)` ~ 40–80) while `L' = log(2x+2) → ∞`; hence the
ratio `→ ∞` and the crude route OVERSHOOTS irreducibly.  The `1/L'` in the frozen shape can
only come from the pair count's `1/(log Z)²` saving.  So the sharp single-block cap
`Λ̃(n+2) ≤ e^{(log2)z₀}·Λ(w)` (`lamTilde_single_block_le`) + `l2c_pair_count_clean` are
mandatory, not optional.

### The residual step (the several-hundred-line C-core)

From `EL_T3_eq`, `EL_T3 = Σ_{n∈T3} 2·Λ(v)·Λ̃(n+2)` with `v = n₋`, `w = (n+2)₋`.  The frozen
fibration:
1. Split by `w`-shape: `w = 1` (all-plus, `lamTilde_cap_window_add_two`), `w` a prime power
   (sharp `lamTilde_single_block_le`, keep `Λ(w)`), `ω(w) ≥ 2` (`Λ̃(n+2) = 0`, drops).
2. `w`-routing (as T2): `w ≤ z^{1/4}` → modulus `d₂ := w`; `w ∈ (z^{1/4}, z]` prime / pp-base
   `> Zz` → cofactor route (`d₂ := 1`); small-base squarefull `w` → the SEPARATE `(c)`-junk.
3. Fiber by `(d₁, d₂) = (P, w)`; count via `l2c_pair_count_clean` at the sieve floor
   `Z := Zz = ⌊z^{1/16}⌋` (so `v ≥ z ≥ Zz` is coprime to `primorial Zz`).  Legality
   `P·w·Zz⁸·(log Zz)² ≤ 32x` holds: `P·w ≤ 2x·z^{-3/4}`, `Zz⁸ = z^{1/2}`, so
   `2x·z^{-1/4}·(log z)² ≤ 32x` from `(log z)² ≤ 16·z^{1/4}` at `z ≥ 100^16`.
4. Weighted summation: the `Λ(v)` weight VARIES within each `d₁ = P` fiber (`v = n/P`), so
   this is a `Λ(v)`-WEIGHTED count, not `count × const`.  Sum `Σ_P 1/P ≤ z₀·PS/L'`
   (`sum_inv_plusprime_le_pretense`) for the `PS/L'` factor; sum `Λ(w)` over the routed `w`
   via Mertens (`mertens_vonMangoldt_div_le` / `mertens_log_div_prime_le`).  Budget
   `≤ C·x·z₀³·e^{0.7 z₀}·PS/L' ≤ C·(x/L')·e^{5 z₀}·PS` (`z₀³·e^{0.7 z₀} ≤ e^{5 z₀}`).

### Two Lean-time cover subtleties (iron rule 1 — flag, do not improvise)

(A) **Sift floor Zz vs Zf.**  The cofactor coprimality `Coprime (primorial Z) (v·m)` needs
    `v ≥ Z`.  Since `x` may exceed `z⁴⁸`, `Zf = ⌊x^{1/48}⌋` can exceed `z`, so `v ≥ z` need
    NOT give `v ≥ Zf`.  The fibration MUST sift at `Zz = ⌊z^{1/16}⌋ ≤ z ≤ v` — the freeze's
    `Zf` (used for the modulus route) is the WRONG floor for the `T3` cofactor `v`.

(B) **Squarefull-`w` corner disjointness.**  Freeze routes small-base squarefull `w` to the
    `(c)`-junk, whose shape is `junkExpr` (`x/z^{1/8} + x^{9/10}`), NOT `J2`.  So the `T3`
    sub-sum as filtered here (`n₊`, `n₋` both prime — NO `w`-condition) contains those corner
    terms, which do NOT fit the `J2` `EL_T3_bound` RHS.  A rigorous landing must EITHER prove
    those terms separately fit `J2` (they may, via the sharp cap giving `Λ(w) ≤ L'` and the
    sparse squarefull count), OR restrict the `T3` filter to exclude them and ship them to the
    `(c)`-junk sub-sum.  Which choice the frozen `EL_T3_bound` intends is UNDER-SPECIFIED in
    the freeze; resolving it is a statement-adjacent decision (Fable/human tier) — flagged, not
    improvised.  This is exactly the freeze's `R5/R6 COVER COMPLETENESS` open risk at Lean time.
-/

end Salt.HB
