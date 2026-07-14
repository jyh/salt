/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.WindowSmallChi
import Salt.Chen.DivisorBound
import Salt.Chen.BandIdent
import Salt.Chen.BlockPricing
import Salt.Chen.SwitchBlocks
import Salt.Chen.SwitchBV

/-!
# GLU-BV — discharging `hBVblocks` at the operating point (the H-glue's BV half)

Design: `docs/blueprints/flags.md`, the entries `2026-07-14 WBV7` (the terminal theorem
`general_BV_cutoff_unconditional`'s full threshold list), `BND3`, `WBV6`, `DIV1`,
`PE3c-4 GATE`; and `Salt.Chen.WindowSmallChi`'s in-file threshold documentation.

The chain (all LANDED — this node instantiates the thresholds at the operating point):
`SwitchBlocks.mainA3_of_block_remainders`'s `hBVblocks`
  ← `BlockPricing.hBVblocks_of_generalBV` (hHD/hCE/hNum)
  ← `hHDblocks_of_perBlock` (hBlock)
  ← `PieceDecomp.hBlock_of_window_prices` (high-piece Φ's + band `Plo`)
  ← `WindowClose.hHD_of_generalBV_window` + `BandIdent.Plo_discharge_priced`
  ← **`WindowSmallChi.general_BV_cutoff_unconditional`** (the terminal windowed-BV price).

## Numeric plan (recorded FIRST, per the C+ discipline)

The consumers (`hHD_of_generalBV_window`, `Plo_discharge_priced`) each take, as the named
inputs `hprice_hi`/`hprice_lo` / the four one-sided band prices, a bound of the shape
`∑_{d∈Dset} ‖apDiscBilinCutoff α (blockPrimeInd N) X M 2 d T‖ ≤ P` at `T ∈ {x, x/2+1}`.  That
is EXACTLY the conclusion of `general_BV_cutoff_unconditional`, whose price is
`P = (Kβ + (6(Km + 448 + 32√26) + (2^{A+5}Kβ' + 15360)))·(X·M)/(log(X·M))^A`.

### The operating point (READ from `PieceDecomp`/`BandIdent`)

Per `(j, k)` (block `j ∈ range(maxBlock+1)`, dyadic `p₃`-piece `k ∈ range(⌊log₂x⌋+1)`):
* `N = pieceN k = 2^k − 1`, `M = pieceM k = 2^{k+1} − 1` (so the block primes are `(N, M] =
  {2^k, …, 2^{k+1}−1}`, exactly `[2^k, 2^{k+1})`);
* high-piece box: `α = restrictAlpha (blockAlpha z y ε₀ j) 0 (min (z·N+1) (x+1))`,
  `X ≥ min (z·N, x)` (`hHD_of_generalBV_window`'s `hbX : b ≤ X+1`);
* band box: `α ∈ {blockAlphaSym, restrictAlpha (blockAlphaLow …)}`, `X ≥ x`
  (`Plo_discharge_priced`'s `hxX : x ≤ X`);
* `T ∈ {x, x/2+1}` (the two one-sided cutoffs of `blockBox_windowDisc_eq`);
* `D = Q·Dlev` (the level of distribution, `~ √x/(log)`), `Dset = {d ∣ Ps : d < Q·Dlev}`;
* `D0 = 2^{k0}` the small-conductor cut.

### The coupled exponent budget (A ≥ 12-family)

Per-box price `~ (const)·(X·M)/(log)^A`; there are `O(log²x)` boxes `(j, k)`.  IF each box had
`X·M = O(x)`, the sum would be `O(log²x)·x/(log)^A = x/(log)^{A−2} ≤ x/(log)^{10}` for `A ≥ 12`.
The coupled constraints are `A + 2 ≤ C0` (the terminal `hCge`; the small-conductor `D0`-power),
`A + 2 ≤ B` (the level cut `hBge`), and the SW couplings hold at any exponent with a CONSTANT
`Kβ/Km/Kβ'` on the SW-priceable pieces (see below).  A concrete satisfying choice is
`A = 12, C0 = 14, B = 14` (`A+2 = 14 ≤ 14 = C0`, `A+2 = 14 ≤ 14 = B`, `A = 12 ≥ 12`).

### The `M ≤ 2N` off-by-one (RESOLVED — item `blockPrimeInd_pieceN_eq`)

`M = pieceM k = 2^{k+1} − 1` and `N = pieceN k = 2^k − 1` give `M = 2N + 1`, which VIOLATES the
terminal theorem's `M ≤ 2·N`.  Resolution: apply the terminal theorem at `N' := 2^k`
(`M = 2^{k+1} − 1 ≤ 2·2^k` ✓) and transport the price back to `blockPrimeInd (pieceN k)` via
`blockPrimeInd_pieceN_eq` — for `k ≥ 2` the two indicators are EQUAL, since they differ only at
`n = 2^k`, which is not prime (`2^k` even, `> 2`).  For `k ≤ 1` the pieces `(0,1]`, `(1,3]` are
`O(1)` and fall under the crude/empty fallback.

### ★ THE OPERATING-POINT BUDGET GAP (catch — see the closing flag) ★

The task's premise "`X_box·M_piece ~ x` per box" does **NOT** hold on the WINDOW route as landed,
because the `m`-range is priced in ONE shot (not dyadically sub-blocked in `m`, unlike the SW3
box route `SwitchDyadic`/`SwitchPricing` where `X = 2^i`, `M = 2^j`, `X·M = 2^{i+j} ~ x` on the
`O(log x)` surviving boxes).  Concretely:

* **Band boxes** (`Plo_discharge_priced`) use a GLOBAL `X ≥ x` (`hxX : x ≤ X`).  Summed over the
  pieces the price is `≥ (const)·X·∑_k pieceM k / (log)^A ≥ (const)·x·2^{⌊log₂x⌋+2}/(log)^A ~
  (const)·4x²/(log)^A ≫ x/(log)^{10}`.
* **High-piece boxes** (`hHD_of_generalBV_window`, `hbX : b ≤ X+1`, `b = min(z·N+1, x+1)`) have
  `X·M = min(z·N, x)·2N`.  For `N ≤ √(x/z)` this is `≤ 2x` ✓; but pieces with `√(x/z) < N ≤ x/z²`
  are NON-EMPTY (an admissible triple `p₁p₂ ≤ x/N`, `p₁p₂ ≥ z²`) yet carry `X·M = 2z·N² ≫ x`
  (up to `~ x^{13/8}` at `N ~ x^{3/4}` for `z = x^{1/8}`).

The root cause: `general_BV_cutoff_unconditional`'s price is by the NOMINAL box area `X·M`, but
the cutoff `m·n ≤ T = x` makes the EFFECTIVE mass `~ x/log ≪ X·M`.  The price is a true upper
bound but is `X·M / x`-lossy, so summing it over the `O(log²x)` boxes exceeds the `x/(log)^{10}`
budget.  Closing `hNum` (`RHD + RCE ≤ x/(log x)^{10}`) therefore requires EITHER a cutoff-mass
price (`≤ (const)·T/(log T)^A`) OR dyadic `m`-sub-blocking of the window boxes so `X·M ~ T` — a
change to the LANDED `general_BV_cutoff_final`/`PieceDecomp` design (Fable/human-tier).  This node
lands the per-box thresholds honestly (`cutoff_BV_at_op`, the `M ≤ 2N` re-index, `hdiv` via
`DivisorBound`) and records the budget gap; the composed `hBVblocks_at_op` is BLOCKED on it.

## What this file lands (sorry-free, axiom-clean, NEW FILE — no edits to landed files)

1. `blockPrimeInd_pieceN_eq` — the `M ≤ 2N` re-index (`k ≥ 2`).
2. `cutoff_BV_at_op` — `general_BV_cutoff_unconditional` with the `herr_div` slot discharged via
   `DivisorBound.hdiv_discharge` (the operating relations `D ≤ √x`, `√x ≤ 4X`, `X·M ≤ x²`), the
   rest exposed as the structural operating-point bundle (item A / FLOOR).
3. `cutoff_BV_at_piece` — item 2 re-indexed to the dyadic piece (`N := 2^k`), transporting the
   price to `blockPrimeInd (pieceN k)`; the direct `hprice_hi`/`hprice_lo` supplier.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## 1. The `M ≤ 2N` re-index: `blockPrimeInd (pieceN k) = blockPrimeInd (2^k)` for `k ≥ 2` -/

/-- **`2^k` is not prime for `k ≥ 2`.**  It is even and `≥ 4 > 2`. -/
theorem not_prime_two_pow {k : ℕ} (hk : 2 ≤ k) : ¬ (2 ^ k).Prime := by
  intro hp
  have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h4 : (4 : ℕ) ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rcases (hp.eq_one_or_self_of_dvd 2 h2) with h | h <;> omega

/-- **The `M ≤ 2N` re-index (FULL).**  For `k ≥ 2`, `blockPrimeInd (pieceN k) = blockPrimeInd
(2^k)`.  The two interval-prime indicators differ only at `n = 2^k` (the single integer in
`(pieceN k, 2^k] = (2^k − 1, 2^k]`), where both vanish because `2^k` is not prime.  This lets the
operating point apply `general_BV_cutoff_unconditional` at the `M ≤ 2N`-satisfying lower endpoint
`2^k` (`pieceM k = 2^{k+1} − 1 ≤ 2·2^k`) while pricing the actual `blockPrimeInd (pieceN k)`
object. -/
theorem blockPrimeInd_pieceN_eq {k : ℕ} (hk : 2 ≤ k) :
    blockPrimeInd (pieceN k) = blockPrimeInd (2 ^ k) := by
  funext n
  unfold blockPrimeInd pieceN
  have h2k1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
  by_cases hn : n = 2 ^ k
  · subst hn
    have hnp : ¬ (2 ^ k).Prime := not_prime_two_pow hk
    rw [if_neg (fun h => hnp h.2), if_neg (fun h => hnp h.2)]
  · by_cases hp : n.Prime
    · by_cases hlt : 2 ^ k < n
      · rw [if_pos ⟨by omega, hp⟩, if_pos ⟨hlt, hp⟩]
      · have hnn : ¬ 2 ^ k - 1 < n := by omega
        rw [if_neg (fun h => hnn h.1), if_neg (fun h => hlt h.1)]
    · rw [if_neg (fun h => hp h.2), if_neg (fun h => hp h.2)]

/-- `pieceM k ≤ 2·2^k` — the `M ≤ 2·N` input at the re-index `N := 2^k`
(`2^{k+1} − 1 ≤ 2^{k+1}`). -/
theorem pieceM_le_two_pow (k : ℕ) : pieceM k ≤ 2 * 2 ^ k := by
  unfold pieceM
  have h : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  omega

/-- `2^k ≤ pieceM k` — the `N ≤ M` input at the re-index `N := 2^k` (`2^k ≤ 2^{k+1} − 1`). -/
theorem two_pow_le_pieceM (k : ℕ) : 2 ^ k ≤ pieceM k := by
  unfold pieceM
  have h : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- **The piece transport (FULL).**  The windowed-BV price sum at the re-indexed lower endpoint
`2^k` transfers VERBATIM to the actual dyadic-piece endpoint `pieceN k = 2^k − 1` (for `k ≥ 2`),
since `blockPrimeInd (pieceN k) = blockPrimeInd (2^k)` (`blockPrimeInd_pieceN_eq`).  Composing this
with `cutoff_BV_at_op` at `N := 2^k`, `M := pieceM k` (the `M ≤ 2N`/`N ≤ M` inputs from
`pieceM_le_two_pow`/`two_pow_le_pieceM`) supplies the `hprice_hi`/`hprice_lo` inputs of
`WindowClose.hHD_of_generalBV_window` and the four one-sided prices of
`BandIdent.Plo_discharge_priced` at the ACTUAL operating-point object. -/
theorem sum_norm_apDiscBilinCutoff_pieceN {k : ℕ} (hk : 2 ≤ k) (α : ℕ → ℂ) (X M T : ℕ)
    (Dset : Finset ℕ) (r : ℕ → ℕ) :
    (∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd (pieceN k)) X M (r d) d T‖)
      = ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd (2 ^ k)) X M (r d) d T‖ := by
  rw [blockPrimeInd_pieceN_eq hk]

/-! ## 2. `cutoff_BV_at_op` — the terminal theorem with `herr_div` discharged (item A / FLOOR) -/

open Classical in
/-- **`cutoff_BV_at_op` (FLOOR A) — the operating-point windowed-BV price.**
`general_BV_cutoff_unconditional` with its `herr_div` slot (`∀ e, 2 ≤ e ≤ D →
#div(e)·L^{A+5} ≤ √X`) discharged by `DivisorBound.hdiv_discharge` at the operating relations
`D ≤ √x`, `√x ≤ 4X`, `X·M ≤ x²` (`d(e) ≤ C₃·e^{1/3}` with `1/3 < 1/2` absorbs the log-power).
The remaining hypotheses are the structural operating-point bundle (the scale relations, the
coupled `A+2 ≤ B, C0`, the dyadic `D0 = 2^{k0}`, the level cut, the `e`-fold thresholds, and the
three SW couplings — SW-supplied at any exponent by the landed `hβSW` machinery on the
SW-priceable pieces).  The conclusion is exactly the `hprice_hi`/`hprice_lo` shape the window/band
consumers name.

NOTE (see the file header + the closing flag): this is the honest PER-BOX price; the operating
relation `X·M ≤ x²` (like the `x/(log)^{10}` budget) FAILS on the top window pieces, where the
un-sub-blocked `m`-range makes `X·M ≫ x²`. -/
theorem cutoff_BV_at_op {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ) (x₀ : ℝ), 0 < K ∧
      ∀ (x : ℝ) (α : ℕ → ℂ) (X N M T D0 D k0 Klog : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ)
        (Kβ Km Kβ' B : ℝ),
        x₀ ≤ x →
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 0 ≤ Km → 0 ≤ Kβ' → N₀ ≤ N → M ≤ 2 * N → D0 ≤ N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (1 ≤ Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < N → 2 ≤ X → 2 ≤ M → A + 2 ≤ B → A + 2 ≤ C0 →
        D0 = 2 ^ k0 → 2 ≤ D0 → D0 ≤ D → Klog = Nat.log 2 D →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ B) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2) ≤ 2 * (2 : ℝ) ^ k0) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt X) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 3) ≤ Real.sqrt M) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt ((X : ℝ) * (M : ℝ))) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 4) ≤ (D0 : ℝ)) →
        ((Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (M : ℝ)) →
        -- the `hdiv` operating relations (discharge `herr_div` via `DivisorBound.hdiv_discharge`)
        (Real.sqrt x ≤ 4 * (X : ℝ)) → ((D : ℝ) ≤ Real.sqrt x) → ((X : ℝ) * (M : ℝ) ≤ x ^ 2) →
        (∀ e, 2 ≤ e → e ≤ D → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (∀ e, 2 ≤ e → e ≤ D →
            (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ C0) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + C0) ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1 + 2 * C0) ≤ Km * (Real.log N) ^ (A + 2 * C0)) →
        (∀ e, 2 ≤ e → e ≤ D →
            K * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (A + 1 + 1 + 2 * C0)
              ≤ Kβ' * (Real.log N) ^ (A + 1 + 2 * C0)) →
        ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
          ≤ (Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                + ((2 : ℝ) ^ (A + 5) * Kβ' + 15360))) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hbody⟩ := general_BV_cutoff_unconditional hA hC0
  obtain ⟨x₀, hdiv⟩ := hdiv_discharge (A := A) hA.le
  refine ⟨K, N₀, x₀, hK0, fun x α X N M T D0 D k0 Klog Dset r Kβ Km Kβ' B hx
    hα hKβ hKm hKβ' hN hM2N hD0N hDge1 hcop2 hL1 hD0 hD0N' hNM hD1 hDsetD hDN hX2 hM2 hBge hCge
    hD0eq h2D0 hD0D hKlog hDscale hD0lo_main hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev
    hsqrt4X hDsqrtx hXMx2 herr_LEpos herr_D0E hDXM herr_scale hcoupG hcoup3 herr_book4 => ?_⟩
  have herr_div : ∀ e, 2 ≤ e → e ≤ D →
      (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Real.sqrt (X : ℝ) :=
    fun e he2 heD => hdiv x hx X M D (by omega) (by omega) hDsqrtx hsqrt4X hXMx2 e (by omega) heD
  exact hbody α X N M T D0 D k0 Klog Dset r Kβ Km Kβ' B hα hKβ hKm hKβ' hN hM2N hD0N hDge1 hcop2 hL1
    hD0 hD0N' hNM hD1 hDsetD hDN hX2 hM2 hBge hCge hD0eq h2D0 hD0D hKlog hDscale hD0lo_main hXsqrt
    hMsqrt herr_lev herr_D0lo herr_Mlev herr_div herr_LEpos herr_D0E hDXM herr_scale hcoupG hcoup3
    herr_book4

/-! ## 3. The crumbs — `hCE` and the diagonal (item B / FLOOR)

Both crumbs feed the block-remainder close (`hCE` is `hBVblocks_of_generalBV`'s conversion-error
slot; the diagonal is the `x^{2/3}`-mass row of `BandIdent.Plo_discharge_priced`'s conclusion).
The tight forms — the crude conversion count "`d` has a prime factor `≥ w₀` ⟹ few such `d`", and
the diagonal's `π`-refined `∑_{p₁≤y} π(√(x/p₁)) ≪ x^{2/3}/log` — are SW4-downstream analytic
number theory (Mertens `∑ 1/φd`, prime-counting).  Following the codebase's named-slot pattern,
this section lands the CRUDE-REDUCTION halves (the `ν ≤ 1` / ν-summability steps) with the deep
counts exposed as the named residuals. -/

/-- **The coarse ν-summability (FULL).**  `∑_{d ∈ S} nuChen d ≤ #S` (each `nuChen d ≤ 1`,
`nuChen_le_one`).  The reusable "ν-summability" factor of both crumbs (the tight
`∑_{d∣Ps} 1/φd = ∏(1 + 1/(p−1))` Mertens form is the downstream residual). -/
theorem sum_nuChen_le_card (S : Finset ℕ) : ∑ d ∈ S, nuChen d ≤ (S.card : ℝ) := by
  calc ∑ d ∈ S, nuChen d ≤ ∑ _d ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun d _ => nuChen_le_one d)
    _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **`hCE_discharge` (FLOOR B — the crude conversion-error reduction).**  The `ν ≤ 1` step of
SW4's crude route: the block conversion-error double sum (`hBVblocks_of_generalBV`'s `hCE` slot,
`blockConvErr j d = ν(d)·blockNonUnitCount j d`) is bounded by the non-unit triple-count double
sum, VERBATIM at the same guard/level.  The remaining content — the count `hcount` — is the
honest crude arithmetic "the non-coprime block triples have `p₁ ∣ d`, so `d` carries a prime
factor `≥ w₀` and there are few such `d`" (the SW4/`w₀`-scale residual, named here). -/
theorem hCE_discharge (x z y : ℕ) (ε₀ : ℝ) (Ps : ℕ) (bound RCE : ℝ)
    (hcount : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then blockNonUnitCount x z y ε₀ j d else 0) ≤ RCE) :
    (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then blockConvErr x z y ε₀ j d else 0) ≤ RCE := by
  refine le_trans (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun d _ => ?_) hcount
  split_ifs with hd
  · unfold blockConvErr
    have hcnt : (0 : ℝ) ≤ blockNonUnitCount x z y ε₀ j d := by unfold blockNonUnitCount; positivity
    calc nuChen d * blockNonUnitCount x z y ε₀ j d
        ≤ 1 * blockNonUnitCount x z y ε₀ j d := mul_le_mul_of_nonneg_right (nuChen_le_one d) hcnt
      _ = blockNonUnitCount x z y ε₀ j d := one_mul _
  · exact le_refl _

/-- **`diag_nu_crumb` (FLOOR B — the ν-weighted diagonal reduction).**  BND2's diagonal crumb: the
`p₂ = p₃` band-diagonal count is `d`-INDEPENDENT (no residue filter — `bandDiagCount`), so its
`ν`-weighted sum FACTORS as `(∑_d ν(d))·#diag`, bounded via the coarse ν-summability
(`sum_nuChen_le_card`) and the landed crude count `bandDiagCount_le` (`#diag ≤ y·(M−N)`).  The
analytic tightening — replacing the `∑_k y·(M−N) ~ x·y` crude sum by the `π`-refined
`∑_{p₁≤y} π(√(x/p₁)) ≪ x^{2/3}/log` (the genuinely budget-clearing form) — is the downstream
residual (SW4's budget row). -/
theorem diag_nu_crumb (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) (S : Finset ℕ) :
    (∑ d ∈ S, nuChen d * bandDiagCount x z y ε₀ j N M)
      ≤ (S.card : ℝ) * ((y : ℝ) * ((M - N : ℕ) : ℝ)) := by
  have hdiag0 : (0 : ℝ) ≤ bandDiagCount x z y ε₀ j N M := by unfold bandDiagCount; positivity
  calc ∑ d ∈ S, nuChen d * bandDiagCount x z y ε₀ j N M
      = (∑ d ∈ S, nuChen d) * bandDiagCount x z y ε₀ j N M := by rw [Finset.sum_mul]
    _ ≤ (S.card : ℝ) * bandDiagCount x z y ε₀ j N M :=
        mul_le_mul_of_nonneg_right (sum_nuChen_le_card S) hdiag0
    _ ≤ (S.card : ℝ) * ((y : ℝ) * ((M - N : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (bandDiagCount_le x z y ε₀ j N M) (by positivity)

/-! ## Composition sanity -/

section CompositionSanity

#check @Salt.Chen.blockPrimeInd_pieceN_eq
#check @Salt.Chen.pieceM_le_two_pow
#check @Salt.Chen.two_pow_le_pieceM
#check @Salt.Chen.sum_norm_apDiscBilinCutoff_pieceN
#check @Salt.Chen.cutoff_BV_at_op
#check @Salt.Chen.sum_nuChen_le_card
#check @Salt.Chen.hCE_discharge
#check @Salt.Chen.diag_nu_crumb
#check @Salt.Chen.general_BV_cutoff_unconditional
#check @Salt.Chen.hdiv_discharge

end CompositionSanity

end Salt.Chen
