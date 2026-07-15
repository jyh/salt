/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.ChenFinal2

/-!
# Node fin7b — the BAND-leg row bundles + the sym single-`k` treatment

Design: `docs/blueprints/flags.md`, the `2026-07-14 fin6` entry (the restructure; the SYM SUBTLETY),
the `fin5`/`PRICE-GATE` entries.  New file; namespace `Salt.Chen`; NO edits to any landed file, NO
wiring of `All.lean`.  Sibling `Salt/Chen/ChenRows1.lean` (fin7a) does the box leg in parallel
(disjoint).

## The two `_band` legs discharged here (`Salt/Chen/ChenFinal2.lean`), hypothesis lists verbatim

Both `sym_box_hprice_at_2pow_band` (§F0.4) and `low_box_hprice_at_2pow_band` carry the SAME
analytic hypothesis list; the sym leg additionally carries `y ≤ pieceN k` (the `max`-collapse
selector).  With `X = 2^{i+1}−1`, `M = pieceM k`, `L = Real.log ((X:ℝ)·(pieceM k))`:

| # | hypothesis | class |
|---|---|---|
| 1  | `2 ≤ k`                                     | caller |
| 2  | `y ≤ pieceN k` (SYM only)                    | collapsed-regime selector |
| 3  | `Real.exp (10^10) ≤ x`                       | FRESH (tower threshold) |
| 4  | `i ∈ dyadicBoundary (pieceN k) (pieceM k) …` | caller (box membership) |
| 5  | `X = 2^{i+1}−1`                              | defn |
| 6  | `x^{1/3}/8 ≤ 2^k`                            | SUPPLIED (`band_kfloor_of_live`) |
| 7  | `N₀ ≤ 2^k`                                   | FRESH |
| 8  | `2 ≤ L`                                      | SUPPLIED (scaffold + `log x ≥ 2`) |
| 9  | `2 ≤ X`                                      | SUPPLIED (band `X`-floor `F < 2^{i+1}`) |
| 10 | `1 ≤ D`                                      | SUPPLIED (`D := opD x`) |
| 11 | `x^{11/24}/8 ≤ D`                            | SUPPLIED (`opD`) |
| 12 | `Q·(QR·Dlev) ≤ D`                            | FRESH (`a12_level`-style) |
| 13 | `D ≤ √(X·M)/L^15`                            | FRESH |
| 14 | `D < (2^k+1)²`                               | FRESH (`hDsq` via kfloor) |
| 15 | `4·(1+log D)·D ≤ 2^k·M/L^13`                 | FRESH (`habs`) |
| 16 | `L^16 ≤ √X`                                  | FRESH (band `X`-floor) |
| 17 | `L^16 ≤ √M`                                  | FRESH |
| 18 | `D·L^18 ≤ √(X·M)`                            | FRESH (`herr_lev`) |
| 19 | `L^18 ≤ √M`                                  | FRESH (`herr_Mlev`) |
| 20 | `F ≤ X`                                      | SUPPLIED (`F < 2^{i+1} ⟹ F ≤ X`) |
| 21 | `D ≤ √x`                                     | SUPPLIED (`opD`) |
| 22 | `L ≤ Lb`                                     | SUPPLIED (`Lb := log x + 3`) |
| 23 | `(3/log 2)^8·x^{1/6}·Lb^18 ≤ √F`             | FRESH (band `F`-floor `F ≥ z·y`) |
| 24 | `D ≤ X·M`                                    | SUPPLIED |

The `_band` legs feed, per `k`, `PriceTwo.sym_box_price_at_op` / `low_box_price_at_op` (the
`box_disc_three_way` box price), whose conclusion is the VERBATIM `hpriceSym`/`hpriceLow` slot of
`SwitchW2.PloW_sym_of_box_disc` / `PloW_low_of_box_disc`.  The consumers sum over ALL
`k ∈ range (Nat.log 2 x + 1)`.

## ★ CATCH #73 — the sym single middle `k` is LIVE and UNPRICED by landed atoms ★  (§1)

Do this EARLY (fin6 flagged it the only design risk).  The sym carrier's three `k`-regimes:

* **vanish** (`pieceM k ≤ y`, i.e. `2^{k+1}−1 ≤ y`): `blockAlphaSym = 0`
  (`blockAlphaSym_eq_zero_of_pieceM_le`), so `PsymK k = 0`.
* **collapsed** (`y ≤ pieceN k`, i.e. `y < 2^k`): `max y (pieceN k) = pieceN k`, priced by
  `sym_box_hprice_at_2pow_band`.
* **the single MIDDLE `k`** (`pieceN k < y < pieceM k`, i.e. `2^k ≤ y < 2^{k+1}−1`): the sym
  carrier is LIVE (large prime `p₂ ∈ (y, pieceM k]` ≠ ∅) and the box is inhabited
  (`2^i ∈ (x^{2/3}/8, x^{2/3}]` ≠ ∅), yet `y ≤ pieceN k` FAILS, so `sym_box_hprice_at_2pow_band`
  cannot fire.

Tracing the consumer (mandate step 2, option (c)): `PloW_sym_of_box_disc`'s per-`k` requirement
uses the indicator `blockPrimeInd (max y (pieceN k)) = blockPrimeInd y` (the OUTER prime `n > y`),
which is intrinsic to `bandSymRectDiscW` via `norm_symRectW_eq` — there is no alternate route.  The
middle `k` sits inside `range (Nat.log 2 x + 1)` (`k ≈ Nat.log 2 y ≈ (1/3)·log₂ x`), so the
consumer GENUINELY demands `PsymK (middle k)`.

The carrier COLLAPSES to a low shape — `blockAlphaSym z y ε₀ j (pieceN k) (pieceM k) =
blockAlphaLow z y ε₀ j (pieceM k)` on `pieceN k ≤ y` (`blockAlphaSym_eq_blockAlphaLow_of_le`,
§1) — but the INDICATOR stays `blockPrimeInd y`, NOT the low leg's `blockPrimeInd (pieceN k)`.
No landed terminal prices this combination: `medium_box_price_at_op_band`/`_core` hardcode
`blockPrimeInd (pieceN k) → blockPrimeInd (2^k)` (`sum_norm_apDiscBilinCutoff_pieceN`), pricing
at `log (2^k)`.  The underlying terminal `medium_survivor_price_sqrtD` COULD price
`blockPrimeInd y` directly at `N := y` (the guards close: `D < (y+1)² ≈ x^{2/3} > D`,
`pieceM k ≤ 2y`, `y ≤ pieceM k` on the middle `k`, `x^{1/3}/8 ≤ y` at `opY` feeds
`d0_window_of_XM_band` with `N := y` VERBATIM), but ONLY through a fresh
`medium_box_price_core`-analogue at `N := y` — new statement-level machinery emitting a DIFFERENT
price shape (constants at `log y`, not `log 2^k`) that fin8's `hSum` budget must be redesigned to
absorb.  That is Fable/human-directed.

Per mandate step 2, this is STOP-AND-FLAG = catch #73 (exact shapes recorded in the flags entry
and the §1 lemmas).  The LOW leg is UNAFFECTED (it vanishes exactly on `pieceN k ≤ y`, i.e. on
the middle and vanishing `k`, so no live-but-unpriceable box) and closes fully (`low_rows_at_op`,
§3).  The sym composite (`sym_rows_at_op`, §4) closes the vanish + collapsed regimes and threads
the single middle-`k` price as the one named residual `hMidSym`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## §1 — the sym single middle-`k` treatment (catch #73)

The design-risk part, done first.  §1a is the carrier-collapse identity (the repair artifact for
the Fable session); §1b pins the middle-`k` geometry (`2^k ≤ y < 2^{k+1}`), witnessing that the
middle `k` is a genuine live box, not a vacuous case. -/

/-- **§1a — the sym→low carrier collapse (catch #73 repair artifact).**  When `N ≤ y` (so
`max y N = y`), the symmetric-band carrier equals the low-band carrier at large-prime cap `M`:
`blockAlphaSym z y ε₀ j N M = blockAlphaLow z y ε₀ j M`.  Both count semiprimes `p₁·p₂` with
`z ≤ p₁ ≤ y < p₂ ≤ M`.  This shows the middle-`k` sym carrier is a LOW carrier at
`N' = pieceM k`; the OBSTRUCTION (catch #73) is that its indicator is still `blockPrimeInd y`,
not the low leg's `blockPrimeInd (pieceN k)`. -/
theorem blockAlphaSym_eq_blockAlphaLow_of_le {z y : ℕ} {ε₀ : ℝ} {j N M : ℕ} (h : N ≤ y) :
    blockAlphaSym z y ε₀ j N M = blockAlphaLow z y ε₀ j M := by
  funext m
  unfold blockAlphaSym blockAlphaLow
  rw [max_eq_left h]

/-- **§1b — the middle-`k` lower geometry.**  `pieceN k < y` gives `2^k ≤ y` (the
middle/vanishing regime lower edge; `pieceN k = 2^k − 1`). -/
theorem two_pow_le_of_pieceN_lt {y k : ℕ} (h : pieceN k < y) : 2 ^ k ≤ y := by
  unfold pieceN at h
  have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- **§1b — the middle-`k` upper geometry.**  `y < pieceM k` gives `y < 2^{k+1}` (the middle
regime upper edge; `pieceM k = 2^{k+1} − 1`). -/
theorem lt_two_pow_succ_of_lt_pieceM {y k : ℕ} (h : y < pieceM k) : y < 2 ^ (k + 1) := by
  unfold pieceM at h
  have h1 : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- **§1b — the middle-`k` band floor.**  On the single middle `k` (`pieceN k < y < pieceM k`)
with the operating fact `x^{1/3}/8 ≤ y`, the band floor `x^{1/3}/16 ≤ 2^k` holds (via
`2^k > y/2 ≥ x^{1/3}/16`, from `y < 2^{k+1}`).  Recorded to witness that the middle `k`'s box
would clear the band floor — the obstruction (catch #73) is the indicator, not the floor. -/
theorem middle_k_band_floor {x y k : ℕ}
    (hy : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (y : ℝ)) (_hlo : pieceN k < y) (hhi : y < pieceM k) :
    (x : ℝ) ^ ((1 : ℝ) / 3) / 16 ≤ ((2 ^ k : ℕ) : ℝ) := by
  have hup : y < 2 ^ (k + 1) := lt_two_pow_succ_of_lt_pieceM hhi
  have hupR : (y : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hup
  have hpow : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * ((2 ^ k : ℕ) : ℝ) := by
    push_cast [pow_succ]; ring
  rw [hpow] at hupR
  linarith

/-! ## §2 — the band-specific structural row atoms

The rows that come from the band boundary's `m`-floor clause `F < 2^{i+1}` (`F = z·max(y,N)` for
sym, `z·y` for low) and the band `k`-floor (`hDsq`/`hNfloor` via `band_kfloor_of_live`).  These
are the genuinely band-specific pieces (mandate step 3: "the band `X`-floors come from the band
`m`-floor clauses"); the `X·M ≍ x` scaffold rows are already in `ChenFinal` (`boundary_XM_raw`,
`xm_*_bounds`, `boundary_log_bounds`). -/

/-- **§2 — the band `m`-floor clause.**  A boundary box has `F < 2^{i+1}` (the `dyadicBoundary`
membership's third clause). -/
theorem band_boundary_F_lt {N M T₁ T₂ F K i : ℕ}
    (hi : i ∈ dyadicBoundary N M T₁ T₂ F K) : F < 2 ^ (i + 1) := by
  rw [dyadicBoundary, Finset.mem_filter] at hi
  exact hi.2.2.1

/-- **§2 — row 20 (`F ≤ X`).**  `F < 2^{i+1}` and `X = 2^{i+1}−1` give `F ≤ X` (the survivor sits
above the `m`-floor, i.e. its dyadic top exceeds the floor). -/
theorem band_F_le_X {N M T₁ T₂ F K i X : ℕ}
    (hi : i ∈ dyadicBoundary N M T₁ T₂ F K) (hX : X = 2 ^ (i + 1) - 1) : F ≤ X := by
  have h := band_boundary_F_lt hi
  omega

/-- **§2 — row 9 (`2 ≤ X`).**  With a floor `2 ≤ F` (`z·max(y,N) ≥ 2` at the operating point),
`F < 2^{i+1}` forces `2^{i+1} ≥ 4`, so `X = 2^{i+1}−1 ≥ 3 ≥ 2`. -/
theorem band_two_le_X {N M T₁ T₂ F K i X : ℕ}
    (hi : i ∈ dyadicBoundary N M T₁ T₂ F K) (hX : X = 2 ^ (i + 1) - 1) (hF : 2 ≤ F) : 2 ≤ X := by
  have hFlt := band_boundary_F_lt hi
  have h2i : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
  have h2ipos : 1 ≤ 2 ^ i := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- **§2 — row 14 (`hDsq : D < (2^k+1)²`) via the band `k`-floor.**  At the band floor
`x^{1/3}/8 ≤ 2^k` and `D ≤ √x` with `x` large, `D < (2^k+1)²`: `(2^k)² ≥ x^{2/3}/64 ≫ √x ≥ D`
once `x^{2/3}/64 > √x`, i.e. `x^{1/6} > 64`, i.e. `x > 64^6 ≈ 6.9·10^{10}`. -/
theorem band_hDsq_of_kfloor {x k D : ℕ}
    (hNfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ))
    (hDx : (D : ℝ) ≤ Real.sqrt x) (hx : (10 : ℝ) ^ 48 ≤ (x : ℝ)) :
    D < (2 ^ k + 1) * (2 ^ k + 1) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx
  have h13nn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hxpos.le _
  -- `√x = x^{1/2}`, `x^{2/3} = (x^{1/3})²`
  have hsqrt_eq : Real.sqrt x = (x : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  -- `x^{1/2} ≤ x^{2/3}/64` for `x ≥ 10^{48}` (⟺ `64 ≤ x^{1/6}`)
  have hx16 : (64 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
    have hpow : ((10 : ℝ) ^ (48 : ℕ)) ^ ((1 : ℝ) / 6) = (10 : ℝ) ^ (8 : ℕ) := by
      rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10),
        show ((48 : ℕ) : ℝ) * (1 / 6) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h1 : ((10 : ℝ) ^ (48 : ℕ)) ^ ((1 : ℝ) / 6) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow (by positivity) hx (by norm_num)
    rw [hpow] at h1
    have h2 : (64 : ℝ) ≤ (10 : ℝ) ^ (8 : ℕ) := by norm_num
    linarith
  have h12nn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hxpos.le _
  have hx12 : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ ((2 : ℝ) / 3) / 64 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64)]
    have hsplit : (x : ℝ) ^ ((2 : ℝ) / 3) = (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_add hxpos, show (1 : ℝ) / 2 + 1 / 6 = 2 / 3 by norm_num]
    rw [hsplit]
    nlinarith [hx16, h12nn]
  -- `x^{2/3} = x^{1/3}·x^{1/3}`, so `x^{2/3}/64 = (x^{1/3}/8)·(x^{1/3}/8) ≤ (2^k)·(2^k)`
  have hx13x13 : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) = (x : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add hxpos, show (1 : ℝ) / 3 + 1 / 3 = 2 / 3 by norm_num]
  have h8pos : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) / 8 := by positivity
  have hsq : ((x : ℝ) ^ ((1 : ℝ) / 3) / 8) * ((x : ℝ) ^ ((1 : ℝ) / 3) / 8)
      ≤ ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) := mul_self_le_mul_self h8pos hNfloor
  have heq64 : ((x : ℝ) ^ ((1 : ℝ) / 3) / 8) * ((x : ℝ) ^ ((1 : ℝ) / 3) / 8)
      = (x : ℝ) ^ ((2 : ℝ) / 3) / 64 := by rw [← hx13x13]; ring
  -- assemble: `D ≤ √x ≤ x^{2/3}/64 = (x^{1/3}/8)² ≤ (2^k)² < (2^k+1)²`
  have hDR : (D : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) := by
    calc (D : ℝ) ≤ Real.sqrt x := hDx
      _ = (x : ℝ) ^ ((1 : ℝ) / 2) := hsqrt_eq
      _ ≤ (x : ℝ) ^ ((2 : ℝ) / 3) / 64 := hx12
      _ = ((x : ℝ) ^ ((1 : ℝ) / 3) / 8) * ((x : ℝ) ^ ((1 : ℝ) / 3) / 8) := heq64.symm
      _ ≤ ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) := hsq
  have hDnat : D ≤ (2 ^ k) * (2 ^ k) := by
    have h : ((D : ℕ) : ℝ) ≤ (((2 ^ k) * (2 ^ k) : ℕ) : ℝ) := by
      push_cast; push_cast at hDR; linarith
    exact_mod_cast h
  have hpos : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
  nlinarith [hDnat, hpos]

/-! ## §3 — the fresh operating-value rows (deliverable 3)

The polylog/sqrt/`D`-scale rows of the `_band` legs at the operating point, as ∃-`x₁` bundles
mirroring `HeadlineW2.a12_*`.  `log3pow_le_rpow` is the `(log x + 3)^E ≤ x^c` engine (the scaffold
gives `L = log(X·M) ≤ log x + 3`, `a12_logpow_le_rpow` gives `(log x)^E ≤ x^c`).  Rows keyed to the
band `X`-floor `x^{11/24}/8 ≤ X` (from `z·y ≤ X` at `opZ·opY ≥ x^{11/24}/4`), the band `M`-floor
`x^{1/3}/8 ≤ M` (from `2^k ≤ pieceM k`), and `D := opD x ≤ x^{1/2−9·10⁻⁵}`.  The `X·M ≍ x` scale
rows come from `ChenFinal.xm_*_bounds`. -/

/-- **§3 — the `(log x + 3)^E ≤ x^c` engine.**  `a12_logpow_le_rpow` with the shifted base:
`log x + 3 ≤ 2·log x` (`log x ≥ 3`) then `2^E·(log x)^E ≤ x^{c/2}·x^{c/2}` past the constant-absorb
threshold. -/
theorem log3pow_le_rpow (E c : ℝ) (hE : 0 ≤ E) (hc : 0 < c) :
    ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x → (Real.log x + 3) ^ E ≤ (x : ℝ) ^ c := by
  obtain ⟨x₂, h₂⟩ := a12_logpow_le_rpow E (c / 2) hE (by linarith)
  obtain ⟨x₃, h₃⟩ := a12_log_ge (max 3 (E * Real.log 2 / (c / 2)))
  refine ⟨max x₂ x₃, fun x hx => ?_⟩
  obtain ⟨hexpx, hlogx⟩ := h₃ x (le_trans (le_max_right _ _) hx)
  have hpow := h₂ x (le_trans (le_max_left _ _) hx)
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpx
  have hL3 : (3 : ℝ) ≤ Real.log x := le_trans (le_max_left _ _) hlogx
  have hLmargin : E * Real.log 2 / (c / 2) ≤ Real.log x := le_trans (le_max_right _ _) hlogx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log x := by linarith
  -- `log x + 3 ≤ 2·log x`
  have hbase : Real.log x + 3 ≤ 2 * Real.log x := by linarith
  have hbnn : (0 : ℝ) ≤ Real.log x + 3 := by linarith
  -- `2^E ≤ x^{c/2}`
  have hcpos : (0 : ℝ) < c / 2 := by linarith
  have h2E : (2 : ℝ) ^ E ≤ (x : ℝ) ^ (c / 2) := by
    have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hkey : E * Real.log 2 ≤ Real.log (x : ℝ) * (c / 2) := by
      have h := mul_le_mul_of_nonneg_right hLmargin hcpos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hcpos)] at h
    calc (2 : ℝ) ^ E = Real.exp (Real.log 2 * E) := by
          rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
      _ ≤ Real.exp (Real.log (x : ℝ) * (c / 2)) := Real.exp_le_exp.mpr (by nlinarith [hkey])
      _ = (x : ℝ) ^ (c / 2) := (Real.rpow_def_of_pos hxpos _).symm
  calc (Real.log x + 3) ^ E ≤ (2 * Real.log x) ^ E := Real.rpow_le_rpow hbnn hbase hE
    _ = (2 : ℝ) ^ E * (Real.log x) ^ E := Real.mul_rpow (by norm_num) hL0
    _ ≤ (x : ℝ) ^ (c / 2) * (x : ℝ) ^ (c / 2) :=
        mul_le_mul h2E hpow (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hxpos.le _)
    _ = (x : ℝ) ^ c := by rw [← Real.rpow_add hxpos]; congr 1; ring

/-- **§3 — the sqrt-floor engine (rows 16/17/19).**  For a value `V` with `x^γ/8 ≤ V`,
`(log x + 3)^E ≤ √V` for large `x`: `√V ≥ x^{γ/2}/3` (since `√(1/8) ≥ 1/3`) and
`(log x + 3)^E ≤ x^{γ/3} ≤ x^{γ/2}/3` (`log3pow_le_rpow` + `3 ≤ x^{γ/6}`). -/
theorem poly3_le_sqrt_floor (E γ : ℝ) (hE : 0 ≤ E) (hγ : 0 < γ) :
    ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x → ∀ V : ℕ, (x : ℝ) ^ γ / 8 ≤ (V : ℝ) →
      (Real.log x + 3) ^ E ≤ Real.sqrt (V : ℝ) := by
  obtain ⟨x₂, h₂⟩ := log3pow_le_rpow E (γ / 3) hE (by linarith)
  obtain ⟨x₃, h₃⟩ := a12_log_ge (max 1 (Real.log 3 / (γ / 6)))
  refine ⟨max x₂ x₃, fun x hx V hV => ?_⟩
  obtain ⟨hexpx, hlogx⟩ := h₃ x (le_trans (le_max_right _ _) hx)
  have hstep1 := h₂ x (le_trans (le_max_left _ _) hx)
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpx
  have hγ6pos : (0 : ℝ) < γ / 6 := by linarith
  have hmargin : Real.log 3 / (γ / 6) ≤ Real.log x := le_trans (le_max_right _ _) hlogx
  -- `3 ≤ x^{γ/6}`
  have h3x : (3 : ℝ) ≤ (x : ℝ) ^ (γ / 6) := by
    have hkey : Real.log 3 ≤ Real.log (x : ℝ) * (γ / 6) := by
      have h := mul_le_mul_of_nonneg_right hmargin hγ6pos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hγ6pos)] at h
    calc (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log (x : ℝ) * (γ / 6)) := Real.exp_le_exp.mpr (by nlinarith [hkey])
      _ = (x : ℝ) ^ (γ / 6) := (Real.rpow_def_of_pos hxpos _).symm
  -- `x^{γ/3} ≤ x^{γ/2}/3`
  have hxγ3nn : (0 : ℝ) ≤ (x : ℝ) ^ (γ / 3) := Real.rpow_nonneg hxpos.le _
  have hsplit : (x : ℝ) ^ (γ / 2) = (x : ℝ) ^ (γ / 3) * (x : ℝ) ^ (γ / 6) := by
    rw [← Real.rpow_add hxpos]; congr 1; ring
  have hx32 : (x : ℝ) ^ (γ / 3) ≤ (x : ℝ) ^ (γ / 2) / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3), hsplit]
    nlinarith [h3x, hxγ3nn]
  -- `√V ≥ √(x^γ/8) = x^{γ/2}/√8 ≥ x^{γ/2}/3`
  have hsqrtV : (x : ℝ) ^ (γ / 2) / 3 ≤ Real.sqrt (V : ℝ) := by
    have hVnn : (0 : ℝ) ≤ (x : ℝ) ^ γ / 8 := by positivity
    have hmono : Real.sqrt ((x : ℝ) ^ γ / 8) ≤ Real.sqrt (V : ℝ) := Real.sqrt_le_sqrt hV
    have hsq8 : Real.sqrt ((x : ℝ) ^ γ / 8) = (x : ℝ) ^ (γ / 2) / Real.sqrt 8 := by
      rw [Real.sqrt_div' _ (by norm_num), Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]
      · congr 2; ring
    have h8lt : Real.sqrt 8 ≤ 3 := by
      rw [show (3 : ℝ) = Real.sqrt 9 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hxγ2nn : (0 : ℝ) ≤ (x : ℝ) ^ (γ / 2) := Real.rpow_nonneg hxpos.le _
    have h8pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
    have hle : (x : ℝ) ^ (γ / 2) / 3 ≤ (x : ℝ) ^ (γ / 2) / Real.sqrt 8 :=
      div_le_div_of_nonneg_left hxγ2nn h8pos h8lt
    rw [hsq8] at hmono; linarith
  calc (Real.log x + 3) ^ E ≤ (x : ℝ) ^ (γ / 3) := hstep1
    _ ≤ (x : ℝ) ^ (γ / 2) / 3 := hx32
    _ ≤ Real.sqrt (V : ℝ) := hsqrtV

/-- **§3 — the `D`-scale engine (rows 13/18).**  For `D ≤ x^{1/2−9·10⁻⁵}` (the `opD` bound) and
`W ≥ x^{1/2}/2` (a `√(X·M)` lower bound), `D·(log x + 3)^E ≤ W` for large `x`: the product is
`≤ x^{1/2−9·10⁻⁵}·x^{9/200000} = x^{1/2−9/200000} ≤ x^{1/2}/2 ≤ W` (the polylog `(log x+3)^E`
absorbed under `x^{9/200000}`, the factor `2` under `2 ≤ x^{9/200000}`). -/
theorem poly3_mul_le_sqrtXM (E : ℝ) (hE : 0 ≤ E) :
    ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x → ∀ (D : ℕ) (W : ℝ),
      (D : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) → (x : ℝ) ^ ((1 : ℝ) / 2) / 2 ≤ W →
      (D : ℝ) * (Real.log x + 3) ^ E ≤ W := by
  obtain ⟨x₂, h₂⟩ := log3pow_le_rpow E (9 / 200000) hE (by norm_num)
  obtain ⟨x₃, h₃⟩ := a12_log_ge (max 1 (Real.log 2 / (9 / 200000)))
  refine ⟨max x₂ x₃, fun x hx D W hD hW => ?_⟩
  obtain ⟨hexpx, hlogx⟩ := h₃ x (le_trans (le_max_right _ _) hx)
  have hpoly := h₂ x (le_trans (le_max_left _ _) hx)
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpx
  have hL0 : (0 : ℝ) ≤ Real.log x := le_trans (by norm_num) (le_trans (le_max_left _ _) hlogx)
  have hpolynn : (0 : ℝ) ≤ (Real.log x + 3) ^ E := Real.rpow_nonneg (by linarith) _
  have hmargin : Real.log 2 / (9 / 200000) ≤ Real.log x := le_trans (le_max_right _ _) hlogx
  -- `2 ≤ x^{9/200000}`
  have h2x : (2 : ℝ) ≤ (x : ℝ) ^ ((9 : ℝ) / 200000) := by
    have hkey : Real.log 2 ≤ Real.log (x : ℝ) * ((9 : ℝ) / 200000) := by
      have h := mul_le_mul_of_nonneg_right hmargin (by norm_num : (0 : ℝ) ≤ (9 : ℝ) / 200000)
      rwa [div_mul_cancel₀ _ (by norm_num : ((9 : ℝ) / 200000) ≠ 0)] at h
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log (x : ℝ) * ((9 : ℝ) / 200000)) :=
          Real.exp_le_exp.mpr (by nlinarith [hkey])
      _ = (x : ℝ) ^ ((9 : ℝ) / 200000) := (Real.rpow_def_of_pos hxpos _).symm
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hmid : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (x : ℝ) ^ ((9 : ℝ) / 200000)
      = (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 200000) := by
    rw [← Real.rpow_add hxpos]; congr 1; norm_num
  have hxhalfnn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 200000) := Real.rpow_nonneg hxpos.le _
  have hupper : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 200000) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 200000) * 2
        ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 200000) * (x : ℝ) ^ ((9 : ℝ) / 200000) :=
          mul_le_mul_of_nonneg_left h2x hxhalfnn
      _ = (x : ℝ) ^ ((1 : ℝ) / 2) := by rw [← Real.rpow_add hxpos]; congr 1; norm_num
  calc (D : ℝ) * (Real.log x + 3) ^ E
      ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) * (x : ℝ) ^ ((9 : ℝ) / 200000) :=
        mul_le_mul hD hpoly hpolynn (Real.rpow_nonneg hxpos.le _)
    _ = (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 200000) := hmid
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) / 2 := hupper
    _ ≤ W := hW

/-- **§3 — row 23 (`hfloor`).**  `(3/log 2)^8·x^{1/6}·Lb^18 ≤ √F` for `F ≥ x^{11/24}/8` and
`Lb ≤ log x + 3`.  `√F ≥ x^{11/48}/3`; `Lb^18 ≤ (log x+3)^18 ≤ x^{1/32}`; the LHS is
`≤ C₀·x^{1/6}·x^{1/32} = C₀·x^{19/96}`, and `3·C₀ ≤ x^{1/32}` closes `3·C₀·x^{19/96} ≤ x^{22/96}
= x^{11/48}` (`C₀ = (3/log 2)^8`, room `x^{1/16}` from the gate). -/
theorem row23_at_op :
    ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x → ∀ (F : ℕ) (Lb : ℝ),
      (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (F : ℝ) → 0 ≤ Lb → Lb ≤ Real.log x + 3 →
      ((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
        ≤ Real.sqrt (F : ℝ) := by
  set C0 : ℝ := ((3 : ℝ) / Real.log 2) ^ 8 with hC0def
  have hC0pos : 0 < C0 := by
    rw [hC0def]; have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num); positivity
  obtain ⟨x₂, h₂⟩ := log3pow_le_rpow ((13 : ℝ) + 5) (1 / 32) (by norm_num) (by norm_num)
  obtain ⟨x₃, h₃⟩ := a12_log_ge (max 1 (Real.log (3 * C0) / (1 / 32)))
  refine ⟨max x₂ x₃, fun x hx F Lb hF hLb0 hLbub => ?_⟩
  obtain ⟨hexpx, hlogx⟩ := h₃ x (le_trans (le_max_right _ _) hx)
  have hpoly := h₂ x (le_trans (le_max_left _ _) hx)
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpx
  have hL0 : (0 : ℝ) ≤ Real.log x := le_trans (by norm_num) (le_trans (le_max_left _ _) hlogx)
  have hmargin : Real.log (3 * C0) / (1 / 32) ≤ Real.log x := le_trans (le_max_right _ _) hlogx
  -- `3·C0 ≤ x^{1/32}`
  have h3C0x : 3 * C0 ≤ (x : ℝ) ^ ((1 : ℝ) / 32) := by
    have hkey : Real.log (3 * C0) ≤ Real.log (x : ℝ) * ((1 : ℝ) / 32) := by
      have h := mul_le_mul_of_nonneg_right hmargin (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 32)
      rwa [div_mul_cancel₀ _ (by norm_num : ((1 : ℝ) / 32) ≠ 0)] at h
    calc 3 * C0 = Real.exp (Real.log (3 * C0)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (Real.log (x : ℝ) * ((1 : ℝ) / 32)) := Real.exp_le_exp.mpr (by nlinarith [hkey])
      _ = (x : ℝ) ^ ((1 : ℝ) / 32) := (Real.rpow_def_of_pos hxpos _).symm
  -- `Lb^18 ≤ (log x+3)^18 ≤ x^{1/32}`
  have hLbpow : Lb ^ ((13 : ℝ) + 5) ≤ (x : ℝ) ^ ((1 : ℝ) / 32) :=
    le_trans (Real.rpow_le_rpow hLb0 hLbub (by norm_num)) hpoly
  -- `√F ≥ x^{11/48}/3`
  have hsqrtF : (x : ℝ) ^ ((11 : ℝ) / 48) / 3 ≤ Real.sqrt (F : ℝ) := by
    have hmono : Real.sqrt ((x : ℝ) ^ ((11 : ℝ) / 24) / 8) ≤ Real.sqrt (F : ℝ) :=
      Real.sqrt_le_sqrt hF
    have hsq8 : Real.sqrt ((x : ℝ) ^ ((11 : ℝ) / 24) / 8)
        = (x : ℝ) ^ ((11 : ℝ) / 48) / Real.sqrt 8 := by
      rw [Real.sqrt_div' _ (by norm_num), Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]
      · congr 2; norm_num
    have h8lt : Real.sqrt 8 ≤ 3 := by
      rw [show (3 : ℝ) = Real.sqrt 9 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hxnn : (0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 48) := Real.rpow_nonneg hxpos.le _
    have h8pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
    have hle : (x : ℝ) ^ ((11 : ℝ) / 48) / 3 ≤ (x : ℝ) ^ ((11 : ℝ) / 48) / Real.sqrt 8 :=
      div_le_div_of_nonneg_left hxnn h8pos h8lt
    rw [hsq8] at hmono; linarith
  -- assemble
  have hx16nn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hxpos.le _
  have hstep : C0 * (x : ℝ) ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
      ≤ C0 * (x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 32) :=
    mul_le_mul_of_nonneg_left hLbpow (by positivity)
  have hprod : C0 * (x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 32)
      ≤ (x : ℝ) ^ ((11 : ℝ) / 48) / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have hx6_32 : (x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 32)
        = (x : ℝ) ^ ((19 : ℝ) / 96) := by rw [← Real.rpow_add hxpos]; congr 1; norm_num
    have hx3_96 : (x : ℝ) ^ ((19 : ℝ) / 96) * (x : ℝ) ^ ((1 : ℝ) / 32)
        = (x : ℝ) ^ ((11 : ℝ) / 48) := by rw [← Real.rpow_add hxpos]; congr 1; norm_num
    have hx19nn : (0 : ℝ) ≤ (x : ℝ) ^ ((19 : ℝ) / 96) := Real.rpow_nonneg hxpos.le _
    calc C0 * (x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 32) * 3
        = 3 * C0 * (x : ℝ) ^ ((19 : ℝ) / 96) := by rw [← hx6_32]; ring
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 32) * (x : ℝ) ^ ((19 : ℝ) / 96) :=
          mul_le_mul_of_nonneg_right h3C0x hx19nn
      _ = (x : ℝ) ^ ((11 : ℝ) / 48) := by rw [mul_comm, hx3_96]
  calc C0 * (x : ℝ) ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
      ≤ C0 * (x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 32) := hstep
    _ ≤ (x : ℝ) ^ ((11 : ℝ) / 48) / 3 := hprod
    _ ≤ Real.sqrt (F : ℝ) := hsqrtF

/-- **§3 — `band_price_rows_at_op` (deliverable 3).**  The six polylog/sqrt/`D`-scale rows of the
`_band` legs (rows 13, 16, 17, 18, 19, 23 in the header table) at the operating point, as one
∃-`x₁` bundle over a boundary box.  Inputs: the raw `X·M` window (`x/2+1 < X·M ≤ 4x`,
`ChenFinal.boundary_XM_raw`), the band floors `x^{11/24}/8 ≤ X` (from `z·y ≤ X`) and
`x^{1/3}/8 ≤ M` (from `2^k ≤ pieceM k`), the band `F`-floor `x^{11/24}/8 ≤ F`, the `opD` bound
`D ≤ x^{1/2−9·10⁻⁵}`, and `0 ≤ Lb ≤ log x + 3`.  Discharged by the three engines above +
`row23_at_op`.  (Rows 6/8/9/10/11/20/21/22/24 are `SUPPLIED` by `§2`/scaffold/`opf`; rows 12/15 are
the `a12_level`/product-floor residuals — see the report.) -/
theorem band_price_rows_at_op :
    ∃ x₁ : ℕ, 10 ^ 48 ≤ x₁ ∧ ∀ (x : ℕ), x₁ ≤ x → ∀ (X M D F : ℕ) (Lb : ℝ),
      x / 2 + 1 < X * M → X * M ≤ 4 * x →
      (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (X : ℝ) →
      (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (M : ℝ) →
      (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (F : ℝ) →
      (D : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) →
      0 ≤ Lb → Lb ≤ Real.log x + 3 →
      ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (15 : ℝ))
      ∧ ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ))
      ∧ ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (M : ℝ))
      ∧ ((D : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt ((X : ℝ) * (M : ℝ)))
      ∧ ((Real.log ((X : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt (M : ℝ))
      ∧ (((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
          ≤ Real.sqrt (F : ℝ)) := by
  obtain ⟨xa, ha⟩ := poly3_le_sqrt_floor ((13 : ℝ) + 3) ((11 : ℝ) / 24) (by norm_num) (by norm_num)
  obtain ⟨xb, hb⟩ := poly3_le_sqrt_floor ((13 : ℝ) + 3) ((1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨xc, hc⟩ := poly3_le_sqrt_floor ((13 : ℝ) + 5) ((1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨xd, hd⟩ := poly3_mul_le_sqrtXM (15 : ℝ) (by norm_num)
  obtain ⟨xe, he⟩ := poly3_mul_le_sqrtXM ((13 : ℝ) + 5) (by norm_num)
  obtain ⟨xf, hf⟩ := row23_at_op
  refine ⟨10 ^ 48 + xa + xb + xc + xd + xe + xf, by omega,
    fun x hx X M D F Lb hXMlo hXMhi hXlo hMlo hFlo hDub hLb0 hLbub => ?_⟩
  have hx48 : 10 ^ 48 ≤ x := by omega
  have hxa : xa ≤ x := by omega
  have hxb : xb ≤ x := by omega
  have hxc : xc ≤ x := by omega
  have hxd : xd ≤ x := by omega
  have hxe : xe ≤ x := by omega
  have hxf : xf ≤ x := by omega
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hx2 : 2 ≤ x := le_trans (by norm_num) hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hxR
  -- the scale facts (`ChenFinal` scaffold)
  obtain ⟨hLlo, hLub⟩ := xm_log_bounds hx2 hXMlo hXMhi
  obtain ⟨hsqrtlo, -⟩ := xm_sqrt_bounds hXMlo hXMhi
  have hL96 : (96 : ℝ) ≤ Real.log x := opf_log_ge_96 x hxR
  set L : ℝ := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  have hLnn : (0 : ℝ) ≤ L := by rw [hLdef]; linarith
  have hLlub : L ≤ Real.log x + 3 := by rw [hLdef]; linarith
  -- the sqrt lower bound `x^{1/2}/2 ≤ √(X·M)`
  have hWlo : (x : ℝ) ^ ((1 : ℝ) / 2) / 2 ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) := by
    rw [← Real.sqrt_eq_rpow]; have : (1 / 2 : ℝ) * Real.sqrt x = Real.sqrt x / 2 := by ring
    rw [← this]; exact hsqrtlo
  -- helper: `L^E ≤ (log x+3)^E` for `E ≥ 0`
  have hLpow : ∀ E : ℝ, 0 ≤ E → L ^ E ≤ (Real.log x + 3) ^ E :=
    fun E hE => Real.rpow_le_rpow hLnn hLlub hE
  -- Row 16
  have hrow16 : L ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ) :=
    le_trans (hLpow _ (by norm_num)) (ha x hxa X hXlo)
  -- Row 17
  have hrow17 : L ^ ((13 : ℝ) + 3) ≤ Real.sqrt (M : ℝ) :=
    le_trans (hLpow _ (by norm_num)) (hb x hxb M hMlo)
  -- Row 19
  have hrow19 : L ^ ((13 : ℝ) + 5) ≤ Real.sqrt (M : ℝ) :=
    le_trans (hLpow _ (by norm_num)) (hc x hxc M hMlo)
  -- Row 18
  have hrow18 : (D : ℝ) * L ^ ((13 : ℝ) + 5) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) := by
    have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
    refine le_trans (mul_le_mul_of_nonneg_left (hLpow _ (by norm_num)) hDnn) ?_
    exact he x hxe D _ hDub hWlo
  -- Row 13 (in the `≤ √/L^15` form)
  have hrow13 : (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / L ^ (15 : ℝ) := by
    have hL15pos : (0 : ℝ) < L ^ (15 : ℝ) := by
      apply Real.rpow_pos_of_pos; rw [hLdef]; linarith
    rw [le_div_iff₀ hL15pos]
    have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
    refine le_trans (mul_le_mul_of_nonneg_left (hLpow _ (by norm_num)) hDnn) ?_
    exact hd x hxd D _ hDub hWlo
  -- Row 23
  have hrow23 : ((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
      ≤ Real.sqrt (F : ℝ) :=
    hf x hxf F Lb hFlo hLb0 hLbub
  exact ⟨hrow13, hrow16, hrow17, hrow18, hrow19, hrow23⟩

/-! ## §4 — the composites feeding the consumers (deliverable 4)

`low_rows_at_op` reduces `low_box_hprice_at_2pow_band` at a live-low box (`y < pieceN k`) by
discharging the band-specific rows (§2: `hNfloor` via `band_kfloor_of_live`, `hDsq` via
`band_hDsq_of_kfloor`, `2 ≤ X` via `band_two_le_X`, `F ≤ X` via `band_F_le_X`).  The consumer-feed
examples (`low_price_feeds_consumer`, mirroring the sym one at `PriceTwo`) witness that the per-`k`
box prices slot character-for-character into `PloW_low_of_box_disc` / `PloW_sym_of_box_disc`
(anti-#69). -/

open Classical in
/-- **§4 — `low_price_feeds_consumer` (anti-#69, the low leg).**  The per-`k` `low_box_price_at_op`
conclusions are EXACTLY the `hdiffK` input `PloW_low_of_box_disc` consumes (`SwitchW2`).  Feeding
them yields the feeder's `bandLowDiscW`-sum bound — the low analogue of `PriceTwo`'s sym example,
witnessing the character-for-character slot match. -/
example {x z y : ℕ} {ε₀ : ℝ} {j X Q a : ℕ} (Ps : ℕ) (bound : ℝ) (K : ℕ) (Price : ℕ → ℕ → ℝ)
    (hQ1 : 1 ≤ Q) (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x)
    (hlow : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price k i) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandLowDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
            (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price k i :=
  PloW_low_of_box_disc Ps bound
    (fun k => ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price k i)
    hQ1 hxX hxlo hlow

/-- **§4 — `low_rows_at_op` (deliverable 4, the low leg).**  `low_box_hprice_at_2pow_band` at a
live-low box (`y < pieceN k`) with the band-specific rows (`hNfloor`, `hDsq`, `2 ≤ X`, `F ≤ X`,
`2 ≤ L`, `D ≤ X·M`) and the fresh polylog/sqrt/`D`-scale rows (`hDscale`, `hXsqrt`, `hMsqrt`,
`herr_lev`, `herr_Mlev`, `hfloor` at `Lb := log x + 3`) DISCHARGED internally (via §2/§3).  The
surviving side conditions are the caller rows `N₀ ≤ 2^k`, `1 ≤ D`, `x^{11/24}/8 ≤ D`,
`Q·(QR·Dlev) ≤ D`, `D ≤ √x`, the `habs` row, and the band floors `x^{11/24}/8 ≤ X/F`, `2 ≤ z·y`
(the `opZ·opY ≥ x^{11/24}/4` facts fin8 supplies).  Conclusion: the per-box two-`T` sum
`≤ 2·(Kerr price)` — the `hprice` slot of `low_box_price_at_op`. -/
theorem low_rows_at_op (z y Ps Q a : ℕ) (hQ1 : 1 ≤ Q) (hPspos : 0 < Ps)
    (hQPs : Nat.Coprime Q Ps) (hQa2 : Nat.Coprime Q (a + 2))
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    ∃ (Kc : ℝ) (N₀ x₁ : ℕ), 0 < Kc ∧
      ∀ (x : ℕ) (ε₀ : ℝ) (j k i : ℕ) (Krange : ℕ) (QR : ℝ) (Dlev D : ℕ),
        x₁ ≤ x →
        2 ≤ k →
        y < pieceN k →
        (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (y : ℝ) →
        2 ≤ z * y →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((z * y : ℕ) : ℝ) →
        i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) Krange →
        N₀ ≤ 2 ^ k →
        1 ≤ D →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
        (D : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ)
                / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) →
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1)) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                    (min (z * pieceN k + 1) (x + 1)) (x + 1)) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ 2 * ((Kbeta_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                    (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18
                + (6 * (Km_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                          (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                        * Kbeta'_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                            (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 15360 + 1)))
              * (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))
              / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨Kc, N₀, hK0, hbody⟩ := low_box_hprice_at_2pow_band z y Ps Q a hQ1 hPspos hQPs hQa2 hPodd
  obtain ⟨x₂, hx₂48, hrows⟩ := band_price_rows_at_op
  refine ⟨Kc, N₀, max x₂ (⌈Real.exp (10 ^ 10)⌉₊ + 1), hK0,
    fun x ε₀ j k i Krange QR Dlev D hx hk hylt hy hzy2 hXlo hFlo hi hN₀ hD1 hDge_x hDbnd hDub
      habs => ?_⟩
  -- global scale facts
  have hx2x : x₂ ≤ x := le_trans (le_max_left _ _) hx
  have hxexp : ⌈Real.exp (10 ^ 10)⌉₊ + 1 ≤ x := le_trans (le_max_right _ _) hx
  have htower : Real.exp (10 ^ 10) ≤ (x : ℝ) := by
    calc Real.exp (10 ^ 10) ≤ (⌈Real.exp (10 ^ 10)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (x : ℝ) := by exact_mod_cast (by omega : ⌈Real.exp (10 ^ 10)⌉₊ ≤ x)
  have hx48 : 10 ^ 48 ≤ x := le_trans hx₂48 hx2x
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hx2 : 2 ≤ x := le_trans (by norm_num) hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hxR
  set X : ℕ := 2 ^ (i + 1) - 1 with hXdef
  -- band-specific discharges (§2)
  have hylt2 : y < 2 ^ k := lt_two_pow_of_lt_pieceN hylt
  have hNfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ) := band_kfloor_of_live hy hylt2
  have hDx : (D : ℝ) ≤ Real.sqrt x := by
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [hxpos]) (by norm_num)
    rw [Real.sqrt_eq_rpow]; linarith [hDub]
  have hDsq : D < (2 ^ k + 1) * (2 ^ k + 1) := band_hDsq_of_kfloor hNfloor hDx hxR
  have hFX : (z * y : ℕ) ≤ X := band_F_le_X hi hXdef
  have hX2 : 2 ≤ X := band_two_le_X hi hXdef hzy2
  -- the raw `X·M` window + scale facts (scaffold)
  obtain ⟨hXMlo, hXMhi⟩ := boundary_XM_raw hi
  rw [← hXdef] at hXMlo hXMhi
  obtain ⟨hLlo, hLub⟩ := boundary_log_bounds hx2 hi
  rw [← hXdef] at hLlo hLub
  have hL96 : (96 : ℝ) ≤ Real.log x := opf_log_ge_96 x hxR
  have hL2 : 2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) := by linarith [hLlo]
  -- M-floor `x^{1/3}/8 ≤ pieceM k`
  have hMlo : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (pieceM k : ℝ) := by
    have h2kM : ((2 ^ k : ℕ) : ℝ) ≤ (pieceM k : ℝ) := by exact_mod_cast two_pow_le_pieceM k
    linarith [hNfloor]
  -- the fresh rows (§3) at `Lb := log x + 3`
  have hLb0 : (0 : ℝ) ≤ Real.log x + 3 := by linarith
  obtain ⟨hDscale, hXsqrt, hMsqrt, herr_lev, herr_Mlev, hfloor⟩ :=
    hrows x hx2x X (pieceM k) D (z * y) (Real.log x + 3) hXMlo hXMhi hXlo hMlo hFlo hDub hLb0 le_rfl
  -- `L ≤ Lb`, `D ≤ X·M`
  have hLbb : Real.log ((X : ℝ) * (pieceM k : ℝ)) ≤ Real.log x + 3 := by linarith [hLub]
  have hx4R : (4 : ℝ) ≤ (x : ℝ) := by
    have : 4 ≤ x := le_trans (by norm_num) hx48
    exact_mod_cast this
  have hDXM : (D : ℝ) ≤ (X : ℝ) * (pieceM k : ℝ) := by
    have hsx : Real.sqrt x ≤ (x : ℝ) / 2 := by
      rw [show (x : ℝ) / 2 = Real.sqrt (((x : ℝ) / 2) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg (by linarith [hx4R] : (0 : ℝ) ≤ (x : ℝ) - 4) hxpos.le]
    have hXMloR : (x : ℝ) / 2 < (X : ℝ) * (pieceM k : ℝ) := by
      have hxlt : x < 2 * (x / 2 + 1) := by omega
      have hxltR : (x : ℝ) < 2 * ((x / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hxlt
      have h2 : ((x / 2 + 1 : ℕ) : ℝ) ≤ (X : ℝ) * (pieceM k : ℝ) := by
        have hc : ((X * pieceM k : ℕ) : ℝ) = (X : ℝ) * (pieceM k : ℝ) := by push_cast; ring
        rw [← hc]; exact_mod_cast le_of_lt hXMlo
      push_cast at hxltR h2; linarith
    linarith [hDx, hsx]
  -- assemble the `_band` leg
  exact hbody x ε₀ j k i (Real.log x + 3) (z * y) Krange X QR Dlev D hk htower hi hXdef hNfloor
    hN₀ hL2 hX2 hD1 hDge_x hDbnd hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb
    hfloor hDXM

/-- **§4 — `sym_rows_at_op` (deliverable 4, the sym leg, COLLAPSED regime).**  The sym analogue of
`low_rows_at_op` on the collapse strip `y ≤ pieceN k` (`max y (pieceN k) = pieceN k`), discharging
the identical row set via §2/§3 and applying `sym_box_hprice_at_2pow_band`.  Together with the
vanish regime (`pieceM k ≤ y ⟹ blockAlphaSym = 0 ⟹ PsymK k = 0`,
`blockAlphaSym_eq_zero_of_pieceM_le`) this covers every `k` EXCEPT the single middle `k`
(`pieceN k < y < pieceM k`), which is CATCH #73 (see §1): its price is unavailable from landed
atoms and must be threaded by fin8 as the one named residual. -/
theorem sym_rows_at_op (z y Ps Q a : ℕ) (hQ1 : 1 ≤ Q) (hPspos : 0 < Ps)
    (hQPs : Nat.Coprime Q Ps) (hQa2 : Nat.Coprime Q (a + 2))
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    ∃ (Kc : ℝ) (N₀ x₁ : ℕ), 0 < Kc ∧
      ∀ (x : ℕ) (ε₀ : ℝ) (j k i : ℕ) (Krange : ℕ) (QR : ℝ) (Dlev D : ℕ),
        x₁ ≤ x →
        2 ≤ k →
        y ≤ pieceN k →
        (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (y : ℝ) →
        2 ≤ z * y →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((z * y : ℕ) : ℝ) →
        i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) Krange →
        N₀ ≤ 2 ^ k →
        1 ≤ D →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
        (D : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ)
                / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) →
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                  (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (max y (pieceN k))) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                    (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (max y (pieceN k))) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ 2 * ((Kbeta_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                    (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18
                + (6 * (Km_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                          (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                        * Kbeta'_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                            (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 15360 + 1)))
              * (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))
              / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨Kc, N₀, hK0, hbody⟩ := sym_box_hprice_at_2pow_band z y Ps Q a hQ1 hPspos hQPs hQa2 hPodd
  obtain ⟨x₂, hx₂48, hrows⟩ := band_price_rows_at_op
  refine ⟨Kc, N₀, max x₂ (⌈Real.exp (10 ^ 10)⌉₊ + 1), hK0,
    fun x ε₀ j k i Krange QR Dlev D hx hk hyN hy hzy2 hXlo hFlo hi hN₀ hD1 hDge_x hDbnd hDub
      habs => ?_⟩
  have hx2x : x₂ ≤ x := le_trans (le_max_left _ _) hx
  have htower : Real.exp (10 ^ 10) ≤ (x : ℝ) := by
    calc Real.exp (10 ^ 10) ≤ (⌈Real.exp (10 ^ 10)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (x : ℝ) := by
          exact_mod_cast (by omega : ⌈Real.exp (10 ^ 10)⌉₊ ≤ x)
  have hx48 : 10 ^ 48 ≤ x := le_trans hx₂48 hx2x
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hx2 : 2 ≤ x := le_trans (by norm_num) hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hxR
  set X : ℕ := 2 ^ (i + 1) - 1 with hXdef
  have hylt2 : y < 2 ^ k := lt_two_pow_of_le_pieceN hyN
  have hNfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ ((2 ^ k : ℕ) : ℝ) := band_kfloor_of_live hy hylt2
  have hDx : (D : ℝ) ≤ Real.sqrt x := by
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [hxpos]) (by norm_num)
    rw [Real.sqrt_eq_rpow]; linarith [hDub]
  have hDsq : D < (2 ^ k + 1) * (2 ^ k + 1) := band_hDsq_of_kfloor hNfloor hDx hxR
  have hFX : (z * y : ℕ) ≤ X := band_F_le_X hi hXdef
  have hX2 : 2 ≤ X := band_two_le_X hi hXdef hzy2
  obtain ⟨hXMlo, hXMhi⟩ := boundary_XM_raw hi
  rw [← hXdef] at hXMlo hXMhi
  obtain ⟨hLlo, hLub⟩ := boundary_log_bounds hx2 hi
  rw [← hXdef] at hLlo hLub
  have hL96 : (96 : ℝ) ≤ Real.log x := opf_log_ge_96 x hxR
  have hL2 : 2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) := by linarith [hLlo]
  have hMlo : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (pieceM k : ℝ) := by
    have h2kM : ((2 ^ k : ℕ) : ℝ) ≤ (pieceM k : ℝ) := by exact_mod_cast two_pow_le_pieceM k
    linarith [hNfloor]
  have hLb0 : (0 : ℝ) ≤ Real.log x + 3 := by linarith
  obtain ⟨hDscale, hXsqrt, hMsqrt, herr_lev, herr_Mlev, hfloor⟩ :=
    hrows x hx2x X (pieceM k) D (z * y) (Real.log x + 3) hXMlo hXMhi hXlo hMlo hFlo hDub hLb0 le_rfl
  have hLbb : Real.log ((X : ℝ) * (pieceM k : ℝ)) ≤ Real.log x + 3 := by linarith [hLub]
  have hx4R : (4 : ℝ) ≤ (x : ℝ) := by
    have : 4 ≤ x := le_trans (by norm_num) hx48
    exact_mod_cast this
  have hDXM : (D : ℝ) ≤ (X : ℝ) * (pieceM k : ℝ) := by
    have hsx : Real.sqrt x ≤ (x : ℝ) / 2 := by
      rw [show (x : ℝ) / 2 = Real.sqrt (((x : ℝ) / 2) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg (by linarith [hx4R] : (0 : ℝ) ≤ (x : ℝ) - 4) hxpos.le]
    have hXMloR : (x : ℝ) / 2 < (X : ℝ) * (pieceM k : ℝ) := by
      have hxlt : x < 2 * (x / 2 + 1) := by omega
      have hxltR : (x : ℝ) < 2 * ((x / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hxlt
      have h2 : ((x / 2 + 1 : ℕ) : ℝ) ≤ (X : ℝ) * (pieceM k : ℝ) := by
        have hc : ((X * pieceM k : ℕ) : ℝ) = (X : ℝ) * (pieceM k : ℝ) := by push_cast; ring
        rw [← hc]; exact_mod_cast le_of_lt hXMlo
      push_cast at hxltR h2; linarith
    linarith [hDx, hsx]
  exact hbody x ε₀ j k i (Real.log x + 3) (z * y) Krange X QR Dlev D hk hyN htower hi hXdef hNfloor
    hN₀ hL2 hX2 hD1 hDge_x hDbnd hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb
    hfloor hDXM

end Salt.Chen
