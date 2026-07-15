/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.Headline3

/-!
# Node fin8a — `middle_k_price` : the terminal at `N := y` for the single middle `k`

Design: `docs/blueprints/flags.md`, the `2026-07-14 fin7b` entry (★ CATCH #73 ★ — the sym
middle-`k` box, adjudicated SMALL) + the `fin8` re-scope entry.

The sym dichotomy leaves ONE live box uncovered: the single middle `k` with
`pieceN k < y < pieceM k`.  There `blockAlphaSym_eq_blockAlphaLow_of_le` collapses the sym
carrier to a LOW shape, but the prime indicator stays `blockPrimeInd (max y (pieceN k)) =
blockPrimeInd y` (since `pieceN k < y`), and no landed terminal prices that combination.  This
node closes it by applying the generic-`N` terminal `medium_survivor_price_sqrtD` DIRECTLY at
`N := y` (the fin7b/#73 adjudication: `2^k ≤ y` gives `M = pieceM k ≤ 2·y`, so the terminal's
`M ≤ 2·N` guard closes at `N := y` with NO `2^k` bridge; `d0_window_of_XM_band` applies verbatim
at the band floor `x^{1/3}/8 ≤ y`; the price is the Kerr form at `log y`).

New file; NO edits to any landed file; `All.lean` NOT wired.

## Enumerated spec of `medium_survivor_price_sqrtD` at `N := y` (mandate item 1)

The terminal (`SqrtDFold.lean:956`) is generic in `N`.  Instantiating `A := 13`, `C0 := 18`,
`B := 15`, `X := 2^{i+1}−1`, `M := pieceM k`, `N := y`, in the middle-`k` regime
(`pieceN k < y < pieceM k`, so `2^k ≤ y < 2^{k+1}`), its ~35 hypotheses classify as:

* `hM2N : pieceM k ≤ 2·y`     ← `middle_k_M_le_two_y` (Headline3, off `2^k ≤ y`).
* the `D0` family (`hD0N`, `hD0N'`, `hD0lo_main`, `herr_D0lo`, `hD0`, `hd_conj7`, `hd_xscale`,
  `hd_eq`, `hd_2D0`)          ← `d0_window_of_XM_band (N := y)` (ChenFinal2), verbatim at
                                 `x^{1/3}/8 ≤ y`.
* the SW couplings (`hcoupG`/`hcoup3`/`herr_book4`) ← the PriceOne suppliers
  (`Kbeta_min_coupling`/`Km_min_coupling`/`Kbeta'_min_coupling`) at `logN := log y` — GENERIC in
  `logN`, reused verbatim (`0 < log y` off `y ≥ 4`).
* the per-`e` rows (`herr_scale`/`herr_LEpos`/`herr_D0E`) ← `bridge_scale` (PriceOne), generic
  in `N`/`M`, the catch-#69 `e ≤ X` guard passed straight through.
* the analytic rows: `hMsqrt`/`hXsqrt`/`hDscale`/`herr_lev`/`herr_Mlev`/`hfloor` ←
  `band_price_rows_at_op` (ChenRows2) at the `y`-floor; `hDsq : D < (y+1)²` ← `hDsq_of_floor`
  (below, the `2^k`→`y` restatement of `band_hDsq_of_kfloor`); `habs` ← `band_habs_row` (the
  `2^k·M/L^13` residual fin7b threads), weakened to the `y·M/L^13` form via `2^k ≤ y`;
  `hFX`/`hX2` ← `band_F_le_X`/`band_two_le_X`; `hDx`/`hDXM` ← the `opD`/window scaffold.
* `hNM : (y:ℝ) ≤ pieceM k` ← `y < pieceM k`; `hM2 : 2 ≤ pieceM k` ← `two_le_pieceM`.

Residuals threaded to fin8 (fin7b's adjudication): row 12 (caller `QR·Dlev`, `hDbnd`) and row 15
(`habs`, in the `2^k·M` shape `band_habs_row` supplies).  Everything else is discharged here.

The consumer slot (mandate item 2, quoted): `PloW_sym_of_box_disc` (SwitchW2) — via
`sym_box_price_at_op` (PriceTwo) — demands, for the middle `k`, the `hpriceSym` T-difference

```
∑ m ∈ ((divisors Ps).filter (·<bound)).image (Q··),
    ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
        (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m/Q) a) m x
      - apDiscBilinCutoff (…) m (x/2+1)‖  ≤  PsymK k
```

whose `box_disc_three_way` reduction is the per-`i` two-`T` slot `middle_k_price` supplies
(reduced top `2^{i+1}−1`, `≤ 2·(Kerr price at log y)`).  The anti-#69 `example` at the end feeds
that slot into `sym_box_price_at_op` character-for-character.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## §0 — the `hDsq` engine at a general block floor (the `2^k`→`N` restatement)

`band_hDsq_of_kfloor` (ChenRows2 §2) is stated at `N = 2^k`; the middle-`k` box prices at
`N := y`, so `hDsq : D < (y+1)²` needs the SAME argument with `2^k` replaced by `y`.  Factored
here as a general-floor lemma (`x^{2/3}/64 = (x^{1/3}/8)² ≤ N² < (N+1)²`, `x^{1/6}` room). -/

/-- **`hDsq_of_floor` (the general-floor `hDsq`).**  A block floor `x^{1/3}/8 ≤ N` with `D ≤ √x`
and `x ≥ 10^{48}` gives `D < (N+1)²`.  The `N = 2^k` case is `band_hDsq_of_kfloor`; here `N := y`
for the middle-`k` terminal at `N := y`. -/
theorem hDsq_of_floor {x N D : ℕ}
    (hNfloor : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (N : ℝ))
    (hDx : (D : ℝ) ≤ Real.sqrt x) (hx : (10 : ℝ) ^ 48 ≤ (x : ℝ)) :
    D < (N + 1) * (N + 1) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx
  have hsqrt_eq : Real.sqrt x = (x : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  -- `√x = x^{1/2} ≤ x^{2/3}/64` for `x ≥ 10^{48}` (⟺ `64 ≤ x^{1/6}`)
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
  have hx13x13 : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) = (x : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add hxpos, show (1 : ℝ) / 3 + 1 / 3 = 2 / 3 by norm_num]
  have h8pos : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) / 8 := by positivity
  have hsq : ((x : ℝ) ^ ((1 : ℝ) / 3) / 8) * ((x : ℝ) ^ ((1 : ℝ) / 3) / 8)
      ≤ (N : ℝ) * (N : ℝ) := mul_self_le_mul_self h8pos hNfloor
  have heq64 : ((x : ℝ) ^ ((1 : ℝ) / 3) / 8) * ((x : ℝ) ^ ((1 : ℝ) / 3) / 8)
      = (x : ℝ) ^ ((2 : ℝ) / 3) / 64 := by rw [← hx13x13]; ring
  have hDR : (D : ℝ) ≤ (N : ℝ) * (N : ℝ) := by
    calc (D : ℝ) ≤ Real.sqrt x := hDx
      _ = (x : ℝ) ^ ((1 : ℝ) / 2) := hsqrt_eq
      _ ≤ (x : ℝ) ^ ((2 : ℝ) / 3) / 64 := hx12
      _ = ((x : ℝ) ^ ((1 : ℝ) / 3) / 8) * ((x : ℝ) ^ ((1 : ℝ) / 3) / 8) := heq64.symm
      _ ≤ (N : ℝ) * (N : ℝ) := hsq
  have hDnat : D ≤ N * N := by
    have h : ((D : ℕ) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  have hexp : (N + 1) * (N + 1) = N * N + 2 * N + 1 := by ring
  omega

/-! ## §1 — the single-`T` terminal at `N := y` (mandate item 1)

`medium_box_price_core` (PriceTwo §2) HARDCODES the `pieceN k → 2^k` indicator bridge
(`sum_norm_apDiscBilinCutoff_pieceN`) and prices at `N := 2^k`.  The middle-`k` box keeps the
indicator `blockPrimeInd y` (no bridge — `max y (pieceN k) = y` there), so it needs the terminal
applied DIRECTLY at `N := y`.  `middle_medium_box_price_at_y` is `medium_box_price_core` merged
with `medium_box_price_at_op_band` (the `d0_window_of_XM_band` feed) at `N := y`: the `2^k`
routing (`pieceM_le_two_pow`/`two_pow_le_pieceM`/`sum_norm_apDiscBilinCutoff_pieceN`) is replaced
by the `y` routing (`middle_k_M_le_two_y` / `y ≤ pieceM k` / NO bridge).  The `habs` row enters in
the `2^k·M` shape `band_habs_row` supplies and is weakened to `y·M` via `2^k ≤ y`. -/

/-- **`middle_medium_box_price_at_y` (single-`T` core).**  `medium_box_price_at_op_band` at
`N := y` and indicator `blockPrimeInd y`: the generic terminal `medium_survivor_price_sqrtD`
(`A=13`, `C0=18`, `B=15`) applied to a generic `0/1` carrier `α`, with the band `D0` window at
`N := y` (`d0_window_of_XM_band`), the couplings at `logN := log y`, and the `habs` row taken in
the `2^k·M/L^13` shape (weakened to `y·M/L^13` via `2^k ≤ y`).  The price is the Kerr form at
`log y`. -/
theorem middle_medium_box_price_at_y :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (x : ℕ) (Lb : ℝ) (F k y : ℕ) (α : ℕ → ℂ) (X T D : ℕ)
        (Dset : Finset ℕ) (r : ℕ → ℕ),
        2 ≤ k →
        pieceN k < y →
        y < pieceM k →
        Real.exp (10 ^ 10) ≤ (x : ℝ) →
        (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (y : ℝ) →
        x / 2 + 1 < X * pieceM k →
        X * pieceM k ≤ 4 * x →
        (∀ m, ‖α m‖ ≤ 1) →
        (∀ d ∈ Dset, 1 ≤ d) →
        (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (∀ d ∈ Dset, d ≤ D) →
        N₀ ≤ y →
        2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) →
        2 ≤ X →
        1 ≤ D →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))
            / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (15 : ℝ)) →
        D < (y + 1) * (y + 1) →
        (4 * (1 + Real.log D) * (D : ℝ)
            ≤ ((2 ^ k : ℕ) : ℝ) * (pieceM k : ℝ)
                / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (X : ℝ)) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 3) ≤ Real.sqrt (pieceM k : ℝ)) →
        ((D : ℝ) * (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))) →
        ((Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ ((13 : ℝ) + 5) ≤ Real.sqrt (pieceM k : ℝ)) →
        F ≤ X →
        ((D : ℝ) ≤ Real.sqrt (x : ℝ)) →
        (Real.log ((X : ℝ) * (pieceM k : ℝ)) ≤ Lb) →
        (((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6) * Lb ^ ((13 : ℝ) + 5)
            ≤ Real.sqrt (F : ℝ)) →
        ((D : ℝ) ≤ (X : ℝ) * (pieceM k : ℝ)) →
        ∑ d ∈ Dset,
            ‖apDiscBilinCutoff α (blockPrimeInd y) X (pieceM k) (r d) d T‖
          ≤ (Kbeta_min K (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                  (Real.log (y : ℝ)) 13 18
              + (6 * (Km_min K (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                        (Real.log (y : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                  + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                      * Kbeta'_min K (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                          (Real.log (y : ℝ)) 13 18 + 15360 + 1)))
            * ((X : ℝ) * (pieceM k : ℝ)) / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ) := by
  obtain ⟨K, N₀, hK0, hbody⟩ := medium_survivor_price_sqrtD (A := 13) (C0 := 18) (by norm_num)
    (by norm_num)
  refine ⟨K, N₀, hK0, fun x Lb F k y α X T D Dset r hk hmidlo hmidhi hx hy hXMlo hXMhi hα hd1
    hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX
    hDx hLbb hfloor hDXM => ?_⟩
  set M : ℕ := pieceM k with hMdef
  set L : ℝ := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  set logY : ℝ := Real.log (y : ℝ) with hlogYdef
  have hk1 : 1 ≤ k := by omega
  have hLnn : (0 : ℝ) ≤ L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hM2 : 2 ≤ M := by rw [hMdef]; exact two_le_pieceM hk1
  -- middle-`k` geometry: `2^k ≤ y`, so `y ≥ 4 > 1` and `0 < log y`.
  have h2ky : 2 ^ k ≤ y := two_pow_le_of_pieceN_lt hmidlo
  have h4k : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hy1 : 1 < y := by omega
  have hy1R : (1 : ℝ) < (y : ℝ) := by exact_mod_cast hy1
  have hlogYpos : (0 : ℝ) < logY := by rw [hlogYdef]; exact Real.log_pos hy1R
  have h2kyR : ((2 ^ k : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast h2ky
  -- the `M ≤ 2N`/`N ≤ M` guards at `N := y`.
  have hM2N : M ≤ 2 * y := by rw [hMdef]; exact middle_k_M_le_two_y hmidlo
  have hNM : (y : ℝ) ≤ (M : ℝ) := by rw [hMdef]; exact_mod_cast le_of_lt hmidhi
  -- the band `D0` window at `N := y`.
  obtain ⟨D0, k0, hd_eq, hd_2D0, hd_main, hd_D0lo, hd_hD0, hd_hD0N', hd_conj7, hd_xscale,
    hd_hD0N⟩ := d0_window_of_XM_band (x := x) (N := y) (M := M) (X := X) hx hy hXMlo hXMhi
  -- SW couplings (minimal choices) at `logN := log y`.
  have hcoupG : K * L ^ ((13 : ℝ) + 18)
      ≤ Kbeta_min K L logY 13 18 * logY ^ ((13 : ℝ) + 2 * 18) := Kbeta_min_coupling hlogYpos
  have hcoup3 : K * L ^ ((13 : ℝ) + 1 + 2 * 18)
      ≤ Km_min K L logY 13 18 * logY ^ ((13 : ℝ) + 2 * 18) := Km_min_coupling hlogYpos
  have herr_book4 : ∀ e, 2 ≤ e → e ≤ D →
      K * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
        ≤ Kbeta'_min K L logY 13 18 * logY ^ ((13 : ℝ) + 1 + 2 * 18) :=
    fun e _ _ => Kbeta'_min_coupling hK0.le hlogYpos (log_efold_nonneg X M e)
      (log_efold_le X M e) (by norm_num)
  -- guarded per-`e` rows (catch #69).
  have herr_scale : ∀ e, 2 ≤ e → e ≤ D → e ≤ X →
      L ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) :=
    fun e he2 heD heX => bridge_scale hM2 he2 heX heD hDscale (by norm_num) hL2
  have herr_LEpos : ∀ e, 2 ≤ e → e ≤ D → e ≤ X →
      0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) := by
    intro e he2 heD heX
    have h := herr_scale e he2 heD heX
    linarith [hL2]
  have herr_D0E : ∀ e, 2 ≤ e → e ≤ D → e ≤ X →
      (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (18 : ℝ) :=
    fun e he2 heD heX => hd_conj7 _ (herr_scale e he2 heD heX)
  -- `D0`-window rows re-shaped to the terminal's `A = 13` exponents.
  have hD0D : D0 ≤ D := Nat.cast_le.mp (le_trans hd_xscale hDge_x)
  have hD0lo_main : L ^ ((13 : ℝ) + 2) ≤ 2 * (2 : ℝ) ^ k0 := by
    rw [show ((13 : ℝ) + 2) = 15 by norm_num]; exact hd_main
  have herr_D0lo : L ^ ((13 : ℝ) + 4) ≤ (D0 : ℝ) := by
    rw [show ((13 : ℝ) + 4) = 17 by norm_num]; exact hd_D0lo
  -- nonnegativity of the minimal SW constants.
  have hKβnn : 0 ≤ Kbeta_min K L logY 13 18 := Kbeta_min_nonneg hK0.le hLnn hlogYpos.le
  have hKmnn : 0 ≤ Km_min K L logY 13 18 := Km_min_nonneg hK0.le hLnn hlogYpos.le
  have hKβ'nn : 0 ≤ Kbeta'_min K L logY 13 18 := Kbeta'_min_nonneg hK0.le hLnn hlogYpos.le
  -- `habs` at `N := y`: weaken the `2^k·M` shape via `2^k ≤ y`.
  have hL13nn : (0 : ℝ) ≤ L ^ (13 : ℝ) := Real.rpow_nonneg hLnn _
  have habs_y : 4 * (1 + Real.log D) * (D : ℝ) ≤ (y : ℝ) * (M : ℝ) / L ^ (13 : ℝ) := by
    refine le_trans habs ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2kyR (Nat.cast_nonneg _)) (inv_nonneg.mpr hL13nn)
  -- apply the terminal at `N := y` (NO `pieceN → 2^k` bridge; sum is already `blockPrimeInd y`).
  exact hbody (x : ℝ) Lb F α X y M T D0 D k0 (Nat.log 2 D) Dset r
    (Kbeta_min K L logY 13 18) (Km_min K L logY 13 18) (Kbeta'_min K L logY 13 18) 15
    hα hKβnn hKmnn hKβ'nn hN₀ hM2N hd_hD0N hd1 hcop2 hL1 hd_hD0 hd_hD0N' hNM hD1 hDsetD hDsq
    habs_y hX2 hM2 (by norm_num) (by norm_num) hd_eq hd_2D0 hD0D rfl hDscale hD0lo_main hXsqrt
    hMsqrt herr_lev herr_D0lo herr_Mlev hFX hDx hLbb hfloor herr_LEpos herr_D0E hDXM herr_scale
    hcoupG hcoup3 herr_book4

/-! ## §2 — `middle_k_price` : the two-`T` composition at the middle-`k` sym carrier
(mandate item 2)

The analogue of `sym_rows_at_op` for the single middle `k` (`pieceN k < y < pieceM k`).  The
sym carrier `blockAlphaSym z y ε₀ j (pieceN k) (pieceM k)` collapses to a LOW shape
(`blockAlphaSym_eq_blockAlphaLow_of_le`, `pieceN k ≤ y`), but the indicator stays
`blockPrimeInd (max y (pieceN k)) = blockPrimeInd y` (since `pieceN k < y`).  We keep the sym
carrier (its `0/1` norm bound is `norm_sym_leg_le_one`, so no rewrite is needed — the carrier
stays as the consumer's slot demands) and price at `N := y` via `middle_medium_box_price_at_y`,
applied TWICE (`T = x`, `T = x/2+1`), for the per-`i` two-`T` slot `≤ 2·(Kerr price at log y)`.

The analytic rows are discharged in-node at the `y`-floor: `band_price_rows_at_op`
(`hDscale`/`hXsqrt`/`hMsqrt`/`herr_lev`/`herr_Mlev`/`hfloor`), `hDsq_of_floor` (`hDsq` at
`x^{1/3}/8 ≤ y`), `band_F_le_X`/`band_two_le_X` (`hFX`/`hX2`), the `√x`/window scaffold
(`hDx`/`hDXM`), and `xm_log_bounds` (`hL2`/`hLbb`).  Residuals threaded from fin8: `hDbnd` (row
12, `Q·QR·Dlev ≤ D`) and `habs` (row 15, `band_habs_row`'s `2^k·M/L^13` shape). -/

open Classical in
/-- **`middle_k_price` (mandate item 2, the terminal at `N := y`).**  For the single middle `k`
(`pieceN k < y < pieceM k`), the sym carrier's per-`i` two-`T` sum (reduced top `2^{i+1}−1`,
indicator `blockPrimeInd (max y (pieceN k)) = blockPrimeInd y`) is `≤ 2·(Kerr price at log y)`.
This is the `hprice` slot `sym_box_price_at_op` (PriceTwo) consumes at the middle `k`, whose
`box_disc_three_way` composition is the `PsymK`/`hpriceSym` T-difference `PloW_sym_of_box_disc`
demands.  Structure: `sym_rows_at_op` at the `y`-floor, then `middle_medium_box_price_at_y`
twice.  Residuals: `hDbnd` (caller `QR`) and `habs` (`band_habs_row`, `2^k·M` shape). -/
theorem middle_k_price (z y Ps Q a : ℕ) (hQ1 : 1 ≤ Q) (hPspos : 0 < Ps)
    (hQPs : Nat.Coprime Q Ps) (hQa2 : Nat.Coprime Q (a + 2))
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    ∃ (Kc : ℝ) (N₀ x₁ : ℕ), 0 < Kc ∧
      ∀ (x : ℕ) (ε₀ : ℝ) (j k i : ℕ) (Krange : ℕ) (QR : ℝ) (Dlev D : ℕ),
        x₁ ≤ x →
        2 ≤ k →
        pieceN k < y →
        y < pieceM k →
        (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (y : ℝ) →
        2 ≤ z * y →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((z * y : ℕ) : ℝ) →
        i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
            (z * max y (pieceN k)) Krange →
        N₀ ≤ y →
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
                    (Real.log (y : ℝ)) 13 18
                + (6 * (Km_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                          (Real.log (y : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                        * Kbeta'_min Kc (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)))
                            (Real.log (y : ℝ)) 13 18 + 15360 + 1)))
              * (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))
              / (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨Kc, N₀, hK0, hbody⟩ := middle_medium_box_price_at_y
  obtain ⟨x₂, hx₂48, hrows⟩ := band_price_rows_at_op
  refine ⟨Kc, N₀, max x₂ (⌈Real.exp (10 ^ 10)⌉₊ + 1), hK0,
    fun x ε₀ j k i Krange QR Dlev D hx hk hmidlo hmidhi hy hzy2 hXlo hFlo hi hN₀ hD1 hDge_x hDbnd
      hDub habs => ?_⟩
  -- collapse `max y (pieceN k) = y` (in the goal and the boundary membership).
  rw [max_eq_left (le_of_lt hmidlo)] at hi ⊢
  -- scale facts.
  have hx2x : x₂ ≤ x := le_trans (le_max_left _ _) hx
  have htower : Real.exp (10 ^ 10) ≤ (x : ℝ) := by
    calc Real.exp (10 ^ 10) ≤ (⌈Real.exp (10 ^ 10)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (x : ℝ) := by exact_mod_cast (by omega : ⌈Real.exp (10 ^ 10)⌉₊ ≤ x)
  have hx48 : 10 ^ 48 ≤ x := le_trans hx₂48 hx2x
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hx2 : 2 ≤ x := le_trans (by norm_num) hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hxR
  set X : ℕ := 2 ^ (i + 1) - 1 with hXdef
  -- the raw `X·M` window from the `y`-floor boundary clauses (cutoff + corner).
  have hclause := hi
  rw [dyadicBoundary, Finset.mem_filter] at hclause
  obtain ⟨-, hcorner, -, hcut⟩ := hclause
  have hXMlo : x / 2 + 1 < X * pieceM k := by rw [hXdef]; exact hcut
  have hXMhi : X * pieceM k ≤ 4 * x := by
    rw [hXdef]
    have hMle : pieceM k ≤ 2 * (y + 1) := by
      have h1 := pieceM_le_two_pow k
      have h2 := two_pow_le_of_pieceN_lt hmidlo
      omega
    calc (2 ^ (i + 1) - 1) * pieceM k ≤ 2 ^ (i + 1) * (2 * (y + 1)) :=
          Nat.mul_le_mul (Nat.sub_le _ _) hMle
      _ = 4 * (2 ^ i * (y + 1)) := by rw [pow_succ]; ring
      _ ≤ 4 * x := Nat.mul_le_mul (le_refl 4) hcorner
  -- band-specific structural rows.
  have hFX : (z * y : ℕ) ≤ X := band_F_le_X hi hXdef
  have hX2 : 2 ≤ X := band_two_le_X hi hXdef hzy2
  have hNM : (y : ℝ) ≤ (pieceM k : ℝ) := by exact_mod_cast le_of_lt hmidhi
  -- the log window + `hL2`.
  obtain ⟨hLlo, hLub⟩ := xm_log_bounds hx2 hXMlo hXMhi
  have hL96 : (96 : ℝ) ≤ Real.log x := opf_log_ge_96 x hxR
  have hL2 : 2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) := by linarith [hLlo]
  have hLbb : Real.log ((X : ℝ) * (pieceM k : ℝ)) ≤ Real.log x + 3 := by linarith [hLub]
  have hLb0 : (0 : ℝ) ≤ Real.log x + 3 := by linarith
  -- `M`-floor and `D ≤ √x`.
  have hMlo : (x : ℝ) ^ ((1 : ℝ) / 3) / 8 ≤ (pieceM k : ℝ) := le_trans hy hNM
  have hDx : (D : ℝ) ≤ Real.sqrt x := by
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [hxpos]) (by norm_num)
    rw [Real.sqrt_eq_rpow]; linarith [hDub]
  have hDsq : D < (y + 1) * (y + 1) := hDsq_of_floor hy hDx hxR
  -- the fresh polylog/sqrt/`D`-scale rows (`band_price_rows_at_op`).
  obtain ⟨hDscale, hXsqrt, hMsqrt, herr_lev, herr_Mlev, hfloor⟩ :=
    hrows x hx2x X (pieceM k) D (z * y) (Real.log x + 3) hXMlo hXMhi hXlo hMlo hFlo hDub hLb0
      le_rfl
  -- `D ≤ X·M`.
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
  -- the `Q`-image family rows.
  have hα := norm_sym_leg_le_one z y ε₀ j (pieceN k) (pieceM k) i
  have hd1 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), (1 : ℕ) ≤ m := fun m hm => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hm
  have hcop2 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), Nat.Coprime (crtClassW Q (m / Q) a) m :=
    fun m hm => crtClassW_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQa2 hPodd hPspos hm
  have hDsetD : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), m ≤ D := fun m hm => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hm
  -- the two-`T` composition (`T = x` and `T = x/2+1`) at `N := y`.
  rw [two_mul]
  exact add_le_add
    (hbody x (Real.log x + 3) (z * y) k y
        (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k)) (2 ^ i) (2 ^ (i + 1)))
        X x D _ (fun m => crtClassW Q (m / Q) a) hk hmidlo hmidhi htower hy hXMlo hXMhi hα hd1
        hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev
        hFX hDx hLbb hfloor hDXM)
    (hbody x (Real.log x + 3) (z * y) k y
        (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k)) (2 ^ i) (2 ^ (i + 1)))
        X (x / 2 + 1) D _ (fun m => crtClassW Q (m / Q) a) hk hmidlo hmidhi htower hy hXMlo hXMhi
        hα hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev
        herr_Mlev hFX hDx hLbb hfloor hDXM)

/-! ## §3 — the anti-#69 witness : the middle-`k` price feeds the consumer slot
(mandate item 3)

The per-`i` two-`T` slot `middle_k_price` supplies is EXACTLY the `hprice` input of
`sym_box_price_at_op` (PriceTwo); feeding it yields the `hpriceSym`/`PsymK` T-difference bound
that `PloW_sym_of_box_disc` (SwitchW2) consumes at the middle `k` — no shape mismatch (anti-#69).
At the operating point fin8 instantiates `Price i := 2·(Kerr price at log y)`, the exact RHS of
`middle_k_price`. -/

open Classical in
/-- Anti-#69 (the middle-`k` price → consumer slot match): the per-`i` `middle_k_price`
conclusions are character-for-character the `hprice` slot of `sym_box_price_at_op`.  Feeding them
yields the sym-band T-difference bound `PloW_sym_of_box_disc` consumes for the middle `k`. -/
example {x z y : ℕ} {ε₀ : ℝ} {j k X Q a : ℕ} (Ps : ℕ) (bound : ℝ) (K : ℕ) (Price : ℕ → ℝ)
    (hxlo : x / 2 + 1 ≤ x) (hK : Nat.log 2 X ≤ K)
    (hiX : ∀ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
        (z * max y (pieceN k)) K, 2 ^ (i + 1) ≤ X + 1)
    -- the per-`i` two-`T` slot `middle_k_price` produces (`Price i := 2·(Kerr price at log y)`):
    (hprice : ∀ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
        (z * max y (pieceN k)) K,
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd (max y (pieceN k))) (2 ^ (i + 1) - 1)
                (pieceM k) (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                  (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd (max y (pieceN k))) (2 ^ (i + 1) - 1)
                  (pieceM k) (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ Price i) :
    -- the `hpriceSym` slot of `PloW_sym_of_box_disc` (the sym-band T-difference at the full top):
    (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
            (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x
          - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
            (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
      ≤ ∑ i ∈ dyadicBoundary (max y (pieceN k)) (pieceM k) (x / 2 + 1) x
          (z * max y (pieceN k)) K, Price i :=
  sym_box_price_at_op Ps bound K Price hxlo hK hiX hprice

end Salt.Chen
