/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.PriceTwo
import Salt.Chen.HeadlineW2

/-!
# PRICE-3 — the analytic rows + the aggregate close (node PRICE-3)

Design: `docs/blueprints/flags.md`, the `2026-07-14 PRICE-GATE`/`PRICE-1`/`PRICE-2` entries and
the `GLU-2W-fin` scoping finding (Finding 4/B: the honest aggregate closes with tower room).
This is the PRICE wave's last construction node — it discharges the box lemmas'
named-analytic-hypothesis list at the operating values, supplies the carrier bridges + Dset
bookkeeping (PRICE-2's remainder list), and drives toward `hBVblocksW_at_op`.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* (deliverable 2, the PRICE-2 remainder list) **the carrier bridges + Dset bookkeeping** —
  `max y (pieceN k) = pieceN k` on the strip fact `y ≤ pieceN k`; the `≤ 1`-norm transports
  (`norm_restrictAlpha_le_one ∘ norm_blockAlpha*_le_one` for the box / sym / low carriers);
  the image-family facts (`1 ≤ m`, `crtClassW` coprimality via `Q ⊥ (m/Q)`, `m ≤ D`) over the
  operating `Q`-shifted divisor image `((divisors Ps).filter (·<bound)).image (Q··)`.
* (deliverable 4, the summit opener) **`maxBlock_eq_zero_of_eps_self`** — with `ε₀ := x` the
  block partition collapses to the single block `j = 0` (Finding 4): `blockIdx z x x = 0` since
  `log(x/z) < log(1+x)`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## 1. The carrier bridges (deliverable 2)

The consumer `hBVblocksW_discharge'` (PDiag) carries three prime-side carriers, all fed to the
box-price terminal `medium_box_price_at_op(_lo)` through its `hα : ∀ m, ‖α m‖ ≤ 1` slot:

* the box leg `restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0 c) (2^i) (2^{i+1})`;
* the sym leg `restrictAlpha (blockAlphaSym z y ε₀ j N M) (2^i) (2^{i+1})`
  (via `sym_box_price_at_op`'s reduced-top `hprice`);
* the low leg `restrictAlpha (restrictAlpha (blockAlphaLow z y ε₀ j N) c (x+1)) (2^i) (2^{i+1})`.

Each is `≤ 1` by composing `norm_restrictAlpha_le_one` with the landed `‖blockAlpha*‖ ≤ 1`. -/

/-- **The sym carrier bridge (`max` collapse).**  On the strip fact `y ≤ pieceN k`, the sym band's
prime indicator `blockPrimeInd (max y (pieceN k))` collapses to `blockPrimeInd (pieceN k)` — the box
lemma's indicator.  Pure `max_eq_right`. -/
theorem max_y_pieceN_eq {y k : ℕ} (h : y ≤ pieceN k) : max y (pieceN k) = pieceN k :=
  max_eq_right h

/-- **The box-leg norm transport.**  The doubly-restricted block carrier is `0/1`-bounded — the
`hα` slot of `medium_box_price_at_op` for the `hprice`/`hBVblocksW_discharge'` box leg. -/
theorem norm_box_leg_le_one (z y : ℕ) (ε₀ : ℝ) (j c i : ℕ) :
    ∀ m, ‖restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0 c) (2 ^ i) (2 ^ (i + 1)) m‖ ≤ 1 :=
  fun m => norm_restrictAlpha_le_one
    (fun m' => norm_restrictAlpha_le_one (fun m'' => norm_blockAlpha_le_one z y ε₀ j m'') 0 c m')
    (2 ^ i) (2 ^ (i + 1)) m

/-- **The sym-leg norm transport.**  The restricted sym carrier is `0/1`-bounded — the `hα` slot
of `medium_box_price_at_op` inside `sym_box_price_at_op`'s per-box `hprice`. -/
theorem norm_sym_leg_le_one (z y : ℕ) (ε₀ : ℝ) (j N M i : ℕ) :
    ∀ m, ‖restrictAlpha (blockAlphaSym z y ε₀ j N M) (2 ^ i) (2 ^ (i + 1)) m‖ ≤ 1 :=
  fun m => norm_restrictAlpha_le_one
    (fun m' => norm_blockAlphaSym_le_one z y ε₀ j N M m') (2 ^ i) (2 ^ (i + 1)) m

/-- **The low-leg norm transport.**  The doubly-restricted low carrier is `0/1`-bounded — the `hα`
slot of `medium_box_price_at_op` inside `low_box_price_at_op`'s per-box `hprice`. -/
theorem norm_low_leg_le_one (z y : ℕ) (ε₀ : ℝ) (j N c d i : ℕ) :
    ∀ m, ‖restrictAlpha (restrictAlpha (blockAlphaLow z y ε₀ j N) c d) (2 ^ i) (2 ^ (i + 1)) m‖
      ≤ 1 :=
  fun m => norm_restrictAlpha_le_one
    (fun m' => norm_restrictAlpha_le_one
      (fun m'' => norm_blockAlphaLow_le_one z y ε₀ j N m'') c d m')
    (2 ^ i) (2 ^ (i + 1)) m

/-! ## 2. The Dset image-family bookkeeping (deliverable 2)

The box lemmas price over `Dset := ((divisors Ps).filter (·<bound)).image (fun d => Q·d)` with the
residue function `r := fun m => crtClassW Q (m/Q) a`.  The three per-`Dset` rows
(`hd1 : 1 ≤ m`, `hcop2 : Coprime (r m) m`, `hDsetD : m ≤ D`) of `medium_box_price_at_op` are the
following, over the operating `Q`/`Ps`/`bound`/`D`. -/

/-- **`hd1` (image family): `1 ≤ m`.**  Each `m = Q·d` with `Q ≥ 1` and `d ∣ Ps` positive. -/
theorem one_le_of_mem_QImage {Q Ps : ℕ} (bound : ℝ) (hQ1 : 1 ≤ Q)
    {m : ℕ}
    (hm : m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d)) :
    1 ≤ m := by
  rw [Finset.mem_image] at hm
  obtain ⟨d, hd, rfl⟩ := hm
  rw [Finset.mem_filter] at hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd.1
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-- **`hcop2` (image family): `Coprime (crtClassW Q (m/Q) a) m`.**  At `m = Q·d`, `m/Q = d`
(`Q ≥ 1`), and `crtClassW_coprime` closes from `Q ⊥ d` (off `Q ⊥ Ps`), `Q ⊥ (a+2)`, and `d` odd
(off `Ps` `3`-rough). -/
theorem crtClassW_coprime_of_mem {Q Ps a : ℕ} (bound : ℝ) (hQ1 : 1 ≤ Q)
    (hQPs : Nat.Coprime Q Ps) (hQa2 : Nat.Coprime Q (a + 2))
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hPspos : 0 < Ps)
    {m : ℕ}
    (hm : m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d)) :
    Nat.Coprime (crtClassW Q (m / Q) a) m := by
  rw [Finset.mem_image] at hm
  obtain ⟨d, hd, rfl⟩ := hm
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hdvd, _⟩, _⟩ := hd
  have hQd_div : Q * d / Q = d := Nat.mul_div_cancel_left d (by omega)
  rw [hQd_div]
  have hQd : Nat.Coprime Q d := Nat.Coprime.coprime_dvd_right hdvd hQPs
  have h2d : Nat.Coprime 2 d := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h2
    have h2Ps : 2 ∣ Ps := h2.trans hdvd
    have hmem : 2 ∈ Ps.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2Ps, hPspos.ne'⟩
    have := hPodd 2 hmem
    omega
  exact crtClassW_coprime hQd hQa2 h2d

/-- **`hDsetD` (image family): `m ≤ D`.**  At `m = Q·d` with `(d:ℝ) < bound` and `Q·bound ≤ D`. -/
theorem le_D_of_mem_QImage {Q Ps D : ℕ} (bound : ℝ) (hQ1 : 1 ≤ Q)
    (hbnd : (Q : ℝ) * bound ≤ (D : ℝ))
    {m : ℕ}
    (hm : m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d)) :
    m ≤ D := by
  rw [Finset.mem_image] at hm
  obtain ⟨d, hd, rfl⟩ := hm
  rw [Finset.mem_filter] at hd
  have hdb : (d : ℝ) < bound := hd.2
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
  have hlt : ((Q * d : ℕ) : ℝ) < (D : ℝ) := by
    calc ((Q * d : ℕ) : ℝ) = (Q : ℝ) * (d : ℝ) := by push_cast; ring
      _ < (Q : ℝ) * bound := by exact mul_lt_mul_of_pos_left hdb hQR
      _ ≤ (D : ℝ) := hbnd
  exact_mod_cast le_of_lt hlt

/-! ## 3. The single-block collapse `maxBlock = 0` (deliverable 4, the summit opener)

Finding 4/B: choosing `ε₀ := x` makes the geometric block index `blockIdx z ε₀ p = ⌊log(p/z)/
log(1+ε₀)⌋` collapse — at `ε₀ = x` the denominator `log(1+x)` exceeds the numerator `log(x/z) ≤
log x` for every prime up to `x`, so the whole `tripleSet` lands in block `j = 0` and the block
sum `∑ j ∈ range (maxBlock+1)` is a SINGLE term.  This is what lets the aggregate close at a fixed
per-`x` budget rather than paying a `maxBlock ~ log x / ε₀` factor. -/

/-- **`maxBlock_eq_zero_of_eps_self` (deliverable 4).**  With `ε₀ := x`, the top block index is `0`:
`log(x/z) ≤ log x < log(1+x)`, so `⌊log(x/z)/log(1+x)⌋₊ = 0`.  The single-block collapse. -/
theorem maxBlock_eq_zero_of_eps_self {x z : ℕ} (hz : 1 ≤ z) (hx : 1 ≤ x) :
    maxBlock x z (x : ℝ) = 0 := by
  unfold maxBlock blockIdx
  rw [Nat.floor_eq_zero]
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hden_pos : (0 : ℝ) < Real.log (1 + (x : ℝ)) :=
    Real.log_pos (by linarith)
  rw [div_lt_one hden_pos]
  have hxz_pos : (0 : ℝ) < (x : ℝ) / (z : ℝ) := div_pos hxpos (by linarith)
  have hxz_le : (x : ℝ) / (z : ℝ) ≤ (x : ℝ) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (z : ℝ))]
    nlinarith [hxR, hzR]
  calc Real.log ((x : ℝ) / (z : ℝ)) ≤ Real.log (x : ℝ) := Real.log_le_log hxz_pos hxz_le
    _ < Real.log (1 + (x : ℝ)) := Real.log_lt_log hxpos (by linarith)

/-! ## 4. The boundary reconciliation (deliverable 3 wiring; the pieceN ↔ 2^k seam, RESOLVED)

**The seam and its catch-#71 resolution.**  The consumer `hBVblocksW_discharge'` prices the box
leg over `dyadicBoundary (pieceN k) (pieceM k) (x/2+1) x (z·y) K`.  Originally
`medium_box_price_at_op` demanded the boundary at `N = 2^k` (Finding C: `pieceM k = 2·pieceN k+1`
so the terminal's `M ≤ 2N` needs `N = 2^k`), and since `pieceN k + 1 = 2^k`, only the corner
clause `2^i·(N+1) ≤ T₂` distinguishes the two — the `2^k`-corner `2^i·(2^k+1) ≤ x` is STRICTLY
stronger than the pieceN-corner `2^i·2^k ≤ x`, so `dyadicBoundary (2^k) ⊆ dyadicBoundary (pieceN k)`
(`boundary_2pow_subset_pieceN`), the WRONG way for a direct discharge.  The `≤ 1` "edge" box per
piece `i ∈ dyadicBoundary (pieceN k) \ dyadicBoundary (2^k)` (window `2^i ∈ (x/(2^k+1), x/2^k]`,
ratio `1 + 2^{-k} < 2`) was catch #71: for `2^k > x^{7/16}` its carrier is live yet it resisted
both the vanish and the `2^k`-boundary price routes.

**Catch #71, ratified option (a) — the corner relaxation.**  `medium_box_price_at_op(_lo)`,
`medium_box_price_core`, and all three `*_hprice_at_2pow` now take the pieceN-boundary membership
directly (weak corner `2^i·2^k ≤ x`).  The proofs rebuild the `D0`-window from the raw scale facts
`x/2+1 < X·M ≤ 4x` (`d0_window_of_XM`/`d0_window_of_XM_lo`, PriceOne §4b / PriceTwo §1b) — which
the WEAK corner supplies IDENTICALLY (`X·M ≤ 2^{i+1}·(2·2^k) = 4·2^i·2^k ≤ 4x`, NO degradation:
the `4x` bound is unchanged, `d0_window_nonempty` never used the `+1` slack).  So
`box_hprice_at_2pow` now prices EVERY box of the FULL pieceN-boundary, edge box included.  The
trichotomy (vanish / `2^k`-priced / edge) COLLAPSES to a **dichotomy** (vanish / priced) over the
pieceN-boundary: the former edge box is now on the "priced" side (or vanishes).
`boundary_2pow_subset_pieceN` survives as a historical fact (unused by the discharge). -/

/-- **`boundary_2pow_subset_pieceN` (deliverable 3 wiring).**  The `2^k`-boundary (what
`medium_box_price_at_op` prices) is contained in the `pieceN k`-boundary (what the consumer
`hprice` ranges over): the only `N`-dependent clause `2^i·(N+1) ≤ T₂` weakens from `N+1 = 2^k+1`
to `N+1 = 2^k`. -/
theorem boundary_2pow_subset_pieceN (k M T₁ T₂ F K : ℕ) :
    dyadicBoundary (2 ^ k) M T₁ T₂ F K ⊆ dyadicBoundary (pieceN k) M T₁ T₂ F K := by
  intro i hi
  rw [dyadicBoundary, Finset.mem_filter] at hi ⊢
  obtain ⟨hr, hc1, hc2, hc3⟩ := hi
  refine ⟨hr, ?_, hc2, hc3⟩
  have hpk : pieceN k + 1 = 2 ^ k := by
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    unfold pieceN; omega
  rw [hpk]
  exact le_trans (Nat.mul_le_mul_left _ (by omega : (2 : ℕ) ^ k ≤ 2 ^ k + 1)) hc1

/-! ## 5. The per-box price over the pieceN-boundary (deliverable 3, the box leg)

`box_hprice_at_2pow` composes the carrier bridge (`norm_box_leg_le_one`), the Dset bookkeeping
(`one_le_of_mem_QImage`/`crtClassW_coprime_of_mem`/`le_D_of_mem_QImage`), and TWO applications of
PriceOne's `medium_box_price_at_op` (at `T = x` and `T = x/2+1`, same `T`-independent bound) into
the consumer's box `hprice` slot: the box leg's HONEST two-`T` sum over the `Q`-shifted image
family is `≤ 2·(the box price)`.  The `Price j k i := 2·(Kerr bound)`, feeding the `hprice` slot of
`hBVblocksW_discharge'` at every box of the pieceN-boundary (catch #71: the corner-relaxed
terminal now prices the full pieceN-boundary, edge box included).  Everything except the 27 named
analytic rows (GlueFinal/`opf_*`-shaped, at `X = 2^{i+1}−1`, `M = pieceM k`, `N = 2^k`) is
discharged internally.  The `Q`/`Ps`/`a` coprimality side conditions are the operating
`opf_QPs`/`opf_Qa2`/`opf_Psodd`. -/

/-- **`box_hprice_at_2pow` (deliverable 3, the box leg).**  Over the pieceN-boundary (catch #71
corner relaxation), the box-leg two-`T` `hprice` sum is `≤ 2·(the Kerr box price)` — PriceOne's
`medium_box_price_at_op` applied twice, with the carrier `≤ 1`-norm and the `Q`-image Dset rows
discharged internally.  The surviving inputs are the 27 named analytic rows (the operating-point
facts PRICE-3's row table supplies) and the `Q·bound ≤ D` conductor row.  Directly slots the
`Price j k i := 2·Kerr` value into `hBVblocksW_discharge'`'s box `hprice` for every pieceN-boundary
box. -/
theorem box_hprice_at_2pow (z y Ps Q a : ℕ) (hQ1 : 1 ≤ Q) (hPspos : 0 < Ps)
    (hQPs : Nat.Coprime Q Ps) (hQa2 : Nat.Coprime Q (a + 2))
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x : ℕ) (ε₀ : ℝ) (j k i : ℕ) (Lb : ℝ) (F Krange X : ℕ) (QR : ℝ) (Dlev D : ℕ),
        2 ≤ k →
        Real.exp (10 ^ 9) ≤ (x : ℝ) →
        i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange →
        X = 2 ^ (i + 1) - 1 →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((2 ^ k : ℕ) : ℝ) →
        N₀ ≤ 2 ^ k →
        2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) →
        2 ≤ X →
        1 ≤ D →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))
            / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (15 : ℝ)) →
        D < (2 ^ k + 1) * (2 ^ k + 1) →
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
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                  (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                    (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ 2 * ((Kbeta_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                    (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18
                + (6 * (Km_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                          (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                        * Kbeta'_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                            (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 15360 + 1)))
              * ((X : ℝ) * (pieceM k : ℝ))
              / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨Kc, N₀, hK0, hbody⟩ := medium_box_price_at_op
  refine ⟨Kc, N₀, hK0, fun x ε₀ j k i Lb F Krange X QR Dlev D hk hx hi hXsub hNfloor hN₀ hL2 hX2
    hD1 hDge_x hDbnd hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor
    hDXM => ?_⟩
  have hα := norm_box_leg_le_one z y ε₀ j (min (z * pieceN k + 1) (x + 1)) i
  have hd1 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), (1 : ℕ) ≤ m := fun m hm => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hm
  have hcop2 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), Nat.Coprime (crtClassW Q (m / Q) a) m :=
    fun m hm => crtClassW_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQa2 hPodd hPspos hm
  have hDsetD : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), m ≤ D := fun m hm => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hm
  rw [two_mul]
  exact add_le_add
    (hbody x Lb F Krange k i _ X x D _ (fun m => crtClassW Q (m / Q) a) hk hx hi hXsub hNfloor hα
      hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev
      hFX hDx hLbb hfloor hDXM)
    (hbody x Lb F Krange k i _ X (x / 2 + 1) D _ (fun m => crtClassW Q (m / Q) a) hk hx hi hXsub
      hNfloor hα hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev
      herr_Mlev hFX hDx hLbb hfloor hDXM)

/-! ## 6. The band-leg per-box prices at the `2^k`-boundary (deliverable 3, the sym / low legs)

`sym_box_hprice_at_2pow` / `low_box_hprice_at_2pow` are the band analogues of
`box_hprice_at_2pow`, discharging the per-box `hprice` slots that PriceTwo's `sym_box_price_at_op`
/ `low_box_price_at_op` take as named inputs.  Sym additionally needs the `max`-collapse bridge
`max y (pieceN k) = pieceN k` (on the strip fact `y ≤ pieceN k`, `max_y_pieceN_eq`) to match the
terminal's `blockPrimeInd (pieceN k)` indicator; low needs no collapse. -/

/-- **`sym_box_hprice_at_2pow` (deliverable 3, the sym band leg).**  The per-box `hprice` slot of
`sym_box_price_at_op` at the `2^k`-boundary: the sym carrier's two-`T` sum is `≤ 2·(Kerr price)`.
Uses the `max`-collapse `max y (pieceN k) = pieceN k` (needs `y ≤ pieceN k`) to match the terminal
indicator, then `medium_box_price_at_op` twice — same structure as `box_hprice_at_2pow`. -/
theorem sym_box_hprice_at_2pow (z y Ps Q a : ℕ) (hQ1 : 1 ≤ Q) (hPspos : 0 < Ps)
    (hQPs : Nat.Coprime Q Ps) (hQa2 : Nat.Coprime Q (a + 2))
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x : ℕ) (ε₀ : ℝ) (j k i : ℕ) (Lb : ℝ) (F Krange X : ℕ) (QR : ℝ) (Dlev D : ℕ),
        2 ≤ k →
        y ≤ pieceN k →
        Real.exp (10 ^ 9) ≤ (x : ℝ) →
        i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange →
        X = 2 ^ (i + 1) - 1 →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((2 ^ k : ℕ) : ℝ) →
        N₀ ≤ 2 ^ k →
        2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) →
        2 ≤ X →
        1 ≤ D →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))
            / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (15 : ℝ)) →
        D < (2 ^ k + 1) * (2 ^ k + 1) →
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
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                  (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                    (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m
                  (x / 2 + 1)‖)
          ≤ 2 * ((Kbeta_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                    (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18
                + (6 * (Km_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                          (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                        * Kbeta'_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                            (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 15360 + 1)))
              * ((X : ℝ) * (pieceM k : ℝ))
              / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨Kc, N₀, hK0, hbody⟩ := medium_box_price_at_op
  refine ⟨Kc, N₀, hK0, fun x ε₀ j k i Lb F Krange X QR Dlev D hk hyN hx hi hXsub hNfloor hN₀ hL2
    hX2 hD1 hDge_x hDbnd hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor
    hDXM => ?_⟩
  rw [max_y_pieceN_eq hyN]
  have hα := norm_sym_leg_le_one z y ε₀ j (pieceN k) (pieceM k) i
  have hd1 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), (1 : ℕ) ≤ m := fun m hm => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hm
  have hcop2 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), Nat.Coprime (crtClassW Q (m / Q) a) m :=
    fun m hm => crtClassW_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQa2 hPodd hPspos hm
  have hDsetD : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), m ≤ D := fun m hm => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hm
  rw [two_mul]
  exact add_le_add
    (hbody x Lb F Krange k i _ X x D _ (fun m => crtClassW Q (m / Q) a) hk hx hi hXsub hNfloor hα
      hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev
      hFX hDx hLbb hfloor hDXM)
    (hbody x Lb F Krange k i _ X (x / 2 + 1) D _ (fun m => crtClassW Q (m / Q) a) hk hx hi hXsub
      hNfloor hα hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev
      herr_Mlev hFX hDx hLbb hfloor hDXM)

/-- **`low_box_hprice_at_2pow` (deliverable 3, the low band leg).**  The per-box `hprice` slot of
`low_box_price_at_op` at the `2^k`-boundary: the low carrier's two-`T` sum is `≤ 2·(Kerr price)`.
Indicator is already `blockPrimeInd (pieceN k)` (no `max` collapse); `medium_box_price_at_op`
twice, same structure as `box_hprice_at_2pow`. -/
theorem low_box_hprice_at_2pow (z y Ps Q a : ℕ) (hQ1 : 1 ≤ Q) (hPspos : 0 < Ps)
    (hQPs : Nat.Coprime Q Ps) (hQa2 : Nat.Coprime Q (a + 2))
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x : ℕ) (ε₀ : ℝ) (j k i : ℕ) (Lb : ℝ) (F Krange X : ℕ) (QR : ℝ) (Dlev D : ℕ),
        2 ≤ k →
        Real.exp (10 ^ 9) ≤ (x : ℝ) →
        i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange →
        X = 2 ^ (i + 1) - 1 →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((2 ^ k : ℕ) : ℝ) →
        N₀ ≤ 2 ^ k →
        2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) →
        2 ≤ X →
        1 ≤ D →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
        (Q : ℝ) * (QR * Dlev) ≤ (D : ℝ) →
        ((D : ℝ) ≤ Real.sqrt ((X : ℝ) * (pieceM k : ℝ))
            / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (15 : ℝ)) →
        D < (2 ^ k + 1) * (2 ^ k + 1) →
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
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
              (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1)) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
                (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                    (min (z * pieceN k + 1) (x + 1)) (x + 1)) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ 2 * ((Kbeta_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                    (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18
                + (6 * (Km_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                          (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                    + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                        * Kbeta'_min Kc (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                            (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 15360 + 1)))
              * ((X : ℝ) * (pieceM k : ℝ))
              / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ)) := by
  obtain ⟨Kc, N₀, hK0, hbody⟩ := medium_box_price_at_op
  refine ⟨Kc, N₀, hK0, fun x ε₀ j k i Lb F Krange X QR Dlev D hk hx hi hXsub hNfloor hN₀ hL2 hX2
    hD1 hDge_x hDbnd hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx hLbb hfloor
    hDXM => ?_⟩
  have hα := norm_low_leg_le_one z y ε₀ j (pieceN k) (min (z * pieceN k + 1) (x + 1)) (x + 1) i
  have hd1 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), (1 : ℕ) ≤ m := fun m hm => one_le_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hm
  have hcop2 : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), Nat.Coprime (crtClassW Q (m / Q) a) m :=
    fun m hm => crtClassW_coprime_of_mem (QR * (Dlev : ℝ)) hQ1 hQPs hQa2 hPodd hPspos hm
  have hDsetD : ∀ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < QR * Dlev)).image
      (fun d => Q * d), m ≤ D := fun m hm => le_D_of_mem_QImage (QR * (Dlev : ℝ)) hQ1 hDbnd hm
  rw [two_mul]
  exact add_le_add
    (hbody x Lb F Krange k i _ X x D _ (fun m => crtClassW Q (m / Q) a) hk hx hi hXsub hNfloor hα
      hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev
      hFX hDx hLbb hfloor hDXM)
    (hbody x Lb F Krange k i _ X (x / 2 + 1) D _ (fun m => crtClassW Q (m / Q) a) hk hx hi hXsub
      hNfloor hα hd1 hcop2 hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev
      herr_Mlev hFX hDx hLbb hfloor hDXM)

end Salt.Chen
