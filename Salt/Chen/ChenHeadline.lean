/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.PriceClose

/-!
# Node fin4 — the k-floor lemma + the piece rows + the assembly → `chen_headline`

Design: `docs/blueprints/flags.md`, the `2026-07-14 EDGE` entry (the Fable adjudication
dissolving the coupling obligation — the `kfloor_of_live_box` arithmetic), the `PRICE-3b`
/ `PRICE-1` / `PRICE-GATE` entries.

This is the PRICE wave's summit.  It assembles the landed corpus into the headline theorem
`chen_headline`.  New file, no edits to landed files.

## Floor F1 — the k-floor keystone + the piece-parameter rows

* **`kfloor_of_live_box`** (the EDGE adjudication).  For a box index `i` in the
  pieceN-boundary whose carrier is LIVE (`2^i < cap = z·pieceN k + 1`), the boundary cutoff
  clause `x/2 < X·M` (with `X = 2^{i+1}−1`, `M = pieceM k`) forces `x/8 < 2^{i+k}`, and the
  carrier-live clause gives `2^i ≤ z·2^k`; together `z·2^{2k} > x/8`, so at the operating
  `z ≤ x^{1/8}` one gets `x^{7/16}/8 ≤ 2^k` — the `_lo`-floor hypothesis of the repaired
  price lemmas for every live box.  The gap range `(x^{1/3}/2, x^{7/16}/8)` left open by the
  carrier k-floor (`y_lt_two_pow_succ_of_carrier`) is EMPTY of live boundary boxes.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## F1.1 — `kfloor_of_live_box` (the EDGE adjudication, the honest 7/16 floor) -/

/-- **`kfloor_of_live_box` (F1 keystone, the EDGE adjudication).**  For a box index `i` in the
pieceN-boundary `dyadicBoundary (pieceN k) (pieceM k) (x/2+1) x (z·y) K` whose carrier is LIVE
(`hlive : 2^i < z·pieceN k + 1`), at the operating scale `hz : (z : ℝ) ≤ x^{1/8}`:
`x^{7/16}/8 ≤ 2^k`.

Mechanism (the Fable adjudication that dissolves fin3's surfaced coupling obligation): the
boundary cutoff clause `x/2 + 1 < (2^{i+1}−1)·pieceM k` gives `x/2 < 4·2^{i+k}`, i.e.
`x/8 < 2^i·2^k`; the carrier-live clause gives `2^i ≤ z·2^k`; multiplying, `x/8 < z·2^{2k}
≤ x^{1/8}·(2^k)²`, whence `(2^k)² > x^{7/8}/8` and `2^k > x^{7/16}/(2√2) ≥ x^{7/16}/8`
(`2√2 < 8`). -/
theorem kfloor_of_live_box {x z y k i K : ℕ} (hx : (1 : ℝ) ≤ (x : ℝ))
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K)
    (hlive : 2 ^ i < z * pieceN k + 1)
    (hz : (z : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8)) :
    (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ ((2 ^ k : ℕ) : ℝ) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx
  -- Extract the cutoff clause from boundary membership.
  rw [dyadicBoundary, Finset.mem_filter] at hi
  obtain ⟨-, -, -, hcut⟩ := hi
  -- `pieceM k = 2^{k+1} - 1`, `pieceN k = 2^k - 1`.
  have hM : pieceM k = 2 ^ (k + 1) - 1 := rfl
  have hN : pieceN k = 2 ^ k - 1 := rfl
  rw [hM] at hcut
  -- Step 1 (Nat): `x/2 + 1 < 4 * 2^i * 2^k`, hence `x < 8 * 2^i * 2^k`.
  have hcut2 : x / 2 + 1 < 4 * (2 ^ i * 2 ^ k) :=
    calc x / 2 + 1 < (2 ^ (i + 1) - 1) * (2 ^ (k + 1) - 1) := hcut
      _ ≤ 2 ^ (i + 1) * 2 ^ (k + 1) := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = 4 * (2 ^ i * 2 ^ k) := by ring
  have hxN : x < 8 * (2 ^ i * 2 ^ k) := by omega
  -- Step 2: carrier-live gives `2^i ≤ z * 2^k` (Nat).
  have hliveN : 2 ^ i ≤ z * 2 ^ k := by
    rw [hN] at hlive
    calc 2 ^ i ≤ z * (2 ^ k - 1) := by omega
      _ ≤ z * 2 ^ k := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  -- Step 3: real forms (uniformly in `(2:ℝ)^i`, `(2:ℝ)^k`).
  have hxR : (x : ℝ) < 8 * ((2 : ℝ) ^ i * (2 : ℝ) ^ k) := by exact_mod_cast hxN
  have hliveR : (2 : ℝ) ^ i ≤ (z : ℝ) * (2 : ℝ) ^ k := by exact_mod_cast hliveN
  have hknn : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
  have hcutR : (x : ℝ) / 8 < (2 : ℝ) ^ i * (2 : ℝ) ^ k := by linarith [hxR]
  -- Step 4: `x/8 < 2^i·2^k ≤ z·(2^k)² ≤ x^{1/8}·(2^k)²`.
  have hProd : (x : ℝ) / 8 < (z : ℝ) * ((2 : ℝ) ^ k * (2 : ℝ) ^ k) := by
    nlinarith [hcutR, mul_le_mul_of_nonneg_right hliveR hknn]
  have hProd2 : (x : ℝ) / 8 < (x : ℝ) ^ ((1 : ℝ) / 8) * ((2 : ℝ) ^ k * (2 : ℝ) ^ k) := by
    have hk2nn : (0 : ℝ) ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ k := by positivity
    nlinarith [hProd, mul_le_mul_of_nonneg_right hz hk2nn]
  -- Step 5: cancel `x^{1/8}`: `x^{7/8}/8 < (2^k)²`.
  have hx18pos : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hxpos _
  have hxeq : (x : ℝ) = (x : ℝ) ^ ((7 : ℝ) / 8) * (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_add hxpos, show (7 : ℝ) / 8 + 1 / 8 = 1 by norm_num, Real.rpow_one]
  have hsub : (x : ℝ) / 8
      = (x : ℝ) ^ ((7 : ℝ) / 8) / 8 * (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [div_mul_eq_mul_div, ← hxeq]
  have hPsq : (x : ℝ) ^ ((7 : ℝ) / 8) / 8 < (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
    rw [hsub, mul_comm ((x : ℝ) ^ ((1 : ℝ) / 8)) ((2 : ℝ) ^ k * (2 : ℝ) ^ k)] at hProd2
    exact lt_of_mul_lt_mul_right hProd2 hx18pos.le
  -- Step 6: `(x^{7/16})² = x^{7/8}`, so `(x^{7/16}/8)² < (2^k)²` ⟹ `x^{7/16}/8 ≤ 2^k`.
  have hxx : (x : ℝ) ^ ((7 : ℝ) / 16) * (x : ℝ) ^ ((7 : ℝ) / 16) = (x : ℝ) ^ ((7 : ℝ) / 8) := by
    rw [← Real.rpow_add hxpos]; congr 1; norm_num
  have hann : (0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 16) := Real.rpow_nonneg hxpos.le _
  have h78nn : (0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 8) := Real.rpow_nonneg hxpos.le _
  rw [show ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k by push_cast; ring]
  nlinarith [hPsq, hxx, hann, hknn, h78nn,
    show (0 : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 16) / 8 + (2 : ℝ) ^ k by positivity]

/-! ## F1.2 — `box_hprice_at_2pow_lo` (the priced-branch supplier at the 7/16 floor)

`kfloor_of_live_box` supplies the `x^{7/16}/8 ≤ 2^k` floor for every LIVE boundary box, but the
landed `box_hprice_at_2pow` (PriceThree:228) demands the STRONGER `x^{11/24}/8 ≤ 2^k` floor
(via `medium_box_price_at_op`).  The Finding-3 strip `2^k ∈ [x^{7/16}/8, x^{11/24}/8)` carries
LIVE non-cancelling boxes, so the priced branch of the dichotomy must instead call the strip
terminal `medium_box_price_at_op_lo` (PriceTwo:652), whose conclusion is CHARACTER-FOR-CHARACTER
identical to `medium_box_price_at_op`'s (same `Kbeta_min`/`Km_min`/`Kbeta'_min` price) but whose
`hNfloor` is the 7/16 floor.  `box_hprice_at_2pow_lo` is the exact `_lo` mirror of
`box_hprice_at_2pow` — same conclusion (`Price j k i := 2·Kerr`), same hypothesis list, only the
block floor relaxed to `x^{7/16}/8`. -/

/-- **`box_hprice_at_2pow_lo` (F1, the priced-branch supplier).**  The `_lo` (7/16-floor) analogue
of `PriceThree.box_hprice_at_2pow`: the box carrier's two-`T` disc sum is `≤ 2·(Kerr price)` at
the operating point, with the block floor relaxed to `x^{7/16}/8 ≤ 2^k` (the floor
`kfloor_of_live_box` supplies for every live boundary box).  Conclusion identical to
`box_hprice_at_2pow`; routes through `medium_box_price_at_op_lo`. -/
theorem box_hprice_at_2pow_lo (z y Ps Q a : ℕ) (hQ1 : 1 ≤ Q) (hPspos : 0 < Ps)
    (hQPs : Nat.Coprime Q Ps) (hQa2 : Nat.Coprime Q (a + 2))
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) :
    ∃ (Kc : ℝ) (N₀ : ℕ), 0 < Kc ∧
      ∀ (x : ℕ) (ε₀ : ℝ) (j k i : ℕ) (Lb : ℝ) (F Krange X : ℕ) (QR : ℝ) (Dlev D : ℕ),
        2 ≤ k →
        Real.exp (10 ^ 9) ≤ (x : ℝ) →
        i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange →
        X = 2 ^ (i + 1) - 1 →
        (x : ℝ) ^ ((7 : ℝ) / 16) / 8 ≤ ((2 ^ k : ℕ) : ℝ) →
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
  obtain ⟨Kc, N₀, hK0, hbody⟩ := medium_box_price_at_op_lo
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

end Salt.Chen
