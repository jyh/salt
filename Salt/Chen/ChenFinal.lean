/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.ChenHeadline

/-!
# Node fin5 — the boundary-window scaffold (F1-rows a) + the band-carrier k-floor verdict

Design: `docs/blueprints/flags.md`, the `2026-07-14 fin4` entry (the enumerated fin5 remainder),
the `EDGE` / `PRICE-3b` / `PRICE-GATE` entries.  New file, no edits to landed files.

This node is the PRICE wave's intended summit — the assembly of the landed corpus into
`chen_headline`.  It is organized in floors (F1-rows → F2 → F3).  This file lands **floor
F1-rows(a)** (the boundary-window scaffold) and records the **band-carrier k-floor analysis**
demanded by the fin5 mandate before F1-rows(c).

## Floor F1-rows(a) — the boundary-window scaffold (this file, §§1–3)

For a box index `i` in the pieceN-boundary `dyadicBoundary (pieceN k) (pieceM k) (x/2+1) x F K`,
with `X = 2^{i+1}−1`, `M = pieceM k`, the boundary clauses pin `2^{i+k} ∈ (x/8, x]`, whence
`X·M ≍ x` (between `x/2` and `4x`), `√(X·M) ≍ √x`, and `log(X·M) ∈ [log x − 1, log x + 3]`.  These
are the reusable inputs of the (deferred) 27-row `box_hprice_at_2pow_lo` bundle.  All are
floor-independent (they concern `X·M` vs `x`), so they survive the catch #72 finding below.

## ★ CATCH #72 (the band-carrier k-floor ESCAPES the 7/16 floor) ★  (§4)

The fin5 mandate for F1-rows(c) required verifying the band carriers' live-box k-floors and, if a
band carrier's live range escapes the `x^{7/16}/8 ≤ 2^k` floor of the `_lo` price family, to
STOP-AND-FLAG.  **It escapes.**  The box leg meets the 7/16 floor via `kfloor_of_live_box`
(carrier VANISHES ABOVE its cap `z·pieceN k + 1`, so a LIVE box has `2^i ≤ z·2^k`, which with the
cutoff `x/8 < 2^i·2^k` forces `2^k ≥ x^{7/16}/8`).  The band carriers
`blockAlphaSym`/`blockAlphaLow` have the OPPOSITE geometry: they vanish BELOW a support floor
(`z·max(y, pieceN k)` / `z·y`) and
carry an upper support cap set by the large prime `p₂ ≤ pieceM k` / `p₂ ≤ pieceN k`.  A live band
box therefore has LARGE `2^i` and only an UPPER bound on `2^k`, giving no 7/16 floor.  The honest
band floor is `2^k ≳ x^{1/3}` (`blockAlphaLow` needs a prime `p₂ ∈ (y, 2^k−1]`, so it is IDENTICALLY
ZERO for `2^k ≤ y ~ x^{1/3}`; `blockAlphaSym` similarly).  The range `2^k ∈ (y+1, x^{7/16}/8) ≈
(x^{1/3}, x^{7/16}/8)` carries LIVE band boxes that neither landed route covers (vanishing needs
`2^k ≤ y+1`; the `_lo` price needs `2^k ≥ x^{7/16}/8`).  See `blockAlphaLow_eq_zero_of_pieceN_le` /
`blockAlphaSym_eq_zero_of_pieceM_le` (§4) for the kernel-checked lower edge of the live range and
the module report for the full derivation.  Consequence: F1-rows(c) as designed (reuse the 7/16
`_lo` family for the band legs) is INVALID; F2 (which consumes the band legs via
`hpriceSym`/`hpriceLow`) and F3 are therefore unreached.  The repair is a lower-floor price
construction (a `d0_window` variant at floor `~x^{1/3}` and the band price lemmas over it), which is
statement-level (new floor constant + a raised tower threshold for the `4·L^{17} ≤ W^{18}` margin)
and belongs to a Fable/human-directed session.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## §1 — the raw boundary bounds `x/2+1 < X·M ≤ 4x` (F1-rows(a), Nat)

The two Nat inequalities every downstream scale fact rests on.  The lower one is the boundary's
cutoff clause verbatim; the upper one is the EDGE corner-relaxation bound
`X·M ≤ 2^{i+1}·2^{k+1} = 4·2^i·2^k ≤ 4x` (the weak corner `2^i·2^k ≤ x`, no `+1` slack). -/

/-- **`boundary_XM_raw` (F1-rows(a), the raw Nat window).**  For a box `i` in the pieceN-boundary
with `X = 2^{i+1}−1`, `M = pieceM k`: `x/2+1 < X·M ≤ 4x`. -/
theorem boundary_XM_raw {x k i F K : ℕ}
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F K) :
    x / 2 + 1 < (2 ^ (i + 1) - 1) * pieceM k ∧ (2 ^ (i + 1) - 1) * pieceM k ≤ 4 * x := by
  rw [dyadicBoundary, Finset.mem_filter] at hi
  obtain ⟨-, hcorner, -, hcut⟩ := hi
  refine ⟨hcut, ?_⟩
  have hpk : pieceN k + 1 = 2 ^ k := by
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have hN : pieceN k = 2 ^ k - 1 := rfl
    omega
  have hMle : pieceM k ≤ 2 ^ (k + 1) := by
    have hM : pieceM k = 2 ^ (k + 1) - 1 := rfl
    omega
  calc (2 ^ (i + 1) - 1) * pieceM k
      ≤ 2 ^ (i + 1) * 2 ^ (k + 1) := Nat.mul_le_mul (Nat.sub_le _ _) hMle
    _ = 4 * (2 ^ i * 2 ^ k) := by rw [pow_succ 2 i, pow_succ 2 k]; ring
    _ = 4 * (2 ^ i * (pieceN k + 1)) := by rw [hpk]
    _ ≤ 4 * x := Nat.mul_le_mul (le_refl 4) hcorner

/-! ## §2 — the real + logarithmic scale facts (F1-rows(a))

From the raw Nat window, `X·M ≍ x` in `ℝ` and `log(X·M) ∈ [log x − 1, log x + 3]`.  The
derivation is `PriceOne.d0_window_of_XM`'s log paragraph, factored so any consumer of the box rows
can quote it.  Stated for generic `X, M` from the raw bounds (maximally reusable). -/

/-- **`xm_real_bounds` (F1-rows(a)).**  The real window from the raw Nat window: `0 < X·M`,
`x/2 < X·M`, `X·M ≤ 4x`. -/
theorem xm_real_bounds {x X M : ℕ} (hlo : x / 2 + 1 < X * M) (hhi : X * M ≤ 4 * x) :
    (0 : ℝ) < (X : ℝ) * (M : ℝ)
      ∧ (x : ℝ) / 2 < (X : ℝ) * (M : ℝ)
      ∧ (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) := by
  have hXMposN : 0 < X * M := by omega
  have hXMposR : (0 : ℝ) < (X : ℝ) * (M : ℝ) := by exact_mod_cast hXMposN
  have hhiR : (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) := by exact_mod_cast hhi
  refine ⟨hXMposR, ?_, hhiR⟩
  have h1 : x < (x / 2 + 1) * 2 := by omega
  have h2 : x / 2 + 1 ≤ X * M := by omega
  have h1R : (x : ℝ) < ((x / 2 + 1 : ℕ) : ℝ) * 2 := by exact_mod_cast h1
  have h2R : ((x / 2 + 1 : ℕ) : ℝ) ≤ (X : ℝ) * (M : ℝ) := by exact_mod_cast h2
  push_cast at h1R h2R
  linarith

/-- **`xm_log_bounds` (F1-rows(a)).**  `log x − 1 ≤ log(X·M) ≤ log x + 3` from the raw Nat window
(`x ≥ 2`).  The `−1`/`+3` come from `log 2 ≤ 1` and `log 4 ≤ 3`. -/
theorem xm_log_bounds {x X M : ℕ} (hx : 2 ≤ x)
    (hlo : x / 2 + 1 < X * M) (hhi : X * M ≤ 4 * x) :
    Real.log x - 1 ≤ Real.log ((X : ℝ) * (M : ℝ))
      ∧ Real.log ((X : ℝ) * (M : ℝ)) ≤ Real.log x + 3 := by
  obtain ⟨hXMposR, hhalf, hhiR⟩ := xm_real_bounds hlo hhi
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  constructor
  · have hlog : Real.log ((x : ℝ) / 2) ≤ Real.log ((X : ℝ) * (M : ℝ)) :=
      Real.log_le_log (by linarith) hhalf.le
    rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)] at hlog
    have h2log : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith
  · have h1 : Real.log ((X : ℝ) * (M : ℝ)) ≤ Real.log (4 * (x : ℝ)) :=
      Real.log_le_log hXMposR hhiR
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hxpos)] at h1
    have h4log : Real.log 4 ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
    linarith

/-- **`boundary_log_bounds` (F1-rows(a), composed).**  The `[log x − 1, log x + 3]` window for a
pieceN-boundary box at `X = 2^{i+1}−1`, `M = pieceM k` — the exact `Real.log ((X:ℝ)·(pieceM k))`
shape the box rows consume. -/
theorem boundary_log_bounds {x k i F K : ℕ} (hx : 2 ≤ x)
    (hi : i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F K) :
    Real.log x - 1 ≤ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ))
      ∧ Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k : ℝ)) ≤ Real.log x + 3 := by
  obtain ⟨hlo, hhi⟩ := boundary_XM_raw hi
  exact xm_log_bounds hx hlo hhi

/-! ## §3 — the `√(X·M) ≍ √x` window (F1-rows(a)) -/

/-- **`xm_sqrt_bounds` (F1-rows(a)).**  `(1/2)·√x ≤ √(X·M) ≤ 2·√x` from the raw Nat window. -/
theorem xm_sqrt_bounds {x X M : ℕ} (hlo : x / 2 + 1 < X * M) (hhi : X * M ≤ 4 * x) :
    (1 / 2 : ℝ) * Real.sqrt x ≤ Real.sqrt ((X : ℝ) * (M : ℝ))
      ∧ Real.sqrt ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.sqrt x := by
  obtain ⟨hXMposR, hhalf, hhiR⟩ := xm_real_bounds hlo hhi
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  constructor
  · -- lower: `(1/2)√x = √(x/4) ≤ √(X·M)` (since `x/4 < x/2 < X·M`)
    have heq : (1 / 2 : ℝ) * Real.sqrt x = Real.sqrt ((1 / 4) * x) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
        show Real.sqrt (1 / 4) = 1 / 2 by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)]
    rw [heq]
    exact Real.sqrt_le_sqrt (by linarith)
  · -- upper: `√(X·M) ≤ √(4x) = 2√x`
    have hs4 : Real.sqrt (4 * (x : ℝ)) = 2 * Real.sqrt x := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)]
    calc Real.sqrt ((X : ℝ) * (M : ℝ)) ≤ Real.sqrt (4 * (x : ℝ)) := Real.sqrt_le_sqrt hhiR
      _ = 2 * Real.sqrt x := hs4

/-! ## §4 — CATCH #72: the band carriers vanish only at `2^k ≲ x^{1/3}` (well below `x^{7/16}`)

These two lemmas pin the LOWER edge of the band carriers' live range and make the catch #72 finding
kernel-certain: the low/sym carriers are identically zero only for `2^k` at the `y ~ x^{1/3}` scale,
NOT the `x^{7/16}/8` price floor.  So the band leg is live throughout `2^k ∈ (y+1, x^{7/16}/8)`,
where neither the vanishing route (needs `pieceN k ≤ y`) nor the `_lo` price route (needs
`x^{7/16}/8 ≤ 2^k`) applies — the gap that halts F1-rows(c). -/

/-- **`blockAlphaLow_eq_zero_of_pieceN_le` (catch #72 evidence).**  The low band carrier
`blockAlphaLow z y ε₀ j (pieceN k)` is IDENTICALLY zero when `pieceN k ≤ y` (i.e. `2^k ≤ y + 1`):
its defining semiprime needs a prime `p₂ ∈ (y, pieceN k]`, empty when `pieceN k ≤ y`.  Hence the low
leg's live range starts at `2^k > y + 1 ~ x^{1/3}`, far below the `x^{7/16}/8` price floor. -/
theorem blockAlphaLow_eq_zero_of_pieceN_le {z y : ℕ} {ε₀ : ℝ} {j k m : ℕ}
    (hle : pieceN k ≤ y) :
    blockAlphaLow z y ε₀ j (pieceN k) m = 0 := by
  unfold blockAlphaLow
  rw [if_neg]
  rintro ⟨p₁, p₂, -, -, -, -, hyp2, hp2N, -, -⟩
  -- `y < p₂ ≤ pieceN k ≤ y`
  omega

/-- **`blockAlphaSym_eq_zero_of_pieceM_le` (catch #72 evidence).**  The sym band carrier
`blockAlphaSym z y ε₀ j (pieceN k) (pieceM k)` is IDENTICALLY zero when `pieceM k ≤ y` (i.e.
`2^{k+1} ≤ y + 1`, `2^k ≤ (y+1)/2`): its semiprime needs a prime
`p₂ ∈ (max y (pieceN k), pieceM k]`, empty when `pieceM k ≤ y ≤ max y (pieceN k)`.  Hence the
sym leg's live range starts at
`2^k ≳ x^{1/3}/2`, far below the `x^{7/16}/8` price floor. -/
theorem blockAlphaSym_eq_zero_of_pieceM_le {z y : ℕ} {ε₀ : ℝ} {j k m : ℕ}
    (hle : pieceM k ≤ y) :
    blockAlphaSym z y ε₀ j (pieceN k) (pieceM k) m = 0 := by
  unfold blockAlphaSym
  rw [if_neg]
  rintro ⟨p₁, p₂, -, -, -, -, hmax, hp2M, -, -⟩
  -- `max y (pieceN k) < p₂ ≤ pieceM k ≤ y ≤ max y (pieceN k)`
  have hy : y ≤ max y (pieceN k) := le_max_left _ _
  omega

end Salt.Chen
