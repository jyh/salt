/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SwitchW2

/-!
# GLU-2W — STEP-0 inventory and ★ CATCH #68 ★: the A3W2 budget rows are jointly
unsatisfiable (the diagonal row busts `hNum` at every operating point)

Node GLU-2W (the FINAL node: the H_W ∃-package → `chen_headline` via
`chen_of_hypotheses_W`, `Salt/Chen/Assembly.lean`).  The mandated STEP 0 consolidated the
obligation inventory from the six supplier chains; the audit of the A3W2 row ledger found
the `hSum`/`hNum` budget rows of `hBVblocksW_discharge` (`Salt/Chen/SwitchW2.lean`, the
composed `hA3` supplier) **jointly unsatisfiable at every operating point** — kernel-checked
below (`catch68_hSum_hNum_infeasible`).  Per the node mandate ("if ANY row genuinely fails,
STOP AND FLAG (= catch #68)") and Iron Rule 4, the summit is NOT attempted past this row;
this file lands the certificate and the inventory.  `chen_headline` is NOT produced.

## STEP 0 — the obligation inventory (H_W's 12 conjuncts, from the LANDED docstrings)

Per threshold `X`, at `x := max x₀ (2X + 2)` (tower `x₀ ≥ exp(exp(2·w0N ε))`-form, gate C2),
`ε = 2·10⁻⁸` frozen, `Q = Qval ε`, `a = Q − 1`, `w' = w0N ε`, `z/y/D` per M4F floors,
`Dlev = ⌊x^{497/1000}⌋`, `P = ∏_{p ∈ [w', z)} p`, `Ps = ∏_{p ∈ [w', y)} p`:

| # | H_W slot | supplier chain | STEP-0 status |
|---|---|---|---|
| 1 | `X ≤ x/2`, `2 ≤ x`, `2 ≤ z`, `3 ≤ w'` | arithmetic at the operating point | ready |
| 2 | `hyx : x < (y+1)³` | `GlueFinal.hyx_at_op` | ready (landed) |
| 3 | `hQfull` | `Qval` support (`Finset.range (w0N ε)` filter) | ready |
| 4 | `hPfull'` | `Ico w' z`-primorial (mirror `sievePrimorial`) | ready |
| 5 | `hQa2` | `residue_witness` at `a = Q − 1` | ready (landed) |
| 6 | `hA1` | `TwinA1W` Part F chain; W-LEVEL/W-CLOSE rows (tower-sized) | ready |
| 7 | `hA2` | `TwinA2W` Part G chain; W2-LEVEL/W2-CLOSE + per-prime rows | ready |
| 8 | `hA3` | `mainA3_of_block_remainders_W` ← `hBVblocksW_discharge` | ★ **CATCH #68** ★ |
| 9 | `hcount` (ledger input) | `CountW.tripleSum_le_cbar_final_W` + equidist rows | ready |
| 10 | `hledger` | `normalized_package` at `X_W^Q`; `hEbundle` via `W_twinA1_ge` | ready mod #8 |
| 11 | finding-3 lower-floor `d0` variant (`N ≥ √(x/(24z))`) | in-file re-proof | behind #8 |
| 12 | finding-5 `hCE_W` crumb | Headline-docstring route | behind #8 |

Row-6 detail: `twin_A1_lower_B_W` + `twinA1_hBV_W` + `A1primeSumW_bridge`, with
`h4 := h4_cond_of_base`, `hstepWPC := stepHypWPC_sharpB`, and the value certificate
`fchain_A1_final ∘ logRatio_A1_mem`.  Row-7 detail: the `twin_A2_upper` aggregation with
`hQmPr` from the `Qval` support and the `cdiv`/`logRatio` operating rows.  Row-10 detail:
`hEbundle ≤ 1/200` at the C7 crude scale `X_W^Q ≥ 32e^{−70}·x/(φ(Q)·L²)`-form, every
`e`-term `O(1/log z)` or `polylog/x^c`; blocked only through `mainA3` (row 8).

## ★ CATCH #68 — the `hSum`/`hNum` row pair of `hBVblocksW_discharge` is contradictory ★

`hBVblocksW_discharge` (SwitchW2, THE composed `hA3` supplier; same shape in its
composition `example`) demands, verbatim:

* `hSum : ∑_{j ≤ maxBlock} [ (∑_k ∑_{i ∈ dyadicBoundary} Price j k i)
    + ( ½·∑_k PsymK j k + ∑_k PlowK j k
        + ½·τ(Ps)·∑_{k ∈ range(log₂x + 1)} y·(pieceM k − pieceN k) ) ] ≤ RHD`
* `hNum : RHD + RCE ≤ x/(log x)^10`,

where `τ(Ps) = (Nat.divisors Ps).card` and the diagonal summand is a FIXED formula (row 8
of the A3W2 ledger, inherited verbatim from the landed `BandClose.Plo_discharge` through
`PloW_discharge`).  But:

* `hprice`/`hpriceSym`/`hpriceLow` force `Price, PsymK, PlowK ≥ 0` on the summation domains
  (each dominates a sum of norms);
* `pieceM k − pieceN k = 2^k`, so the `k = ⌊log₂ x⌋` term alone gives
  `∑_k y·(pieceM k − pieceN k) ≥ y·2^{⌊log₂x⌋} > y·x/2`;
* `τ(Ps) ≥ 1` (`Ps ≠ 0`), and the `j = 0` block summand is present.

Hence every admissible `RHD` obeys `RHD ≥ ½·τ(Ps)·y·x/2 ≥ x/4` (already at `y ≥ 1`), while
`hCE` forces `RCE ≥ 0` and `hNum` caps `RHD + RCE ≤ x/(log x)^10 ≤ x/1024` for `x ≥ 8` —
contradiction.  **The row pair is unsatisfiable for EVERY `x ≥ 8`, `y ≥ 1`, `Ps ≠ 0`** — no
choice of `x₀`, prices, `RHD`, `RCE` repairs it (`catch68_hSum_hNum_infeasible` below).

### Both sides' values (the mandate's requirement)

At the honest operating point (`y = ⌊x^{1/3}⌋`, `Ps = ∏_{p ∈ [w', y)} p`, tower `x`):

* forced: `RHD ≥ ½·2^{π(y) − π(w0N ε)}·⌊x^{1/3}⌋·x/2` — the `τ(Ps) = 2^{ω(Ps)}` factor alone
  is `2^{≈ 3x^{1/3}/log x}`;
* demanded: `RHD + RCE ≤ x/(log x)^{10}`;
* deficit factor `≥ y·(log x)^{10}/8 ≥ x^{1/3}` BEFORE the `τ(Ps)` factor — and the
  kernel-checked minimal form (`x ≥ 8`, `y ≥ 1`, `τ(Ps) ≥ 1`) is already `x/4` vs `x/1024`.

### Root cause

`PloW_discharge` (SwitchW2 — the verbatim W-mirror of the landed `BandClose.Plo_discharge`)
bounds the `d`-filtered diagonal-disc sum by `(# ALL divisors of Ps) × (the crude per-box
kernel y·(M − N), BandSplit.bandDiagCount_le) × (ALL pieces k)` — a triple over-count
relative to `BandSplit`'s item-3 RATIFIED numeric plan, which requires (i) the global
diagonal support cutoff (`p₂ = p₃ = p` forces `p ≤ √x`, so `#diag ≤ y·2√x ≈ 2x^{5/6}`
against the crude `∑_k y·2^k ≈ 2xy`), (ii) the `w₀`-rough divisor crumb on the residue side
(`d ∣ Ps ∧ prod ≡ crtClassW (mod Q·d) ⟹ d ∣ prod − 2`, and a `w₀`-rough `d` has
`#{d} ≤ 2^{log x/log w₀} = x^{log 2/log w0R ε} = x^{o(1)}` — NOT `τ(Ps)`), and (iii) the
ν-weighted unit side (`∑_{d ∣ Ps} ν(d) = Ps/φ(Ps) = O(log y/log w₀)`).  The honest close is
`≲ x^{5/6 + o(1)} ≪ x/L^{10}` (room `x^{1/6−o(1)}`) — the mathematics is fine; the LANDED ROW
SHAPE is not.  The failure was never exercised: GLU-2 (catch #64) blocked upstream of
`hSum`, and A3W2 landed `hSum`/`hNum` as hypotheses (the kernel never evaluates
satisfiability of a hypothesis bundle); its row-8 note "the diagonal only shrinks" is true
per-`(d, box)` but the AGGREGATED formula was never audited against the budget.

### Repair direction (Fable-tier — statement changes to the ratified ledger; NOT attempted)

Either (a) abstract the diagonal term of `PloW_discharge`/`Plo_discharge` into a named price
slot `Pdiag` (re-emitting `hBVblocksW_discharge` with `Pdiag j` in `hSum`), discharged at
GLU-2W by the item-3 arithmetic above; or (b) warrant a bypass node that fills
`hBlockW_of_window_prices`' ABSTRACT `Plo` slot directly (that landed statement is NOT
infeasible — only the composed discharge's instantiation of it is), with an in-file honest
diagonal close.  Estimated new mathematics either way: the `√x` diagonal cutoff, the
`w₀`-rough divisor crumb, and the `∑ ν(d)` band constant — class B/C, ~300–500 lines.
NOTE: the landed non-W `BandClose.Plo_discharge` carries the identical row, so any revival
of the unshifted chain inherits the same catch.

## What this file lands (sorry-free, axiom-clean; NEW file, no landed file touched)

* `catch68_price_rows_nonneg` — the three price families are forced nonnegative by the
  verbatim `hprice`/`hpriceSym`/`hpriceLow` rows (the wedge of the certificate).
* `catch68_hSum_hNum_infeasible` — THE CERTIFICATE: against the VERBATIM row shapes of
  `hBVblocksW_discharge`, the bundle {`hprice`, `hpriceSym`, `hpriceLow`, `hSum`, `hCE`,
  `hNum`} + (`8 ≤ x`, `1 ≤ y`, `Ps ≠ 0`) is `False`.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]`).
-/

namespace Salt.Chen

/-! ## Part A — the forced nonnegativity of the price families -/

/-- The `hprice` row forces `0 ≤ Price j k i` on the boundary: its left side is a sum of
norms.  (Stated for the exact `hprice` shape of `hBVblocksW_discharge`.) -/
theorem catch68_price_rows_nonneg {x z y : ℕ} {ε₀ : ℝ} {Q a Ps : ℕ} {QR : ℝ}
    {Dlev K : ℕ} (Price : ℕ → ℕ → ℕ → ℝ)
    (hprice : ∀ j k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                  (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                    (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ Price j k i) :
    ∀ j k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
      0 ≤ Price j k i := by
  intro j k i hi
  refine le_trans ?_ (hprice j k i hi)
  exact add_nonneg (Finset.sum_nonneg fun m _ => norm_nonneg _)
    (Finset.sum_nonneg fun m _ => norm_nonneg _)

/-! ## Part B — ★ THE CERTIFICATE ★ -/

/-- **CATCH #68 — the A3W2 budget rows are jointly unsatisfiable.**  Against the VERBATIM
row shapes of `hBVblocksW_discharge` (`Salt/Chen/SwitchW2.lean`): the price rows
(`hprice`/`hpriceSym`/`hpriceLow`), the budget rows (`hSum`/`hNum`) and the conversion row
(`hCE`), together with `8 ≤ x`, `1 ≤ y` and `Ps ≠ 0` (all three forced at every honest
operating point — `x ≥ x₀`, `y = ⌊x^{1/3}⌋`, `Ps` a nonzero primorial), are contradictory.

Mechanism: the diagonal summand `½·τ(Ps)·∑_{k ≤ log₂x} y·(pieceM k − pieceN k)` of `hSum`
is a fixed formula `≥ ½·1·y·2^{⌊log₂x⌋} > x/4`, the price families are forced `≥ 0`, so
`RHD ≥ x/4`; `hCE` forces `RCE ≥ 0`; and `hNum` demands `RHD + RCE ≤ x/(log x)^{10} ≤
x/1024` at `x ≥ 8`.  See the module header for both sides' values at the honest operating
point (the deficit there is `≥ x^{1/3}·(log x)^{10}` before the `τ(Ps) = 2^{ω(Ps)}` factor). -/
theorem catch68_hSum_hNum_infeasible (x z y : ℕ) (ε₀ : ℝ) (Q a Ps : ℕ) (QR : ℝ)
    (Dlev X K : ℕ) (hx8 : 8 ≤ x) (hy1 : 1 ≤ y) (hPs0 : Ps ≠ 0)
    (Price : ℕ → ℕ → ℕ → ℝ)
    (hprice : ∀ j k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                  (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                    (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ Price j k i)
    (PsymK PlowK : ℕ → ℕ → ℝ)
    (hpriceSym : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PsymK j k)
    (hpriceLow : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PlowK j k)
    (RHD RCE : ℝ)
    (hSum : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ((∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
              Price j k i)
          + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k)
             + (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k)
             + (1 / 2) * ((Nat.divisors Ps).card : ℝ)
                 * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
                     (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ)))) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then blockConvErrW x z y ε₀ j Q d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) : False := by
  classical
  -- ① the price families are forced nonnegative
  have hPrice_nn := catch68_price_rows_nonneg (x := x) (z := z) (y := y) (ε₀ := ε₀)
    (Q := Q) (a := a) (Ps := Ps) (QR := QR) (Dlev := Dlev) (K := K) Price hprice
  have hSym_nn : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1), 0 ≤ PsymK j k := fun j k hk =>
    le_trans (Finset.sum_nonneg fun m _ => norm_nonneg _) (hpriceSym j k hk)
  have hLow_nn : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1), 0 ≤ PlowK j k := fun j k hk =>
    le_trans (Finset.sum_nonneg fun m _ => norm_nonneg _) (hpriceLow j k hk)
  -- ② the diagonal formula is bounded below by its top piece: `∑_k y·2^k ≥ y·2^{log₂x} > x/2`
  have hxlt : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  have hpiece : pieceM (Nat.log 2 x) - pieceN (Nat.log 2 x) = 2 ^ Nat.log 2 x := by
    unfold pieceM pieceN
    have h2 : (2 : ℕ) ^ (Nat.log 2 x + 1) = 2 * 2 ^ Nat.log 2 x := by rw [pow_succ]; ring
    have h1 : (1 : ℕ) ≤ 2 ^ Nat.log 2 x := Nat.one_le_two_pow
    omega
  have hterm : (x : ℝ) / 2
      ≤ (y : ℝ) * ((pieceM (Nat.log 2 x) - pieceN (Nat.log 2 x) : ℕ) : ℝ) := by
    have hxlt2 : x < 2 * 2 ^ Nat.log 2 x := by
      have h2 : (2 : ℕ) ^ (Nat.log 2 x + 1) = 2 * 2 ^ Nat.log 2 x := by rw [pow_succ]; ring
      omega
    have hxltR : (x : ℝ) < 2 * ((2 ^ Nat.log 2 x : ℕ) : ℝ) := by exact_mod_cast hxlt2
    have hy1R : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
    have hpk : (0 : ℝ) ≤ ((2 ^ Nat.log 2 x : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hpiece]
    have h1 : (x : ℝ) / 2 < ((2 ^ Nat.log 2 x : ℕ) : ℝ) := by linarith
    have h2 : ((2 ^ Nat.log 2 x : ℕ) : ℝ)
        ≤ (y : ℝ) * ((2 ^ Nat.log 2 x : ℕ) : ℝ) := le_mul_of_one_le_left hpk hy1R
    linarith
  have hS_nn : (0 : ℝ) ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1),
      (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hsum_diag : (x : ℝ) / 2 ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1),
      (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) :=
    le_trans hterm (Finset.single_le_sum
      (f := fun k => (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ))
      (fun k _ => by positivity) (Finset.self_mem_range_succ (Nat.log 2 x)))
  -- ③ the divisor count is ≥ 1 (`Ps ≠ 0`)
  have hcard1 : (1 : ℝ) ≤ ((Nat.divisors Ps).card : ℝ) := by
    have h : 0 < (Nat.divisors Ps).card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hPs0⟩
    exact_mod_cast h
  have hkey : (x : ℝ) / 2 ≤ ((Nat.divisors Ps).card : ℝ)
      * ∑ k ∈ Finset.range (Nat.log 2 x + 1), (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) :=
    calc (x : ℝ) / 2
        ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1),
            (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) := hsum_diag
      _ = 1 * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
            (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) := (one_mul _).symm
      _ ≤ ((Nat.divisors Ps).card : ℝ)
            * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
                (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hcard1 hS_nn
  -- ④ every `j`-summand of `hSum`'s left side is nonnegative, and the `j = 0` one
  --   dominates the diagonal formula; hence `RHD ≥ x/4`.
  have hG_nn : ∀ j ∈ Finset.range (maxBlock x z ε₀ + 1),
      (0 : ℝ) ≤ (∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
              Price j k i)
          + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k)
             + (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k)
             + (1 / 2) * ((Nat.divisors Ps).card : ℝ)
                 * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
                     (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ)) := by
    intro j _
    have h1 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1),
        ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price j k i :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i hi => hPrice_nn j k i hi
    have h2 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k :=
      Finset.sum_nonneg fun k hk => hSym_nn j k hk
    have h3 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k :=
      Finset.sum_nonneg fun k hk => hLow_nn j k hk
    have h4 : (0 : ℝ) ≤ (1 / 2) * ((Nat.divisors Ps).card : ℝ)
        * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
            (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) := by
      apply mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hS_nn
    linarith
  have hj0mem : 0 ∈ Finset.range (maxBlock x z ε₀ + 1) :=
    Finset.mem_range.mpr (Nat.succ_pos _)
  have hRHD : (x : ℝ) / 4 ≤ RHD := by
    have hj0 := Finset.single_le_sum hG_nn hj0mem
    have h1 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1),
        ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K, Price 0 k i :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i hi => hPrice_nn 0 k i hi
    have h2 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK 0 k :=
      Finset.sum_nonneg fun k hk => hSym_nn 0 k hk
    have h3 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK 0 k :=
      Finset.sum_nonneg fun k hk => hLow_nn 0 k hk
    have hassoc : (1 / 2) * ((Nat.divisors Ps).card : ℝ)
        * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
            (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ)
        = (((Nat.divisors Ps).card : ℝ)
            * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
                (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ)) / 2 := by ring
    -- the j = 0 summand ≥ diagonal formula ≥ (x/2)/2
    have hdiag : (x : ℝ) / 4 ≤ (1 / 2) * ((Nat.divisors Ps).card : ℝ)
        * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
            (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) := by
      rw [hassoc]
      linarith
    linarith [hSum, hj0, hdiag, h1, h2, h3]
  -- ⑤ the conversion row forces `RCE ≥ 0`
  have hconv_nn : ∀ j d, 0 ≤ blockConvErrW x z y ε₀ j Q d := by
    intro j d
    unfold blockConvErrW
    apply mul_nonneg
    · rw [nuChen_apply]; positivity
    · unfold blockNonUnitCountM; positivity
  have hRCE : (0 : ℝ) ≤ RCE := by
    refine le_trans ?_ hCE
    refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun d _ => ?_
    split_ifs with h
    · exact hconv_nn j d
    · exact le_refl 0
  -- ⑥ the numeric close: `x/4 ≤ x/(log x)^10 ≤ x/1024` at `x ≥ 8` — contradiction
  have hx8R : (8 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx8
  have hxposR : (0 : ℝ) < (x : ℝ) := by linarith
  have hlog2x : (2 : ℝ) ≤ Real.log x := by
    have h8 : Real.log (8 : ℝ) ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) hx8R
    have h83 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  have hpow10 : (1024 : ℝ) ≤ (Real.log x) ^ 10 := by
    calc (1024 : ℝ) = 2 ^ 10 := by norm_num
      _ ≤ (Real.log x) ^ 10 := pow_le_pow_left₀ (by norm_num) hlog2x 10
  have hfrac : (x : ℝ) / (Real.log x) ^ 10 ≤ (x : ℝ) / 1024 :=
    div_le_div_of_nonneg_left hxposR.le (by norm_num) hpow10
  -- `x/4 ≤ RHD ≤ RHD + RCE ≤ x/(log x)^10 ≤ x/1024` forces `x ≤ 0`
  linarith

end Salt.Chen
