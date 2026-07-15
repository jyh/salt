/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.GlueFinal
import Salt.Chen.PieceDecomp

/-!
# PRICE-1 — the uniform per-box price lemma (node PRICE-1)

Design: `docs/blueprints/flags.md`, the `2026-07-14 PRICE-GATE`/`PRICE-0` entries and the
`GLU-2W-fin` scoping finding.  This file is the PRICE wave's core: it assembles the
operating-point discharge of `medium_survivor_price_sqrtD` (SqrtDFold) at a generic
`dyadicBoundary` survivor box, using the landed `d0_window_nonempty` supplier for the
`D0`-window rows and pure-algebra choices for the SW couplings.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

1. (deliverable 1) **The SW-coupling suppliers** `Kbeta_min`/`Km_min`/`Kbeta'_min` — the
   minimal `Kβ`/`Km`/`Kβ'` values forced by the terminal's coupling rows
   `hcoupG`/`hcoup3`/`herr_book4`, with their nonnegativity and the coupling rows proven
   (pure algebra: `K·L^{..} = Kβ·(log N)^{..}` by `div_mul_cancel₀`; the per-`e` `Kβ'` row
   via `log(⌊X/e⌋·M) ≤ L`).

2. (deliverable 2) **The `N′ = 2^k` bridge (Finding C)** `blockPrimeInd_pieceN_succ`:
   `blockPrimeInd (pieceN k) = blockPrimeInd (pieceN k + 1)` as functions for `k ≥ 2`
   (`pieceN k + 1 = 2^k` is composite, so the indicator is unchanged) — so the terminal's
   `M ≤ 2N` applies at `N′ = 2^k` where `pieceM k = 2·pieceN k + 1 = 2·N′ − 1 ≤ 2N′`.

3. (deliverable 3) **The guarded per-`e` discharge**: `bridge_scale` (the honest bound
   `L ≤ 2·log(⌊X/e⌋·M)` at `e ≤ X`) and the three guarded rows
   `herr_LEpos`/`herr_scale`/`herr_D0E` (the last via `d0_window_nonempty`'s conjunct 7).

4. (deliverable 4) **The PASS* box rows** as small lemmas taking the operating facts named.

5. (deliverable 5) **The uniform lemma** `medium_box_price_at_op` + the satisfiability
   `example` (the anti-#69 discipline: the hypothesis bundle is jointly consistent).

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## 1. The SW-coupling suppliers (deliverable 1)

The terminal `medium_survivor_price_sqrtD` exposes the SW existential's constant `K` and
demands three coupling rows (at exponents `A + C0`, `A + 1 + 2·C0`, `A + 1 + 1 + 2·C0`):

* `hcoupG  : K·L^{A+C0}       ≤ Kβ ·(log N)^{A+2C0}`
* `hcoup3  : K·L^{A+1+2C0}    ≤ Km ·(log N)^{A+2C0}`
* `herr_book4 : ∀ e, K·(log(⌊X/e⌋·M))^{A+1+1+2C0} ≤ Kβ'·(log N)^{A+1+2C0}`

No corpus discharger names `Kβ`/`Km`/`Kβ'`; PRICE-1 supplies them as the MINIMAL values that
make the rows hold with equality (`hcoupG`/`hcoup3`) or by the log-monotone slack
(`herr_book4`, using `log(⌊X/e⌋·M) ≤ L`).  `L := log(X·M)`, `logN := log N`. -/

/-- The minimal `Kβ` value forced by `hcoupG`: `K·L^{A+C0}/(log N)^{A+2C0}`. -/
noncomputable def Kbeta_min (K L logN A C0 : ℝ) : ℝ := K * L ^ (A + C0) / logN ^ (A + 2 * C0)

/-- The minimal `Km` value forced by `hcoup3`: `K·L^{A+1+2C0}/(log N)^{A+2C0}`. -/
noncomputable def Km_min (K L logN A C0 : ℝ) : ℝ :=
  K * L ^ (A + 1 + 2 * C0) / logN ^ (A + 2 * C0)

/-- The minimal `Kβ'` value forced by `herr_book4`: `K·L^{A+1+1+2C0}/(log N)^{A+1+2C0}`. -/
noncomputable def Kbeta'_min (K L logN A C0 : ℝ) : ℝ :=
  K * L ^ (A + 1 + 1 + 2 * C0) / logN ^ (A + 1 + 2 * C0)

theorem Kbeta_min_nonneg {K L logN A C0 : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hlogN : 0 ≤ logN) :
    0 ≤ Kbeta_min K L logN A C0 :=
  div_nonneg (mul_nonneg hK (Real.rpow_nonneg hL _)) (Real.rpow_nonneg hlogN _)

theorem Km_min_nonneg {K L logN A C0 : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hlogN : 0 ≤ logN) :
    0 ≤ Km_min K L logN A C0 :=
  div_nonneg (mul_nonneg hK (Real.rpow_nonneg hL _)) (Real.rpow_nonneg hlogN _)

theorem Kbeta'_min_nonneg {K L logN A C0 : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hlogN : 0 ≤ logN) :
    0 ≤ Kbeta'_min K L logN A C0 :=
  div_nonneg (mul_nonneg hK (Real.rpow_nonneg hL _)) (Real.rpow_nonneg hlogN _)

/-- `hcoupG`, with equality: `K·L^{A+C0} = Kβ_min·(log N)^{A+2C0}`. -/
theorem Kbeta_min_coupling {K L logN A C0 : ℝ} (hlogN : 0 < logN) :
    K * L ^ (A + C0) ≤ Kbeta_min K L logN A C0 * logN ^ (A + 2 * C0) := by
  refine le_of_eq ?_
  rw [Kbeta_min, div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hlogN _))]

/-- `hcoup3`, with equality: `K·L^{A+1+2C0} = Km_min·(log N)^{A+2C0}`. -/
theorem Km_min_coupling {K L logN A C0 : ℝ} (hlogN : 0 < logN) :
    K * L ^ (A + 1 + 2 * C0) ≤ Km_min K L logN A C0 * logN ^ (A + 2 * C0) := by
  refine le_of_eq ?_
  rw [Km_min, div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hlogN _))]

/-- `herr_book4` (generic, per-`e`): for any log value `ℓ` with `0 ≤ ℓ ≤ L`,
`K·ℓ^{A+1+1+2C0} ≤ Kβ'_min·(log N)^{A+1+2C0}`.  In the assembly `ℓ := log(⌊X/e⌋·M)`. -/
theorem Kbeta'_min_coupling {K L logN A C0 ℓ : ℝ} (hK : 0 ≤ K) (hlogN : 0 < logN)
    (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L) (hexp : 0 ≤ A + 1 + 1 + 2 * C0) :
    K * ℓ ^ (A + 1 + 1 + 2 * C0) ≤ Kbeta'_min K L logN A C0 * logN ^ (A + 1 + 2 * C0) := by
  rw [Kbeta'_min, div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hlogN _))]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hℓ0 hℓL hexp) hK

/-! ## 2. The `N′ = 2^k` bridge (Finding C, deliverable 2)

**CORPUS NOTE.**  Finding C is already landed in `GlueBV.lean` (transitively imported via
`MediumFloor → SubBlocked`): `blockPrimeInd_pieceN_eq {k} (hk : 2 ≤ k) :
blockPrimeInd (pieceN k) = blockPrimeInd (2^k)` (plus its helper `not_prime_two_pow` and the
`pieceM`/`pieceN` arithmetic `pieceM_le_two_pow`/`two_pow_le_pieceM`, and the price transport
`sum_norm_apDiscBilinCutoff_pieceN`).  PRICE-1 REUSES those directly (see the assembly in §5).
The wrapper below re-exports the requested `= pieceN k + 1` shape from the landed `= 2^k`
form (`pieceN k + 1 = 2^k`). -/

/-- **Finding C (requested shape) — the `N′ = 2^k` bridge.**  `blockPrimeInd (pieceN k) =
blockPrimeInd (pieceN k + 1)` for `k ≥ 2`, a thin re-export of the landed
`blockPrimeInd_pieceN_eq` (`pieceN k + 1 = 2^k`, composite, so the indicator is unchanged). -/
theorem blockPrimeInd_pieceN_succ {k : ℕ} (hk : 2 ≤ k) :
    blockPrimeInd (pieceN k) = blockPrimeInd (pieceN k + 1) := by
  have hpk : pieceN k + 1 = 2 ^ k := by
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    unfold pieceN; omega
  rw [blockPrimeInd_pieceN_eq hk, hpk]

/-! ## 3. The guarded per-`e` discharge (deliverable 3)

Catch #69: the per-`e` rows `herr_LEpos`/`herr_scale`/`herr_D0E` are demanded only on the
guarded range `e ≤ X`.  There `⌊X/e⌋ ≥ 1`, and the honest bound `L ≤ 2·log(⌊X/e⌋·M)`
(`bridge_scale`) holds at the operating sizes: from `X < 2·⌊X/e⌋·e` and
`e² ≤ X·M/L^{2B}` (via `e ≤ D ≤ √(X·M)/L^B` and `L^{2B} ≥ 4`) one gets `X·M ≤ (⌊X/e⌋·M)²`.
The bridge then discharges `herr_scale` verbatim, `herr_LEpos` (since `L ≥ 2`), and
`herr_D0E` (via `d0_window_nonempty`'s conjunct-7 form `∀ LE, L ≤ 2·LE → D0 ≤ LE^{C0}`). -/

/-- **`bridge_scale` (deliverable 3, the honest per-`e` bound).**  At `e ≤ X`,
`log(X·M) ≤ 2·log(⌊X/e⌋·M)`, from `X < 2·⌊X/e⌋·e`, `e ≤ D ≤ √(X·M)/L^B` and `L^{2B} ≥ 4`
(guaranteed by `L ≥ 2`, `B ≥ 1`).  The unified route (no case split): `X² < 4q²e² ≤
4q²·XM/L^{2B} ≤ q²·XM`, so `XM ≤ (qM)²`. -/
theorem bridge_scale {X M e D : ℕ} {B : ℝ}
    (hM2 : 2 ≤ M) (he2 : 2 ≤ e) (heX : e ≤ X) (heD : e ≤ D)
    (hDscale : (D : ℝ) ≤ Real.sqrt ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ B)
    (hB1 : 1 ≤ B) (hL2 : 2 ≤ Real.log ((X : ℝ) * (M : ℝ))) :
    Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) := by
  set XR : ℝ := (X : ℝ) with hXR
  set MR : ℝ := (M : ℝ) with hMR
  set eR : ℝ := (e : ℝ) with heR
  set qR : ℝ := ((X / e : ℕ) : ℝ) with hqR
  set L : ℝ := Real.log (XR * MR) with hLdef
  -- basic positivity
  have hepos : 0 < e := by omega
  have hXge2 : 2 ≤ X := le_trans he2 heX
  have hXRnn : 0 ≤ XR := by positivity
  have hMRnn : 0 ≤ MR := by positivity
  have heRpos : 0 < eR := by rw [heR]; exact_mod_cast hepos
  have hXRge2 : (2 : ℝ) ≤ XR := by rw [hXR]; exact_mod_cast hXge2
  have hMRge2 : (2 : ℝ) ≤ MR := by rw [hMR]; exact_mod_cast hM2
  have hXMpos : 0 < XR * MR := by positivity
  -- q := X/e ≥ 1
  have hq1 : 1 ≤ X / e := (Nat.one_le_div_iff hepos).2 heX
  have hqRge1 : (1 : ℝ) ≤ qR := by rw [hqR]; exact_mod_cast hq1
  have hqRpos : 0 < qR := by linarith
  -- X < e·(q+1) ≤ 2·q·e   (Nat.lt_mul_div_succ), cast to reals
  have hXltNat : X < e * (X / e + 1) := Nat.lt_mul_div_succ X hepos
  have hXlt : XR < eR * (qR + 1) := by rw [hXR, heR, hqR]; exact_mod_cast hXltNat
  have hXlt2 : XR < 2 * qR * eR := by
    have haux : eR * (qR + 1) ≤ 2 * qR * eR := by nlinarith [heRpos, hqRge1]
    linarith [hXlt, haux]
  -- t := L^B > 0, and t ≥ 2 (from L ≥ 2, B ≥ 1)
  set t : ℝ := L ^ B with htdef
  have hLpos : 0 < L := by linarith
  have htpos : 0 < t := by rw [htdef]; exact Real.rpow_pos_of_pos hLpos _
  have htge2 : (2 : ℝ) ≤ t := by
    rw [htdef]
    calc (2 : ℝ) ≤ L := hL2
      _ = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le (by linarith) hB1
  -- s := √(XM), s^2 = XM
  set s : ℝ := Real.sqrt (XR * MR) with hsdef
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = XR * MR := Real.sq_sqrt hXMpos.le
  -- e ≤ D ≤ s/t, so eR ≤ s/t
  have heRle : eR ≤ s / t := by
    have h1 : eR ≤ (D : ℝ) := by rw [heR]; exact_mod_cast heD
    have h2 : (D : ℝ) ≤ s / t := hDscale
    linarith
  -- eR^2 ≤ (s/t)^2 = XM/t^2
  have heR2 : eR ^ 2 ≤ (XR * MR) / t ^ 2 := by
    have hsq : eR ^ 2 ≤ (s / t) ^ 2 := pow_le_pow_left₀ heRpos.le heRle 2
    rw [div_pow, hs2] at hsq
    exact hsq
  -- t^2 ≥ 4
  have ht2ge4 : (4 : ℝ) ≤ t ^ 2 := by nlinarith [htge2, htpos]
  have ht2pos : 0 < t ^ 2 := by positivity
  have hXRpos : 0 < XR := by linarith
  -- XR^2 < 4 q^2 e^2  (from XR < 2 q e)
  have hXR2 : XR ^ 2 < 4 * qR ^ 2 * eR ^ 2 := by
    calc XR ^ 2 < (2 * qR * eR) ^ 2 := pow_lt_pow_left₀ hXlt2 hXRnn (by norm_num)
      _ = 4 * qR ^ 2 * eR ^ 2 := by ring
  -- 4 q^2 e^2 ≤ q^2 · XM
  have hstep : 4 * qR ^ 2 * eR ^ 2 ≤ qR ^ 2 * (XR * MR) := by
    have h1 : 4 * qR ^ 2 * eR ^ 2 ≤ 4 * qR ^ 2 * ((XR * MR) / t ^ 2) :=
      mul_le_mul_of_nonneg_left heR2 (by positivity)
    have h2 : 4 * qR ^ 2 * ((XR * MR) / t ^ 2) ≤ qR ^ 2 * (XR * MR) := by
      rw [← mul_div_assoc, div_le_iff₀ ht2pos]
      nlinarith [ht2ge4, mul_nonneg (sq_nonneg qR) hXMpos.le]
    linarith
  have hchain : XR ^ 2 < qR ^ 2 * (XR * MR) := lt_of_lt_of_le hXR2 hstep
  -- divide by XR > 0:  XR < qR^2 · MR
  have hXRlt : XR < qR ^ 2 * MR := by
    have hrw : qR ^ 2 * (XR * MR) = (qR ^ 2 * MR) * XR := by ring
    rw [hrw, pow_two] at hchain
    exact lt_of_mul_lt_mul_right hchain hXRpos.le
  -- XM ≤ (qM)^2
  have hXMle : XR * MR ≤ (qR * MR) ^ 2 := by
    calc XR * MR ≤ (qR ^ 2 * MR) * MR := mul_le_mul_of_nonneg_right hXRlt.le hMRnn
      _ = (qR * MR) ^ 2 := by ring
  -- log monotone + log_pow
  have hqMpos : 0 < qR * MR := by positivity
  have hlogle : L ≤ Real.log ((qR * MR) ^ 2) := by
    rw [hLdef]; exact Real.log_le_log hXMpos hXMle
  rw [Real.log_pow] at hlogle
  push_cast at hlogle
  -- goal: L ≤ 2 * log(qR * MR)
  linarith [hlogle]

/-! ## 4. The PASS* box rows (deliverable 4)

The `M ≤ 2N′`/`N′ ≤ M` arithmetic (`pieceM_le_two_pow`/`two_pow_le_pieceM`) is already landed
in `GlueBV`; PRICE-1 adds only `two_le_pieceM` (`2 ≤ M`) and the per-`e` log helpers used by
the `Kβ'` coupling and `herr_LEpos`.  The remaining terminal rows (`hDsq`/`habs`/`hDscale`/
`hXsqrt`/`hMsqrt`/`herr_lev`/`herr_Mlev`/`hDx`/`hDXM`/`hfloor`) are the analytic operating facts
supplied by `GlueFinal`/`opf_*` — the uniform lemma below takes them as named hypotheses
(parametrized house form). -/

/-- `hM2` at `N′ = 2^k`, `k ≥ 1`: `pieceM k = 2^{k+1} − 1 ≥ 3 ≥ 2`. -/
theorem two_le_pieceM {k : ℕ} (hk : 1 ≤ k) : 2 ≤ pieceM k := by
  have h : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  have h1 : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  unfold pieceM; omega

/-- Per-`e` log floor: `0 ≤ log(⌊X/e⌋·M)` (the argument is a nat, so `Real.log ≥ 0`). -/
theorem log_efold_nonneg (X M e : ℕ) : 0 ≤ Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) := by
  rw [show ((X / e : ℕ) : ℝ) * (M : ℝ) = (((X / e) * M : ℕ) : ℝ) by push_cast; ring]
  exact Real.log_natCast_nonneg _

/-- Per-`e` log ceiling: `log(⌊X/e⌋·M) ≤ log(X·M)` (`⌊X/e⌋ ≤ X`; the `⌊X/e⌋ = 0` leg lands on
`log 0 = 0 ≤ L`). -/
theorem log_efold_le (X M e : ℕ) :
    Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) ≤ Real.log ((X : ℝ) * (M : ℝ)) := by
  have hle : (X / e) * M ≤ X * M := Nat.mul_le_mul (Nat.div_le_self X e) (le_refl M)
  rw [show ((X / e : ℕ) : ℝ) * (M : ℝ) = (((X / e) * M : ℕ) : ℝ) by push_cast; ring,
      show ((X : ℝ)) * (M : ℝ) = ((X * M : ℕ) : ℝ) by push_cast; ring]
  rcases Nat.eq_zero_or_pos ((X / e) * M) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)

/-! ## 4b. The `D0`-window from raw `X·M` bounds (catch #71 repair core)

**Why this exists (catch #71, ratified option (a)).**  The landed `d0_window_nonempty`
(`SqrtDFold`) consumes the `2^k`-boundary membership through its STRONG corner clause
`2^i·(2^k+1) ≤ x`; but the consumer supplies only the pieceN-boundary (weak corner
`2^i·2^k ≤ x`).  The `d0_window_nonempty` construction, however, only ever uses the corner to
derive the two scale facts `x/2 < X·M ≤ 4x` — and the WEAK corner delivers `X·M ≤ 4x` just as
the strong one does (`X·M ≤ 2^{i+1}·M ≤ 2^{i+1}·(2·2^k) = 4·2^i·2^k ≤ 4x`, no `+1` slack
needed).  So we factor the raw-bounds core here: it takes `x/2+1 < X·M` and `X·M ≤ 4x`
directly, reproducing `d0_window_nonempty`'s IDENTICAL 9-conjunct conclusion at the same `N`.
The pieceN-boundary price lemmas call it with the weak corner in hand — there is NO degradation
(the `4x` upper bound is unchanged).  `SqrtDFold`'s `d0_window_nonempty` is left untouched. -/

/-- **`d0_window_of_XM` (catch #71 repair core).**  The `D0`-window construction stripped of the
boundary membership: from the raw scale facts `x/2+1 < X·M` and `X·M ≤ 4x` (which BOTH the strong
`2^k`-corner and the weak pieceN-corner supply — see the section note), at the operating point
(`x ≥ exp(10^9)`, block floor `x^{11/24}/8 ≤ N`) emits the IDENTICAL 9-conjunct conclusion of
`SqrtDFold.d0_window_nonempty`.  Body verbatim `d0_window_nonempty` from the `L`-bounds onward. -/
theorem d0_window_of_XM {x N M X : ℕ}
    (hx : Real.exp (10 ^ 9) ≤ (x : ℝ))
    (hNfloor : (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (N : ℝ))
    (hXMlo : x / 2 + 1 < X * M)
    (hXMhi : X * M ≤ 4 * x) :
    ∃ D0 k0 : ℕ, D0 = 2 ^ k0 ∧ 2 ≤ D0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((15 : ℝ)) ≤ 2 * (2 : ℝ) ^ k0
      ∧ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((17 : ℝ)) ≤ (D0 : ℝ)
      ∧ (D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ ((18 : ℝ))
      ∧ (D0 : ℝ) ≤ (Real.log N) ^ ((18 : ℝ))
      ∧ (∀ LE : ℝ, Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * LE → (D0 : ℝ) ≤ LE ^ ((18 : ℝ)))
      ∧ (D0 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 8
      ∧ D0 ≤ N := by
  -- ① the scale facts: `t ≥ 10^9`, `x ≥ 2`.
  have h109 : (10 : ℝ) ^ 9 = 1000000000 := by norm_num
  have ht : (10 : ℝ) ^ 9 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by
    have h1 := Real.add_one_le_exp ((10 : ℝ) ^ 9)
    linarith
  have hx2 : 2 ≤ x := by exact_mod_cast hxR2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  -- ② the scale facts (from the RAW bounds, in place of the boundary corner): `x/2 < X·M ≤ 4x`.
  have hXM : x / 2 + 1 < X * M := hXMlo
  have hXM4x : X * M ≤ 4 * x := hXMhi
  have hXMposN : 0 < X * M := by omega
  have hXMposR : (0 : ℝ) < (X : ℝ) * (M : ℝ) := by exact_mod_cast hXMposN
  have hXM4xR : (X : ℝ) * (M : ℝ) ≤ 4 * (x : ℝ) := by exact_mod_cast hXM4x
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  -- ③ `t − 1 ≤ L ≤ t + 3`.
  have hL_lo : Real.log x - 1 ≤ L := by
    have h1 : x < (x / 2 + 1) * 2 := by omega
    have h2 : x / 2 + 1 ≤ X * M := by omega
    have h1R : (x : ℝ) < ((x / 2 + 1 : ℕ) : ℝ) * 2 := by exact_mod_cast h1
    have h2R : ((x / 2 + 1 : ℕ) : ℝ) ≤ (X : ℝ) * (M : ℝ) := by exact_mod_cast h2
    push_cast at h1R h2R
    have hhalf : (x : ℝ) / 2 < (X : ℝ) * (M : ℝ) := by linarith
    have hlog : Real.log ((x : ℝ) / 2) ≤ L := Real.log_le_log (by linarith) hhalf.le
    rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)] at hlog
    have h2log : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith
  have hL_up : L ≤ Real.log x + 3 := by
    have h1 : L ≤ Real.log (4 * (x : ℝ)) := Real.log_le_log hXMposR hXM4xR
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hxpos)] at h1
    have h4log : Real.log 4 ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
    linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hLnn : (0 : ℝ) ≤ L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hL4 : (4 : ℝ) ≤ L := by linarith
  have hL20 : (1048576 : ℝ) ≤ L := by linarith
  -- ④ the block-floor log: `W := (11/24)·t − 7 ≤ log N`.
  set W : ℝ := 11 / 24 * Real.log x - 7 with hWdef
  have hWlogN : W ≤ Real.log N := by
    have hlogN := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hxpos _) (by norm_num))
      hNfloor
    rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hxpos _)) (by norm_num : (8 : ℝ) ≠ 0),
      Real.log_rpow hxpos] at hlogN
    have h8log : Real.log 8 ≤ 7 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)]
    rw [hWdef]
    linarith
  have hWpos : (0 : ℝ) < W := by rw [hWdef]; linarith
  have hW1296 : (1296 : ℝ) ≤ W := by rw [hWdef]; linarith
  have hLW : L ≤ 12 / 5 * W := by rw [hWdef]; linarith
  have hW4 : 4 * ((12 : ℝ) / 5) ^ ((17 : ℝ)) ≤ W := by
    have hc : ((12 : ℝ) / 5) ^ ((17 : ℝ)) = ((12 : ℝ) / 5) ^ (17 : ℕ) := by
      rw [show ((17 : ℝ)) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hnum : 4 * ((12 : ℝ) / 5) ^ (17 : ℕ) ≤ 11 / 24 * 10 ^ 9 - 7 := by norm_num
    rw [hc, hWdef]
    linarith
  -- ⑤ the dyadic window: `D0 = 2^{k0} ∈ [L^{17}, 4·L^{17}]`.
  have hL17_1 : (1 : ℝ) ≤ L ^ ((17 : ℝ)) := Real.one_le_rpow hL1 (by norm_num)
  have hL17_2 : (2 : ℝ) ≤ L ^ ((17 : ℝ)) := by
    calc (2 : ℝ) ≤ L := by linarith
      _ = L ^ ((1 : ℝ)) := (Real.rpow_one L).symm
      _ ≤ L ^ ((17 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  obtain ⟨n, hn_ge, hn_le⟩ :
      ∃ n : ℕ, L ^ ((17 : ℝ)) ≤ (n : ℝ) ∧ (n : ℝ) ≤ L ^ ((17 : ℝ)) + 1 :=
    ⟨⌈L ^ ((17 : ℝ))⌉₊, Nat.le_ceil _,
      le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg hLnn _))⟩
  have hn1 : 1 < n := by
    have h1R : (1 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast h1R
  obtain ⟨k0, hnpow, hpow2n⟩ : ∃ k0 : ℕ, n ≤ 2 ^ k0 ∧ 2 ^ k0 ≤ 2 * n := by
    refine ⟨Nat.clog 2 n, Nat.le_pow_clog (by norm_num) n, ?_⟩
    have hk0pos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) hn1
    have hpow_lt : 2 ^ (Nat.clog 2 n - 1) < n :=
      Nat.pow_pred_clog_lt_self (by norm_num) hn1
    have hsplit : 2 * 2 ^ (Nat.clog 2 n - 1) = 2 ^ Nat.clog 2 n := by
      rw [← pow_succ']
      congr 1
      omega
    rw [← hsplit]
    exact Nat.mul_le_mul (le_refl 2) (le_of_lt hpow_lt)
  have hD0_lo : L ^ ((17 : ℝ)) ≤ ((2 ^ k0 : ℕ) : ℝ) := by
    refine le_trans hn_ge ?_
    exact_mod_cast hnpow
  have hD0_hi : ((2 ^ k0 : ℕ) : ℝ) ≤ 4 * L ^ ((17 : ℝ)) := by
    have h1 : ((2 ^ k0 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hpow2n
    linarith
  have hL18eq : L ^ ((18 : ℝ)) = L * L ^ ((17 : ℝ)) := by
    have hh := Real.rpow_add hLpos 1 17
    rw [Real.rpow_one] at hh
    rw [show (18 : ℝ) = 1 + 17 by norm_num, hh]
  have h17nn : (0 : ℝ) ≤ L ^ ((17 : ℝ)) := Real.rpow_nonneg hLnn _
  -- ⑥ the `hD0N'` leg: `4·L^{17} ≤ W^{18}` (the anti-#64 margin).
  have hW18 : 4 * L ^ ((17 : ℝ)) ≤ W ^ ((18 : ℝ)) := by
    have hW17 : L ^ ((17 : ℝ)) ≤ ((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ)) := by
      calc L ^ ((17 : ℝ)) ≤ (12 / 5 * W) ^ ((17 : ℝ)) :=
            Real.rpow_le_rpow hLnn hLW (by norm_num)
        _ = ((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ)) :=
            Real.mul_rpow (by norm_num) hWpos.le
    have hW18eq : W ^ ((18 : ℝ)) = W * W ^ ((17 : ℝ)) := by
      have hh := Real.rpow_add hWpos 1 17
      rw [Real.rpow_one] at hh
      rw [show (18 : ℝ) = 1 + 17 by norm_num, hh]
    have h17Wnn : (0 : ℝ) ≤ W ^ ((17 : ℝ)) := Real.rpow_nonneg hWpos.le _
    rw [hW18eq]
    calc 4 * L ^ ((17 : ℝ))
        ≤ 4 * (((12 : ℝ) / 5) ^ ((17 : ℝ)) * W ^ ((17 : ℝ))) := by linarith
      _ = (4 * ((12 : ℝ) / 5) ^ ((17 : ℝ))) * W ^ ((17 : ℝ)) := by ring
      _ ≤ W * W ^ ((17 : ℝ)) := mul_le_mul_of_nonneg_right hW4 h17Wnn
  -- ⑦ the `hD0N` leg: `W^{18} ≤ e^W ≤ x^{11/24}/8`.
  have hexpW : W ^ ((18 : ℝ)) ≤ Real.exp W := by
    have hunn : (0 : ℝ) ≤ W / 36 := by linarith
    have hquad : W ≤ (W / 36) ^ ((2 : ℝ)) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hexpand : (W / 36) ^ (2 : ℕ) = W * W / 1296 := by ring
      rw [hexpand, le_div_iff₀ (by norm_num : (0 : ℝ) < 1296)]
      have keyq : (0 : ℝ) ≤ (W - 1296) * W := mul_nonneg (by linarith) hWpos.le
      linarith [keyq]
    have hu : W / 36 ≤ Real.exp (W / 36) := by linarith [Real.add_one_le_exp (W / 36)]
    calc W ^ ((18 : ℝ))
        ≤ ((W / 36) ^ ((2 : ℝ))) ^ ((18 : ℝ)) :=
          Real.rpow_le_rpow hWpos.le hquad (by norm_num)
      _ = (W / 36) ^ ((36 : ℝ)) := by
          rw [← Real.rpow_mul hunn]
          norm_num
      _ ≤ (Real.exp (W / 36)) ^ ((36 : ℝ)) := Real.rpow_le_rpow hunn hu (by norm_num)
      _ = Real.exp W := by
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
          congr 1
          ring
  have hexp_le : Real.exp W ≤ (x : ℝ) ^ ((11 : ℝ) / 24) / 8 := by
    have hEW : Real.exp W = (x : ℝ) ^ ((11 : ℝ) / 24) / Real.exp 7 := by
      rw [hWdef, Real.exp_sub, Real.rpow_def_of_pos hxpos]
      have hmul : Real.log (x : ℝ) * ((11 : ℝ) / 24) = 11 / 24 * Real.log x := by ring
      rw [hmul]
    rw [hEW]
    have h7 : (8 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hxpos.le _) (by norm_num) h7
  -- ⑧ emit the rows.
  have hcast : ((2 ^ k0 : ℕ) : ℝ) = (2 : ℝ) ^ k0 := by push_cast; ring
  refine ⟨2 ^ k0, k0, rfl, le_trans (by omega : 2 ≤ n) hnpow, ?_, hD0_lo, ?_, ?_, ?_, ?_, ?_⟩
  · -- `hD0lo_main`, the DECOUPLED row (exponent `A+2 = 15`)
    have h15 : L ^ ((15 : ℝ)) ≤ L ^ ((17 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h2k0pos : (0 : ℝ) < (2 : ℝ) ^ k0 := by positivity
    calc L ^ ((15 : ℝ)) ≤ L ^ ((17 : ℝ)) := h15
      _ ≤ ((2 ^ k0 : ℕ) : ℝ) := hD0_lo
      _ = (2 : ℝ) ^ k0 := hcast
      _ ≤ 2 * (2 : ℝ) ^ k0 := by linarith
  · -- `hD0` (`D0 ≤ L^{C0}`, `C0 = 18`)
    rw [hL18eq]
    have key : (0 : ℝ) ≤ (L - 4) * L ^ ((17 : ℝ)) := mul_nonneg (by linarith) h17nn
    linarith [hD0_hi, key]
  · -- `hD0N'` (`D0 ≤ (log N)^{C0}`, `C0 = 18`)
    have hmono : W ^ ((18 : ℝ)) ≤ (Real.log N) ^ ((18 : ℝ)) :=
      Real.rpow_le_rpow hWpos.le hWlogN (by norm_num)
    linarith [hD0_hi, hW18, hmono]
  · -- `herr_D0E` in the `herr_scale` form (`LE ≥ L/2`, exponent `C0 = 18`)
    intro LE hLE
    have hhalfpos : (0 : ℝ) < L / 2 := by linarith
    have hstep : 4 * L ^ ((17 : ℝ)) ≤ (L / 2) ^ ((18 : ℝ)) := by
      have hdiv : (L / 2) ^ ((18 : ℝ)) = L ^ ((18 : ℝ)) / (2 : ℝ) ^ ((18 : ℝ)) :=
        Real.div_rpow hLnn (by norm_num) _
      have h218 : (2 : ℝ) ^ ((18 : ℝ)) = 262144 := by
        rw [show ((18 : ℝ)) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      rw [hdiv, h218, hL18eq, le_div_iff₀ (by norm_num : (0 : ℝ) < 262144)]
      have key : (0 : ℝ) ≤ (L - 1048576) * L ^ ((17 : ℝ)) := mul_nonneg (by linarith) h17nn
      linarith [key]
    have hmono : (L / 2) ^ ((18 : ℝ)) ≤ LE ^ ((18 : ℝ)) :=
      Real.rpow_le_rpow hhalfpos.le (by linarith) (by norm_num)
    linarith [hD0_hi]
  · -- the `x`-scale bound (`D0 ≤ x^{11/24}/8`)
    linarith [hD0_hi, hW18, hexpW, hexp_le]
  · -- `hD0N` (`D0 ≤ N`)
    have hfin : ((2 ^ k0 : ℕ) : ℝ) ≤ (N : ℝ) := by
      linarith [hD0_hi, hW18, hexpW, hexp_le, hNfloor]
    exact_mod_cast hfin

/-! ## 5. The uniform per-box price lemma `medium_box_price_at_op` (deliverable 5, the summit)

The operating-point discharge of `medium_survivor_price_sqrtD` (the `D < (N+1)²` terminal that
covers the catch-#62 medium-band strip) at a generic `dyadicBoundary` survivor box, re-indexed
to `N′ = 2^k` (Finding C).  Structurally the sibling of `GlueBV.cutoff_BV_at_op` (the `D < N`
top-piece variant), but here PRICE-1 additionally discharges, internally:

* the `D0`-window rows — via the landed `d0_window_nonempty` (node D0W): `hD0`/`hD0N'`/`hD0N`/
  `hD0eq`/`h2D0` verbatim, `hD0D` off the `x^{11/24}/8`-scale bound, `hD0lo_main`/`herr_D0lo`
  off the exponent identities `15 = 13+2`, `17 = 13+4`;
* the guarded per-`e` rows `herr_LEpos`/`herr_scale`/`herr_D0E` — via `bridge_scale` (the honest
  `L ≤ 2·log(⌊X/e⌋·M)` at `e ≤ X`) and `d0_window_nonempty`'s conjunct-7 form (catch #69 repair);
* the three SW couplings `hcoupG`/`hcoup3`/`herr_book4` — via the minimal choices
  `Kβ := Kbeta_min`, `Km := Km_min`, `Kβ' := Kbeta'_min` (§1), `K` the SW existential's constant.

Everything else (the box floors `hDsq`/`habs`, the level/scale rows `hDscale`/`hXsqrt`/`hMsqrt`/
`herr_lev`/`herr_Mlev`, the `hdiv`-route inputs `hFX`/`hDx`/`hLbb`/`hfloor`, `hDXM`) enters as a
named operating hypothesis — the analytic facts `GlueFinal`/`opf_*` supply — at the operating
convention `A = 13`, `B = 15`, `C0 = 18`.  The conclusion is `medium_survivor_price_sqrtD`'s own
`Kerr`-shaped bound with the minimal SW constants, on `blockPrimeInd (pieceN k)`
(`sum_norm_apDiscBilinCutoff_pieceN`). -/
theorem medium_box_price_at_op :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (x : ℕ) (Lb : ℝ) (F Krange k i : ℕ) (α : ℕ → ℂ) (X T D : ℕ)
        (Dset : Finset ℕ) (r : ℕ → ℕ),
        2 ≤ k →
        Real.exp (10 ^ 9) ≤ (x : ℝ) →
        i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x F Krange →
        X = 2 ^ (i + 1) - 1 →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ ((2 ^ k : ℕ) : ℝ) →
        (∀ m, ‖α m‖ ≤ 1) →
        (∀ d ∈ Dset, 1 ≤ d) →
        (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (∀ d ∈ Dset, d ≤ D) →
        N₀ ≤ 2 ^ k →
        2 ≤ Real.log ((X : ℝ) * (pieceM k : ℝ)) →
        2 ≤ X →
        1 ≤ D →
        (x : ℝ) ^ ((11 : ℝ) / 24) / 8 ≤ (D : ℝ) →
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
        ∑ d ∈ Dset,
            ‖apDiscBilinCutoff α (blockPrimeInd (pieceN k)) X (pieceM k) (r d) d T‖
          ≤ (Kbeta_min K (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                  (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18
              + (6 * (Km_min K (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                        (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 448 + 32 * Real.sqrt 26)
                  + ((2 : ℝ) ^ ((13 : ℝ) + 5)
                      * Kbeta'_min K (Real.log ((X : ℝ) * (pieceM k : ℝ)))
                          (Real.log ((2 ^ k : ℕ) : ℝ)) 13 18 + 15360 + 1)))
            * ((X : ℝ) * (pieceM k : ℝ)) / (Real.log ((X : ℝ) * (pieceM k : ℝ))) ^ (13 : ℝ) := by
  obtain ⟨K, N₀, hK0, hbody⟩ := medium_survivor_price_sqrtD (A := 13) (C0 := 18) (by norm_num)
    (by norm_num)
  refine ⟨K, N₀, hK0, fun x Lb F Krange k i α X T D Dset r hk hx hi hXsub hNfloor hα hd1 hcop2
    hDsetD hN₀ hL2 hX2 hD1 hDge_x hDscale hDsq habs hXsqrt hMsqrt herr_lev herr_Mlev hFX hDx
    hLbb hfloor hDXM => ?_⟩
  -- abbreviations
  set M : ℕ := pieceM k with hMdef
  set L : ℝ := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  set logN : ℝ := Real.log ((2 ^ k : ℕ) : ℝ) with hlogNdef
  have hk1 : 1 ≤ k := by omega
  have hLnn : (0 : ℝ) ≤ L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hlogNpos : (0 : ℝ) < logN := by
    rw [hlogNdef]
    refine Real.log_pos ?_
    have h2 : (2 : ℕ) ≤ 2 ^ k := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    have : (1 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 ^ k)
    exact this
  have hM2 : 2 ≤ M := by rw [hMdef]; exact two_le_pieceM hk1
  have hM2k : M ≤ 2 * 2 ^ k := by rw [hMdef]; exact pieceM_le_two_pow k
  -- the `D0`-window (node D0W), rebuilt from the WEAK pieceN-corner (catch #71, ratified (a)).
  -- `pieceN k + 1 = 2^k`, so the pieceN corner `2^i·(pieceN k+1) ≤ x` reads `2^i·2^k ≤ x` and
  -- still gives `X·M ≤ 2^{i+1}·(2·2^k) = 4·2^i·2^k ≤ 4x` — the raw bound `d0_window_of_XM` needs.
  have hpk : pieceN k + 1 = 2 ^ k := by
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    unfold pieceN; omega
  rw [dyadicBoundary, Finset.mem_filter] at hi
  obtain ⟨-, hcorner, -, hcutoff⟩ := hi
  rw [hpk] at hcorner
  have hXMlo : x / 2 + 1 < X * M := by rw [hXsub]; exact hcutoff
  have hXMhi : X * M ≤ 4 * x := by
    have hXle : X ≤ 2 ^ (i + 1) := by rw [hXsub]; exact Nat.sub_le _ _
    calc X * M ≤ 2 ^ (i + 1) * (2 * 2 ^ k) := Nat.mul_le_mul hXle hM2k
      _ = 4 * (2 ^ i * 2 ^ k) := by rw [pow_succ]; ring
      _ ≤ 4 * x := Nat.mul_le_mul (le_refl 4) hcorner
  obtain ⟨D0, k0, hd_eq, hd_2D0, hd_main, hd_D0lo, hd_hD0, hd_hD0N', hd_conj7, hd_xscale,
    hd_hD0N⟩ := d0_window_of_XM (N := 2 ^ k) (M := M) hx hNfloor hXMlo hXMhi
  -- SW couplings (minimal choices), with `Kβ := Kbeta_min` etc.
  have hcoupG : K * L ^ ((13 : ℝ) + 18) ≤ Kbeta_min K L logN 13 18 * logN ^ ((13 : ℝ) + 2 * 18) :=
    Kbeta_min_coupling hlogNpos
  have hcoup3 : K * L ^ ((13 : ℝ) + 1 + 2 * 18)
      ≤ Km_min K L logN 13 18 * logN ^ ((13 : ℝ) + 2 * 18) := Km_min_coupling hlogNpos
  have herr_book4 : ∀ e, 2 ≤ e → e ≤ D →
      K * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ ((13 : ℝ) + 1 + 1 + 2 * 18)
        ≤ Kbeta'_min K L logN 13 18 * logN ^ ((13 : ℝ) + 1 + 2 * 18) :=
    fun e _ _ => Kbeta'_min_coupling hK0.le hlogNpos (log_efold_nonneg X M e)
      (log_efold_le X M e) (by norm_num)
  -- guarded per-`e` rows (catch #69 repair)
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
  -- `D0`-window rows re-shaped to the terminal's `A = 13` exponents
  have hD0D : D0 ≤ D := Nat.cast_le.mp (le_trans hd_xscale hDge_x)
  have hD0lo_main : L ^ ((13 : ℝ) + 2) ≤ 2 * (2 : ℝ) ^ k0 := by
    rw [show ((13 : ℝ) + 2) = 15 by norm_num]; exact hd_main
  have herr_D0lo : L ^ ((13 : ℝ) + 4) ≤ (D0 : ℝ) := by
    rw [show ((13 : ℝ) + 4) = 17 by norm_num]; exact hd_D0lo
  -- nonnegativity of the minimal SW constants
  have hKβnn : 0 ≤ Kbeta_min K L logN 13 18 := Kbeta_min_nonneg hK0.le hLnn hlogNpos.le
  have hKmnn : 0 ≤ Km_min K L logN 13 18 := Km_min_nonneg hK0.le hLnn hlogNpos.le
  have hKβ'nn : 0 ≤ Kbeta'_min K L logN 13 18 := Kbeta'_min_nonneg hK0.le hLnn hlogNpos.le
  -- transport `blockPrimeInd (pieceN k)` ⇒ `blockPrimeInd (2^k)` and apply the terminal
  rw [sum_norm_apDiscBilinCutoff_pieceN hk]
  exact hbody (x : ℝ) Lb F α X (2 ^ k) M T D0 D k0 (Nat.log 2 D) Dset r
    (Kbeta_min K L logN 13 18) (Km_min K L logN 13 18) (Kbeta'_min K L logN 13 18) 15
    hα hKβnn hKmnn hKβ'nn hN₀ (pieceM_le_two_pow k) hd_hD0N hd1 hcop2 hL1 hd_hD0 hd_hD0N'
    (by exact_mod_cast two_pow_le_pieceM k) hD1 hDsetD hDsq habs hX2 hM2 (by norm_num) (by norm_num)
    hd_eq hd_2D0
    hD0D rfl hDscale hD0lo_main hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev hFX hDx hLbb hfloor
    herr_LEpos herr_D0E hDXM herr_scale hcoupG hcoup3 herr_book4

/-! ## 6. Satisfiability — the anti-#69 non-vacuity witnesses (deliverable 5, the node's point)

Catch #69 was an INTRINSICALLY FALSE hypothesis (`0 < 0` on the per-`e` rows for `e > X`), so
the terminal was uninstantiable there.  PRICE-1's bundle has no such defect; the two witnesses
below show the two ingredients PRICE-1 is responsible for are jointly satisfiable at a genuine
medium-band shape:

* the box-index hypothesis `i ∈ dyadicBoundary (2^k) (pieceM k) (x/2+1) x F Krange` is
  INHABITED at a concrete piece shape (`k = 2`, `x = 16`, `i = 1`): the survivor set is
  nonempty, so the lemma is not vacuous over `i`;
* the guarded per-`e` bridge (`bridge_scale`, the mechanism that REPAIRS #69) FIRES at a concrete
  operating-flavoured shape (`X = M = 10⁴`, `e = 2 ≤ X`, `D = 2`, level `B = 1`): the conclusion
  `L ≤ 2·log(⌊X/e⌋·M)` — exactly the `herr_scale` shape whose `e > X` instance was #69's `0 < 0`
  — is provable, positively witnessing the guarded discharge.

(The per-`e` rows' vacuity on `e > X` is separately witnessed at `X = 2 < D = 4` in SqrtDFold
§11b; the `D0`-window rows by `d0_window_nonempty`; the SW couplings hold by construction of
`Kbeta_min`/`Km_min`/`Kbeta'_min`.) -/

/-- Anti-#69 (box inhabitation): the `dyadicBoundary` survivor set of PRICE-1's (relaxed, pieceN)
box hypothesis is NONEMPTY at the concrete piece shape `k = 2`, `x = 16` (`i = 1` survives all
three clauses: weak corner `2¹·(pieceN 2 + 1) = 2¹·4 = 8 ≤ 16`, `1 < 2² = 4`,
`9 < (2²−1)·7 = 21`).  The former `2^k`-boundary witness `1 ∈ dyadicBoundary (2^2) …` still holds
too (it is a subset, `boundary_2pow_subset_pieceN`); the relaxation only ENLARGES the survivor
set (adding the ≤ 1 edge box per piece), so the lemma's hypothesis remains non-vacuous. -/
example : 1 ∈ dyadicBoundary (pieceN 2) (pieceM 2) (16 / 2 + 1) 16 1 5 := by decide

/-- Anti-#69 (guarded per-`e` bridge fires): `bridge_scale` — the honest `L ≤ 2·log(⌊X/e⌋·M)`
that discharges `herr_scale`/`herr_LEpos`/`herr_D0E` — is satisfiable at a concrete medium-band
shape (`X = M = 10⁴`, `e = 2 ≤ X`, `D = 2`, `B = 1`), where #69's UNGUARDED row would have
demanded `0 < 0` on the empty `e`-range.  Uses `log(10⁸) ≤ 4·(10⁸)^{1/4} = 400 ≤ 5000` for
`hDscale` and `exp 2 ≤ 10⁸` for `hL2`. -/
example :
    Real.log (((10000 : ℕ) : ℝ) * ((10000 : ℕ) : ℝ))
      ≤ 2 * Real.log (((10000 / 2 : ℕ) : ℝ) * ((10000 : ℕ) : ℝ)) := by
  have hXM : ((10000 : ℕ) : ℝ) * ((10000 : ℕ) : ℝ) = (100000000 : ℝ) := by norm_num
  -- `hL2 : 2 ≤ log(10⁸)` via `exp 2 ≤ 10⁸`
  have hL2 : (2 : ℝ) ≤ Real.log (((10000 : ℕ) : ℝ) * ((10000 : ℕ) : ℝ)) := by
    rw [hXM, Real.le_log_iff_exp_le (by norm_num)]
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  -- `hDscale : D = 2 ≤ √(10⁸)/L¹`, i.e. `log(10⁸) ≤ 5000`, via `log ≤ 4·(10⁸)^{1/4} = 400`
  have hlog_le : Real.log (((10000 : ℕ) : ℝ) * ((10000 : ℕ) : ℝ)) ≤ 400 := by
    rw [hXM]
    have h := Real.log_le_rpow_div (by norm_num : (0 : ℝ) ≤ 100000000)
      (by norm_num : (0 : ℝ) < 1 / 4)
    have hval : (100000000 : ℝ) ^ ((1 : ℝ) / 4) = 100 := by
      rw [show (100000000 : ℝ) = (100 : ℝ) ^ (4 : ℕ) by norm_num,
        ← Real.rpow_natCast (100 : ℝ) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [hval] at h
    calc Real.log (100000000 : ℝ) ≤ 100 / (1 / 4) := h
      _ = 400 := by norm_num
  have hsqrt : Real.sqrt (((10000 : ℕ) : ℝ) * ((10000 : ℕ) : ℝ)) = 10000 := by
    rw [hXM, show (100000000 : ℝ) = (10000 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hDscale : ((2 : ℕ) : ℝ)
      ≤ Real.sqrt (((10000 : ℕ) : ℝ) * ((10000 : ℕ) : ℝ))
          / (Real.log (((10000 : ℕ) : ℝ) * ((10000 : ℕ) : ℝ))) ^ (1 : ℝ) := by
    rw [hsqrt, Real.rpow_one,
      le_div_iff₀ (by linarith : (0 : ℝ) < Real.log (((10000 : ℕ) : ℝ) * ((10000 : ℕ) : ℝ)))]
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]
    nlinarith [hlog_le]
  exact bridge_scale (M := 10000) (X := 10000) (e := 2) (D := 2) (B := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hDscale (by norm_num) hL2

end Salt.Chen
