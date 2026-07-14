/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.TransposedBV

/-!
# GBV4 — the m-scale floor closes the medium band (catch #61's Fable adjudication, executed)

Design: `docs/blueprints/flags.md`, the entries `2026-07-14 GBV3 … ★ CATCH #61 ★` and its
`FABLE ADJUDICATION` ("THE BLOCKED RANGE IS EMPTY — no dispersion needed").

## STEP 0 — the feasibility re-verification (MANDATORY, from the LANDED files)

* **(i) the `p₁` floor** — `TripleCount.tripleSet` requires `z ≤ t.1`;
  `SwitchBlocks.blockAlpha` hard-codes `z ≤ p₁` in the indicator; `omegaBlock z ε₀ 0 = z`
  (the lowest switch block's left edge IS `z`).  Every carrier support has `p₁ ≥ z`.  ✓
* **(ii) the `p₂` threshold** — `tripleSet` requires `y < t.2.1`; `CountFinal.pairSet'`
  requires `y < q.2`; `BandIdent.blockAlphaLow` has `y < p₂ ≤ N`; `BandIdent.blockAlphaSym`
  has `max y N < p₂` (SHARPER).  Every carrier support has `p₂ > y`.  ✓
* **⟹ the m-floor** — `m = p₁·p₂ ≥ z·(y+1) > z·y` in ALL three carriers; sym carries the
  sharper `z·max(y,N)`; the low box's `restrictAlpha` window `[min(zN+1,x+1), x+1)` adds
  `m ≥ zN+1`.  The floor IS `z·y`-shaped.  ✓
* **(iii) the hdiv slot** — `WindowSmallChi.general_BV_cutoff_unconditional`'s
  `herr_div : ∀ e, 2 ≤ e → e ≤ D → d(e)·L^{A+5} ≤ √X`; `GlueBV.cutoff_BV_at_op` discharged
  it via `DivisorBound.hdiv_discharge` under `√x ≤ 4X`, `D ≤ √x`, `X·M ≤ x²`.  The
  `√x ≤ 4X` relation is exactly what fails at medium `X_sub`; the direct route
  (`hdiv_direct` below) replaces it by `√F ≤ √X_sub` at the floor `F = z·y`.  ✓

Power room at the operating point (`z = x^{1/8}`, `y = x^{1/3}`, `A ≤ 14`):
`√(z·y) = x^{11/48}` vs `C₃·x^{1/6}·L^{A+5}` — `x^{1/16}` of pure power room, exactly the
adjudication's arithmetic.  ✓  STEP 0 verdict: the floor IS `z·y`-shaped; proceed.

## The design-question resolution (the brief's item 4, verified against the threshold list)

With `herr_div` discharged at the floor, the untransposed `general_BV_cutoff_unconditional`
does NOT yet close on EVERY above-floor survivor — two further thresholds bind:

1. **The LEVEL cut** (`hDscale : D ≤ √(X_sub·M)/L^B` and `herr_lev : D·L^{A+5} ≤ √(X_sub·M)`)
   fails for above-floor survivors with `X_sub·M ≪ x` (the high carrier at `N < x^{13/24}`;
   the band carriers at `N < √(x/z)`), since `D` is `√x`-scale (`s = logRatio y Dlev ≈ 3/2`,
   `docs/blueprints/chen.md`, so `Dlev ≈ y^{3/2} = √x`).
   **Resolution (IN SCOPE — the adjudication's "completed three-way survivor split"):** a
   sub-block whose entire box sits under the LOWER cutoff (`(2^{i+1}−1)·M ≤ x/2+1`) has
   IDENTICAL `T = x` and `T = x/2+1` carriers (`apDiscBilinCutoff_eq_of_under`), so it
   CANCELS in the honest T-difference — the object the consumers actually price.  The
   completed split, per dyadic sub-block `i`:
   * (a) `2^{i+1} ≤ z·y` (below the m-floor)        → BOTH one-sided carriers are `0`
         (`carrier_eq_zero_below_floor`);
   * (b) `(2^{i+1}−1)·M ≤ x/2+1` (under the cutoff) → the difference term is `0`;
   * (c) otherwise — the BOUNDARY (`dyadicBoundary`, `≤ 3` sub-blocks per box:
         `dyadicBoundary_card_le_three`) → `X_sub ≥ z·y` (hdiv ✓ by `hdiv_direct`) AND
         `X_sub·M > x/2` (level ✓ with room).  The budget improves to `O(log²x)`
         applications total (3 per box, `O(log²x)` boxes).
2. **`D < N`** (structural in the terminal theorem — it kills the β-side e-fold, the PE2
   design): at the operating `D ~ x^{1/2−ε'}` it FAILS for every piece `N ≤ D`.  The split
   does not touch it (it is `X_sub`-independent).  Status at the operating point:
   * high boxes at `N > D` — close completely through this file's chain;
   * high boxes at `N ≤ √(x/(4z))` — the WHOLE box cancels in the difference ((b) at box
     scale: max product `≤ 2zN² ≤ x/2`);
   * high boxes at `√(x/(4z)) < N ≤ D` — ★ REMAIN: `D < N` is the failing hypothesis ★;
   * band boxes (alive only at `N ≤ √(2x/z)`, and their theorem-`N` is `max y N ≤ √(2x/z)
     < D`) — ★ `D < N` fails throughout the live band range at EVERY admissible
     `s ∈ [4/3, 3]` ★; band boxes at `N > √(2x/z)` close OUTRIGHT (every `T₂`-survivor is
     below the `z·N` floor — the boundary is EMPTY, the box difference is `0`).
   This is a NEW finding (flag-worthy, reported to the house session): the `D < N` strip
   needs either a `D < N`-free e-fold kill or a rebalanced piece decomposition —
   Fable/design tier.  Every lemma below keeps `D < N` as an explicit hypothesis (the house
   parametrized form), so all statements here are unconditionally correct; the strip is a
   GLU-2/design discharge obligation, not a defect of these statements.

## GLU-2 discharge obligations (parametrized here, numeric there)

* `hfloor : C₃·x^{1/6}·Lb^{A+5} ≤ √(z·y)`, `C₃ = (3/log 2)^8`, with any uniform
  `Lb ≥ log(X_sub·M)` (`Lb := log(4x)` works — survivors have `X_sub·M ≤ 4x`);
* the structural/level bundle at the `≤ 3` boundary survivors (`X_sub·M > x/2` supplies the
  level with room);
* `D < N` per piece (the flag above).

## What this file lands (sorry-free, axiom-clean, NEW FILE — no edits to landed files)

1. (deliverable 1) `blockAlpha_support_floor` / `blockAlphaLow_support_floor` /
   `blockAlphaSym_support_floor` + the `restrictAlpha` transfers `medium_support_floor_high`
   / `medium_support_floor_low` / `medium_support_floor_sym` — the m-scale floor on the
   ACTUAL landed carriers (together: "`medium_support_floor`").
2. (deliverable 2) `carrier_eq_zero_below_floor` — the sub-blocked carrier below the floor
   is `0` (the mirror of `SubBlocked.apDiscBilinCutoff_eq_zero_of_over`); plus the (b)-leg
   `apDiscBilinCutoff_eq_of_under` — under-cutoff sub-blocks cancel in the T-difference.
3. (deliverable 3) `hdiv_direct` — `d(e)·L^{A+5} ≤ √X_sub` from `F ≤ X_sub` + `hfloor` +
   `D ≤ √x`; NO `√x ≤ 4X` (the adjudication's direct discharge).
4. (deliverable 4) `dyadicBoundary` + `dyadicBoundary_subset_survivors` +
   `dyadicBoundary_card_le_three`; `box_disc_three_way` (the completed split's summation
   layer); `medium_survivor_price` (the terminal theorem with `herr_div` ← `hdiv_direct`);
   the difference-consuming feeders `hHD_of_box_disc` / `Plo_sym_of_box_disc` /
   `Plo_low_of_box_disc` at the EXACT landed slot shapes; `hNum_at_op` (the per-box close,
   VERBATIM in the `Phi k` slot of `PieceDecomp.hBlock_of_window_prices`); and the
   comment-documented `example` #check-chaining `hNum_at_op → hBlock_of_window_prices →
   hHDblocks_of_perBlock → hBVblocks_of_generalBV` — whose conclusion is the EXACT
   `hBVblocks` hypothesis `SwitchBlocks.mainA3_of_block_remainders` names.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## 1. The m-scale support floors (deliverable 1)

Every landed carrier coefficient is supported on semiprimes `m = p₁·p₂` with `p₁ ≥ z` and
`p₂ > y` (STEP 0 items (i)/(ii)), so `m ≥ z·(y+1) > z·y`.  The sym carrier is sharper:
`p₂ > max y N` gives `m > z·max(y, N)` — the floor that closes the medium band's level cut. -/

/-- **The high-carrier floor.**  `blockAlpha z y ε₀ j m ≠ 0 → z·y < m`: the support is
`m = p₁p₂` with `z ≤ p₁` and `y < p₂`, so `m ≥ p₁·(y+1) ≥ z·y + p₁ > z·y` (`p₁ ≥ 2 > 0`). -/
theorem blockAlpha_support_floor {z y : ℕ} {ε₀ : ℝ} {j m : ℕ}
    (h : blockAlpha z y ε₀ j m ≠ 0) : z * y < m := by
  have hC : ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧ p₁ * p₂ = m
      ∧ blockIdx z ε₀ p₁ = j := by
    by_contra hnc
    exact h (by unfold blockAlpha; rw [if_neg hnc])
  obtain ⟨p₁, p₂, hp1, _hp2, hzp1, _hp1y, hyp2, hprod, _⟩ := hC
  have h1 : z * y ≤ p₁ * y := Nat.mul_le_mul hzp1 le_rfl
  have h2 : p₁ * y < p₁ * p₂ := mul_lt_mul_of_pos_left hyp2 hp1.pos
  omega

/-- **The low-carrier floor.**  `blockAlphaLow z y ε₀ j N m ≠ 0 → z·y < m` (the same
`z ≤ p₁ ≤ y < p₂` orientation; the extra `p₂ ≤ N` cap only shrinks the support). -/
theorem blockAlphaLow_support_floor {z y : ℕ} {ε₀ : ℝ} {j N m : ℕ}
    (h : blockAlphaLow z y ε₀ j N m ≠ 0) : z * y < m := by
  have hC : ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧ p₂ ≤ N
      ∧ p₁ * p₂ = m ∧ blockIdx z ε₀ p₁ = j := by
    by_contra hnc
    exact h (by unfold blockAlphaLow; rw [if_neg hnc])
  obtain ⟨p₁, p₂, hp1, _hp2, hzp1, _hp1y, hyp2, _hp2N, hprod, _⟩ := hC
  have h1 : z * y ≤ p₁ * y := Nat.mul_le_mul hzp1 le_rfl
  have h2 : p₁ * y < p₁ * p₂ := mul_lt_mul_of_pos_left hyp2 hp1.pos
  omega

/-- **The sym-carrier floor (SHARP).**  `blockAlphaSym z y ε₀ j N M m ≠ 0 → z·max(y,N) < m`:
the symmetric band's large prime satisfies `p₂ > max y N`, so the floor RISES with the piece —
`z·N`-shaped on the medium band.  This is the floor that makes every above-floor survivor of a
medium sym box satisfy the level cut (`X_sub·M ≥ z·N·N > x` at `N > √(x/z)`). -/
theorem blockAlphaSym_support_floor {z y : ℕ} {ε₀ : ℝ} {j N M m : ℕ}
    (h : blockAlphaSym z y ε₀ j N M m ≠ 0) : z * max y N < m := by
  have hC : ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ max y N < p₂ ∧ p₂ ≤ M
      ∧ p₁ * p₂ = m ∧ blockIdx z ε₀ p₁ = j := by
    by_contra hnc
    exact h (by unfold blockAlphaSym; rw [if_neg hnc])
  obtain ⟨p₁, p₂, hp1, _hp2, hzp1, _hp1y, hyp2, _hp2M, hprod, _⟩ := hC
  have h1 : z * max y N ≤ p₁ * max y N := Nat.mul_le_mul hzp1 le_rfl
  have h2 : p₁ * max y N < p₁ * p₂ := mul_lt_mul_of_pos_left hyp2 hp1.pos
  omega

/-- **`restrictAlpha` transfers support facts** — a nonvanishing restricted coefficient has a
nonvanishing base coefficient. -/
theorem restrictAlpha_ne_zero {α : ℕ → ℂ} {a b m : ℕ}
    (h : restrictAlpha α a b m ≠ 0) : α m ≠ 0 := by
  intro h0
  refine h ?_
  unfold restrictAlpha
  split_ifs with hab
  · exact h0
  · rfl

/-- **Floor transfer through `restrictAlpha`** — the generic form all three
`medium_support_floor_*` corollaries instantiate. -/
theorem restrictAlpha_support_floor {α : ℕ → ℂ} {F : ℕ}
    (hsupp : ∀ m, α m ≠ 0 → F < m) (a b : ℕ) :
    ∀ m, restrictAlpha α a b m ≠ 0 → F < m :=
  fun m hm => hsupp m (restrictAlpha_ne_zero hm)

/-- **`medium_support_floor`, high leg (deliverable 1).**  Every `m` in the support of the
sub-blocked HIGH-box coefficient (`restrictAlpha (blockAlpha j) a b` — the actual
`hHD_of_generalBV_window` α) has `m > z·y`. -/
theorem medium_support_floor_high {z y : ℕ} {ε₀ : ℝ} {j a b m : ℕ}
    (h : restrictAlpha (blockAlpha z y ε₀ j) a b m ≠ 0) : z * y < m :=
  blockAlpha_support_floor (restrictAlpha_ne_zero h)

/-- **`medium_support_floor`, low leg (deliverable 1).**  Every `m` in the support of the
band-low coefficient (`restrictAlpha (blockAlphaLow j N) a b` — the actual
`Plo_discharge_priced` low α) has `m > z·y`. -/
theorem medium_support_floor_low {z y : ℕ} {ε₀ : ℝ} {j N a b m : ℕ}
    (h : restrictAlpha (blockAlphaLow z y ε₀ j N) a b m ≠ 0) : z * y < m :=
  blockAlphaLow_support_floor (restrictAlpha_ne_zero h)

/-- **`medium_support_floor`, sym leg (deliverable 1).**  Every `m` in the support of the
band-sym coefficient (`blockAlphaSym j N M` — the actual `Plo_discharge_priced` sym α) has
`m > z·y` (weaker uniform form of the sharp `blockAlphaSym_support_floor`). -/
theorem medium_support_floor_sym {z y : ℕ} {ε₀ : ℝ} {j N M m : ℕ}
    (h : blockAlphaSym z y ε₀ j N M m ≠ 0) : z * y < m :=
  lt_of_le_of_lt (Nat.mul_le_mul le_rfl (le_max_left y N)) (blockAlphaSym_support_floor h)

/-! ## 2. The two vanishing legs (deliverable 2 + the (b)-leg)

The completed split's zero buckets: BELOW the floor the sub-blocked carrier vanishes
identically (both cutoffs); UNDER the lower cutoff the two one-sided carriers are EQUAL, so
the sub-block cancels in the honest T-difference. -/

/-- **`carrier_eq_zero_below_floor` (deliverable 2).**  For a coefficient with m-scale floor
`F` (`hsupp`) and a dyadic index `i` with `2^{i+1} ≤ F` (strictly below the floor), the
sub-blocked cutoff carrier vanishes identically — at EVERY summation top `X`, prime side `β`,
modulus `d`, and cutoff `T`.  The support mirror of
`SubBlocked.apDiscBilinCutoff_eq_zero_of_over`: there the CUTOFF empties the sub-box, here
the COEFFICIENT does (every `m ∈ [2^i, 2^{i+1})` has `m < 2^{i+1} ≤ F`, hence `α m = 0`). -/
theorem carrier_eq_zero_below_floor {α : ℕ → ℂ} {F : ℕ}
    (hsupp : ∀ m, α m ≠ 0 → F < m) {i : ℕ} (hbelow : 2 ^ (i + 1) ≤ F)
    (β : ℕ → ℂ) (X M N₀ d T : ℕ) :
    apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1))) β X M N₀ d T = 0 := by
  classical
  have h : ∀ m ∈ Finset.Icc 1 X, restrictAlpha α (2 ^ i) (2 ^ (i + 1)) m = (0 : ℂ) := by
    intro m _
    unfold restrictAlpha
    split_ifs with hm
    · by_contra hne
      exact absurd (hsupp m hne) (by omega)
    · rfl
  rw [apDiscBilinCutoff_congr (α' := fun _ => (0 : ℂ)) h, apDiscBilinCutoff_zero]

/-- **`apDiscBilinCutoff_eq_of_under` (the (b)-leg).**  If the sub-block's MAXIMAL product is
under the lower cutoff (`(b−1)·M ≤ T₁ ≤ T₂`), the two one-sided carriers COINCIDE: every pair
in the coefficient's support (`m ≤ b−1`, `n ≤ M`) passes both cutoff filters, so the filters
are inactive.  This is the leg that cancels the level-cut-failing survivors in the honest
T-difference: they contribute EQUALLY to `T = x` and `T = x/2+1` and vanish from
`‖carrier(x) − carrier(x/2+1)‖`. -/
theorem apDiscBilinCutoff_eq_of_under {α β : ℕ → ℂ} {a b X M N₀ d T₁ T₂ : ℕ}
    (hunder : (b - 1) * M ≤ T₁) (hT : T₁ ≤ T₂) :
    apDiscBilinCutoff (restrictAlpha α a b) β X M N₀ d T₂
      = apDiscBilinCutoff (restrictAlpha α a b) β X M N₀ d T₁ := by
  classical
  simp only [apDiscBilinCutoff]
  have hkey : ∀ (P : ℕ → ℕ → Prop) [∀ p q, Decidable (P p q)],
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T₂),
          (if P m n then restrictAlpha α a b m * β n else 0))
        = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T₁),
          (if P m n then restrictAlpha α a b m * β n else 0)) := by
    intro P _
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hc : restrictAlpha α a b m = 0
    · have h0 : ∀ S : Finset ℕ,
          (∑ n ∈ S, (if P m n then restrictAlpha α a b m * β n else 0)) = 0 :=
        fun S => Finset.sum_eq_zero (fun n _ => by rw [hc]; split_ifs <;> simp)
      rw [h0, h0]
    · have hab : a ≤ m ∧ m < b := by
        by_contra hab
        exact hc (by unfold restrictAlpha; rw [if_neg hab])
      have hfil : ∀ T, T₁ ≤ T →
          (Finset.Icc 1 M).filter (fun n => m * n ≤ T) = Finset.Icc 1 M := by
        intro T hTT
        refine Finset.filter_true_of_mem (fun n hn => ?_)
        rw [Finset.mem_Icc] at hn
        calc m * n ≤ (b - 1) * M := Nat.mul_le_mul (by omega) hn.2
          _ ≤ T₁ := hunder
          _ ≤ T := hTT
      rw [hfil T₂ hT, hfil T₁ le_rfl]
  rw [hkey (fun m n => ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d)),
    hkey (fun m n => IsUnit ((m * n : ℕ) : ZMod d))]

/-! ## 3. `hdiv_direct` — the floor-level divisor-bound discharge (deliverable 3)

The direct discharge the adjudication names: `d(e) ≤ C₃·e^{1/3} ≤ C₃·x^{1/6}` (`e ≤ D ≤ √x`,
`DivisorBound.card_divisors_cube_root`), so `d(e)·L^{A+5} ≤ C₃·x^{1/6}·Lb^{A+5} ≤ √F ≤ √X`
under the GLU-2 obligation `hfloor` — NO `√x ≤ 4X`, no `X·M ≤ x²`.  At the operating point
`F = z·y = x^{11/24}`, `Lb = log(4x)`: `x^{1/16}` of power room. -/

/-- **`hdiv_direct` (deliverable 3).**  The exact `herr_div` slot of
`general_BV_cutoff_unconditional`, discharged from the m-scale floor: `F ≤ X` (the survivor
sits above the floor), `D ≤ √x` (the level is below `√x`), `log(X·M) ≤ Lb` (a uniform log
bound — `Lb := log(4x)` at the operating point), and the numeric floor inequality `hfloor`
(GLU-2's obligation, with `x^{1/16}` of room at `F = z·y`). -/
theorem hdiv_direct {A : ℝ} (hA : 0 ≤ A) (x Lb : ℝ) (F X M D : ℕ)
    (hFX : F ≤ X) (h1X : 1 ≤ X) (h1M : 1 ≤ M)
    (hDx : (D : ℝ) ≤ Real.sqrt x)
    (hLb : Real.log ((X : ℝ) * (M : ℝ)) ≤ Lb)
    (hfloor : ((3 : ℝ) / Real.log 2) ^ 8 * x ^ ((1 : ℝ) / 6) * Lb ^ (A + 5)
        ≤ Real.sqrt (F : ℝ)) :
    ∀ e : ℕ, 1 ≤ e → e ≤ D →
      (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5)
        ≤ Real.sqrt (X : ℝ) := by
  intro e h1e heD
  set C : ℝ := ((3 : ℝ) / Real.log 2) ^ 8 with hC
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by rw [hC]; positivity
  -- `x > 0` from `1 ≤ e ≤ D ≤ √x`.
  have hsx : (1 : ℝ) ≤ Real.sqrt x := by
    have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast h1e
    have heD' : (e : ℝ) ≤ (D : ℝ) := by exact_mod_cast heD
    linarith
  have hxpos : (0 : ℝ) < x := Real.sqrt_pos.mp (by linarith)
  -- `0 ≤ L ≤ Lb`.
  have hXM1 : (1 : ℝ) ≤ (X : ℝ) * (M : ℝ) := by
    have hX' : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h1X
    have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1M
    nlinarith
  have hLnn : (0 : ℝ) ≤ Real.log ((X : ℝ) * (M : ℝ)) := Real.log_nonneg hXM1
  -- Step A: `d(e) ≤ C·x^{1/6}` (the DivisorBound cube-root bound at `e ≤ D ≤ √x`).
  have hsub : (e.divisors.card : ℝ) ≤ C * (e : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [hC]; exact card_divisors_cube_root e h1e
  have hle_sx : (e : ℝ) ≤ Real.sqrt x := le_trans (by exact_mod_cast heD) hDx
  have hsx13 : (Real.sqrt x) ^ ((1 : ℝ) / 3) = x ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]; congr 1; norm_num
  have he13 : (e : ℝ) ^ ((1 : ℝ) / 3) ≤ x ^ ((1 : ℝ) / 6) := by
    rw [← hsx13]; exact Real.rpow_le_rpow (by positivity) hle_sx (by norm_num)
  have hsub2 : (e.divisors.card : ℝ) ≤ C * x ^ ((1 : ℝ) / 6) :=
    le_trans hsub (mul_le_mul_of_nonneg_left he13 hCpos.le)
  -- Step B: `L^{A+5} ≤ Lb^{A+5}`.
  have hLpow : (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5) ≤ Lb ^ (A + 5) :=
    Real.rpow_le_rpow hLnn hLb (by linarith)
  -- assemble: `d(e)·L^{A+5} ≤ C·x^{1/6}·Lb^{A+5} ≤ √F ≤ √X`.
  calc (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5)
      ≤ (C * x ^ ((1 : ℝ) / 6)) * Lb ^ (A + 5) :=
        mul_le_mul hsub2 hLpow (Real.rpow_nonneg hLnn _) (by positivity)
    _ = C * x ^ ((1 : ℝ) / 6) * Lb ^ (A + 5) := by ring
    _ ≤ Real.sqrt (F : ℝ) := hfloor
    _ ≤ Real.sqrt (X : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hFX)

/-! ## 4. The boundary survivors and the completed three-way split (deliverable 4, engine) -/

/-- **The boundary sub-block set** — the dyadic `m`-indices that survive ALL THREE zero tests:
under the `T₂`-corner (`2^i·(N+1) ≤ T₂`, else `apDiscBilinCutoff_eq_zero_of_over`), above the
m-floor (`F < 2^{i+1}`, else `carrier_eq_zero_below_floor`), and over the lower cutoff
(`T₁ < (2^{i+1}−1)·M`, else `apDiscBilinCutoff_eq_of_under` cancels the difference).  Only
these need an analytic price — and each has `X_sub = 2^{i+1}−1 ≥ F` (hdiv) and
`X_sub·M > T₁` (the level cut, at `T₁ = x/2+1`). -/
def dyadicBoundary (N M T₁ T₂ F K : ℕ) : Finset ℕ :=
  (Finset.range (K + 1)).filter
    (fun i => 2 ^ i * (N + 1) ≤ T₂ ∧ F < 2 ^ (i + 1) ∧ T₁ < (2 ^ (i + 1) - 1) * M)

/-- The boundary sub-blocks are `T₂`-survivors (`SubBlocked.dyadicSurvivors`); in particular
`#dyadicBoundary ≤ ⌊log₂ T₂⌋ + 1` via `dyadicSurvivors_card_le`. -/
theorem dyadicBoundary_subset_survivors (N M T₁ T₂ F K : ℕ) :
    dyadicBoundary N M T₁ T₂ F K ⊆ dyadicSurvivors N T₂ K := by
  intro i hi
  rw [dyadicBoundary, Finset.mem_filter] at hi
  rw [dyadicSurvivors, Finset.mem_filter]
  exact ⟨hi.1, hi.2.1⟩

/-- **At most THREE boundary sub-blocks per box.**  At the dyadic-piece geometry
(`M ≤ 2·(N+1)`, `T₂ ≤ 2·T₁` — both hold at `M = pieceM k`, `N = pieceN k`, `T₂ = x`,
`T₁ = x/2+1`), any two boundary indices differ by at most `2`: for `i, i'` in the boundary,
`2^{i'}·(N+1) ≤ T₂ ≤ 2T₁ < 2·2^{i+1}·M ≤ 8·2^i·(N+1)`, so `2^{i'} < 2^{i+3}`.  Hence the
boundary sits inside three consecutive dyadics — the budget is `≤ 3` terminal-theorem
applications per box, `O(log²x)` in total over the `(j, k)` grid. -/
theorem dyadicBoundary_card_le_three {N M T₁ T₂ F K : ℕ}
    (hM : M ≤ 2 * (N + 1)) (hT : T₂ ≤ 2 * T₁) :
    (dyadicBoundary N M T₁ T₂ F K).card ≤ 3 := by
  rcases Finset.eq_empty_or_nonempty (dyadicBoundary N M T₁ T₂ F K) with he | hne
  · rw [he]; simp
  · set S := dyadicBoundary N M T₁ T₂ F K with hS
    have hi₀S : S.min' hne ∈ S := Finset.min'_mem S hne
    set i₀ := S.min' hne with hi₀
    have hkey : ∀ i' ∈ S, i' ≤ i₀ + 2 := by
      intro i' hi'
      have h0 := hi₀S
      rw [hS, dyadicBoundary, Finset.mem_filter] at hi' h0
      -- `2^{i'}(N+1) ≤ T₂ ≤ 2T₁ < 2(2^{i₀+1}−1)M ≤ 2^{i₀+3}(N+1)`.
      have hstep : 2 * ((2 ^ (i₀ + 1) - 1) * M) ≤ 2 ^ (i₀ + 3) * (N + 1) := by
        have h1 : (2 ^ (i₀ + 1) - 1) * M ≤ 2 ^ (i₀ + 1) * (2 * (N + 1)) :=
          Nat.mul_le_mul (by omega) hM
        have h2 : (2 : ℕ) ^ (i₀ + 3) = 2 ^ (i₀ + 1) * 4 := by
          rw [show i₀ + 3 = (i₀ + 1) + 2 by omega, pow_add]; norm_num
        calc 2 * ((2 ^ (i₀ + 1) - 1) * M)
            ≤ 2 * (2 ^ (i₀ + 1) * (2 * (N + 1))) := by omega
          _ = 2 ^ (i₀ + 1) * 4 * (N + 1) := by ring
          _ = 2 ^ (i₀ + 3) * (N + 1) := by rw [h2]
      have hchain : 2 ^ i' * (N + 1) < 2 ^ (i₀ + 3) * (N + 1) := by
        calc 2 ^ i' * (N + 1) ≤ T₂ := hi'.2.1
          _ ≤ 2 * T₁ := hT
          _ < 2 * ((2 ^ (i₀ + 1) - 1) * M) := by
              have := h0.2.2.2
              omega
          _ ≤ 2 ^ (i₀ + 3) * (N + 1) := hstep
      have hpow : 2 ^ i' < 2 ^ (i₀ + 3) :=
        lt_of_mul_lt_mul_right hchain (Nat.zero_le _)
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow
      omega
    have hsub : S ⊆ Finset.Icc i₀ (i₀ + 2) := by
      intro i' hi'
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le S i' hi', hkey i' hi'⟩
    calc S.card ≤ (Finset.Icc i₀ (i₀ + 2)).card := Finset.card_le_card hsub
      _ = 3 := by rw [Nat.card_Icc]; omega

/-- **`box_disc_three_way` (deliverable 4, the completed split).**  The box's `L¹`-over-`d`
HONEST T-difference is bounded by the boundary-survivor price sum: per dyadic sub-block,
* below the floor → both one-sided carriers vanish (`carrier_eq_zero_below_floor`);
* under the lower cutoff → the difference term vanishes (`apDiscBilinCutoff_eq_of_under`);
* over the `T₂`-corner → both carriers vanish (`apDiscBilinCutoff_eq_zero_of_over`);
* otherwise (the `≤ 3` boundary survivors) → the triangle prices BOTH one-sided carriers at
  the REDUCED top `X_sub = 2^{i+1}−1` (`apDiscBilinCutoff_restrict_X`), where `X_sub ≥ F`
  (hdiv via `hdiv_direct`) and `X_sub·M > T₁` (the level cut).
This is the summation layer that closes catch #61's split: the price slot `hprice` is
exactly what `medium_survivor_price` supplies (twice: `T = T₂` and `T = T₁`). -/
theorem box_disc_three_way {α : ℕ → ℂ} {X M N T₁ T₂ F : ℕ} (K : ℕ)
    (hK : Nat.log 2 X ≤ K) (hT : T₁ ≤ T₂)
    (hsupp : ∀ m, α m ≠ 0 → F < m)
    (Dset : Finset ℕ) (r : ℕ → ℕ) (Price : ℕ → ℝ)
    (hiX : ∀ i ∈ dyadicBoundary N M T₁ T₂ F K, 2 ^ (i + 1) ≤ X + 1)
    (hprice : ∀ i ∈ dyadicBoundary N M T₁ T₂ F K,
        (∑ d ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd N) (2 ^ (i + 1) - 1) M (r d) d T₂‖)
          + (∑ d ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd N) (2 ^ (i + 1) - 1) M (r d) d T₁‖) ≤ Price i) :
    ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T₂
        - apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T₁‖
      ≤ ∑ i ∈ dyadicBoundary N M T₁ T₂ F K, Price i := by
  classical
  set B := dyadicBoundary N M T₁ T₂ F K with hB
  -- (1) the dyadic decomposition of both one-sided carriers (as in `SubBlocked`).
  have hdecomp : ∀ (T d : ℕ), apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T
      = ∑ i ∈ Finset.range (K + 1),
          apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd N) X M (r d) d T := by
    intro T d
    rw [← apDiscBilinCutoff_sum_alpha (blockPrimeInd N) X M (r d) d T (Finset.range (K + 1))
          (fun i => restrictAlpha α (2 ^ i) (2 ^ (i + 1)))]
    refine apDiscBilinCutoff_congr (fun m hm => ?_)
    rw [Finset.mem_Icc] at hm
    exact (restrictAlpha_dyadic_sum hm.1 (le_trans (Nat.log_mono_right hm.2) hK)).symm
  -- (2) per `d`, the difference restricts to the boundary (the three zero tests).
  have hdiff : ∀ d, apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T₂
        - apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T₁
      = ∑ i ∈ B, (apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd N) X M (r d) d T₂
          - apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd N) X M (r d) d T₁) := by
    intro d
    rw [hdecomp T₂ d, hdecomp T₁ d, ← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset
    · rw [hB, dyadicBoundary]; exact Finset.filter_subset _ _
    · intro i hi hnB
      have hnP : ¬(2 ^ i * (N + 1) ≤ T₂ ∧ F < 2 ^ (i + 1) ∧ T₁ < (2 ^ (i + 1) - 1) * M) := by
        intro hP
        exact hnB (by rw [hB, dyadicBoundary, Finset.mem_filter]; exact ⟨hi, hP⟩)
      by_cases h1 : 2 ^ i * (N + 1) ≤ T₂
      · by_cases h2 : F < 2 ^ (i + 1)
        · -- over the lower cutoff fails ⟹ under it: the (b)-leg cancels the difference.
          have h3 : (2 ^ (i + 1) - 1) * M ≤ T₁ := by
            by_contra h3
            exact hnP ⟨h1, h2, by omega⟩
          rw [apDiscBilinCutoff_eq_of_under (α := α) (β := blockPrimeInd N) h3 hT, sub_self]
        · -- below the m-floor: both carriers vanish.
          have hbelow : 2 ^ (i + 1) ≤ F := by omega
          rw [carrier_eq_zero_below_floor hsupp hbelow,
            carrier_eq_zero_below_floor hsupp hbelow, sub_self]
      · -- over the `T₂`-corner (hence the `T₁`-corner): both carriers vanish.
        have hover₂ : T₂ < 2 ^ i * (N + 1) := by omega
        have hover₁ : T₁ < 2 ^ i * (N + 1) := by omega
        rw [apDiscBilinCutoff_eq_zero_of_over hover₂,
          apDiscBilinCutoff_eq_zero_of_over hover₁, sub_self]
  -- (3) triangle, swap, shrink to the reduced top, price.
  calc ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T₂
        - apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T₁‖
      = ∑ d ∈ Dset, ‖∑ i ∈ B,
          (apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd N) X M (r d) d T₂
            - apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd N) X M (r d) d T₁)‖ := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [hdiff d]
    _ ≤ ∑ d ∈ Dset, ∑ i ∈ B,
          (‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd N) X M (r d) d T₂‖
            + ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd N) X M (r d) d T₁‖) := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
        exact norm_sub_le _ _
    _ = ∑ i ∈ B, ∑ d ∈ Dset,
          (‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd N) X M (r d) d T₂‖
            + ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd N) X M (r d) d T₁‖) := Finset.sum_comm
    _ ≤ ∑ i ∈ B, Price i := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have h1 : 2 ^ (i + 1) ≤ (2 ^ (i + 1) - 1) + 1 := by
          have : 1 ≤ 2 ^ (i + 1) := Nat.one_le_pow _ _ (by norm_num)
          omega
        have h2 : 2 ^ (i + 1) - 1 ≤ X := by
          have := hiX i hi
          omega
        refine le_trans (le_of_eq ?_) (hprice i hi)
        rw [Finset.sum_add_distrib]
        congr 1
        · refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [apDiscBilinCutoff_restrict_X h1 h2]
        · refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [apDiscBilinCutoff_restrict_X h1 h2]

/-! ## 5. `medium_survivor_price` — the terminal theorem with `herr_div` ← `hdiv_direct` -/

open Classical in
/-- **`medium_survivor_price` (deliverable 4, the per-survivor supplier).**
`general_BV_cutoff_unconditional` with its `herr_div` slot discharged by the m-scale floor
(`hdiv_direct`): the three GLU-BV operating relations `√x ≤ 4X`, `X·M ≤ x²` of
`cutoff_BV_at_op` are REPLACED by `F ≤ X` (the survivor is above the floor — automatic on
`dyadicBoundary`), `D ≤ √x`, the uniform log bound `log(X·M) ≤ Lb`, and the numeric floor
inequality `hfloor : C₃·x^{1/6}·Lb^{A+5} ≤ √F` (GLU-2's obligation; `x^{1/16}` of room at
`F = z·y`).  Every other hypothesis is the terminal theorem's own threshold list, passed
through verbatim (including `D < N` — see the file header's flag for its discharge range).
The conclusion is the exact per-side price `box_disc_three_way`'s `hprice` consumes at
`X := 2^{i+1} − 1` (note the price is `T`-independent: apply once at `T = x`, once at
`T = x/2+1`). -/
theorem medium_survivor_price {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (x Lb : ℝ) (F : ℕ) (α : ℕ → ℂ) (X N M T D0 D k0 Klog : ℕ) (Dset : Finset ℕ)
        (r : ℕ → ℕ) (Kβ Km Kβ' B : ℝ),
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
        -- the m-scale floor discharge of `herr_div` (replaces GLU-BV's `√x ≤ 4X` route)
        F ≤ X →
        ((D : ℝ) ≤ Real.sqrt x) →
        (Real.log ((X : ℝ) * (M : ℝ)) ≤ Lb) →
        (((3 : ℝ) / Real.log 2) ^ 8 * x ^ ((1 : ℝ) / 6) * Lb ^ (A + 5)
            ≤ Real.sqrt (F : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D → 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (∀ e, 2 ≤ e → e ≤ D →
            (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ C0) →
        ((D : ℝ) ≤ (X : ℝ) * (M : ℝ)) →
        (∀ e, 2 ≤ e → e ≤ D →
            Real.log ((X : ℝ) * (M : ℝ)) ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + C0) ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1 + 2 * C0)
            ≤ Km * (Real.log N) ^ (A + 2 * C0)) →
        (∀ e, 2 ≤ e → e ≤ D →
            K * (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (A + 1 + 1 + 2 * C0)
              ≤ Kβ' * (Real.log N) ^ (A + 1 + 2 * C0)) →
        ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
          ≤ (Kβ + (6 * (Km + 448 + 32 * Real.sqrt 26)
                + ((2 : ℝ) ^ (A + 5) * Kβ' + 15360))) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hbody⟩ := general_BV_cutoff_unconditional hA hC0
  refine ⟨K, N₀, hK0, fun x Lb F α X N M T D0 D k0 Klog Dset r Kβ Km Kβ' B hα hKβ hKm hKβ' hN
    hM2N hD0N hDge1 hcop2 hL1 hD0 hD0N' hNM hD1 hDsetD hDN hX2 hM2 hBge hCge hD0eq h2D0 hD0D
    hKlog hDscale hD0lo_main hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev hFX hDx hLbb hfloor
    herr_LEpos herr_D0E hDXM herr_scale hcoupG hcoup3 herr_book4 => ?_⟩
  have herr_div : ∀ e, 2 ≤ e → e ≤ D →
      (e.divisors.card : ℝ) * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 5)
        ≤ Real.sqrt (X : ℝ) :=
    fun e he2 heD =>
      hdiv_direct hA.le x Lb F X M D hFX (by omega) (by omega) hDx hLbb hfloor e (by omega) heD
  exact hbody α X N M T D0 D k0 Klog Dset r Kβ Km Kβ' B hα hKβ hKm hKβ' hN hM2N hD0N hDge1 hcop2
    hL1 hD0 hD0N' hNM hD1 hDsetD hDN hX2 hM2 hBge hCge hD0eq h2D0 hD0D hKlog hDscale hD0lo_main
    hXsqrt hMsqrt herr_lev herr_D0lo herr_Mlev herr_div herr_LEpos herr_D0E hDXM herr_scale
    hcoupG hcoup3 herr_book4

/-! ## 6. The difference-consuming feeders — the landed slot shapes

The three-way split prices the T-DIFFERENCE, so the consumers must be fed at the difference,
not per side.  For the HIGH boxes, `hHD_of_box_disc` mirrors `WindowClose.
hHD_of_generalBV_window` (same identification `blockBox_windowDisc_eq`, no per-side
triangle); its conclusion is the VERBATIM `Phi k` summand of
`PieceDecomp.hBlock_of_window_prices`.  For the BAND boxes, `Plo_sym_of_box_disc` /
`Plo_low_of_box_disc` consume the landed norm-identifications `BandIdent.norm_symRect_eq` /
`norm_lowRect_eq` and produce the VERBATIM `hSym`/`hLow` inputs of `BandClose.Plo_discharge`
(bypassing `Plo_discharge_priced`'s per-side triangle, which would reintroduce the
level-cut-failing survivors). -/

/-- **`hHD_of_box_disc`** — the high-box honest discrepancy priced at the T-DIFFERENCE.
Per `d`, `|blockBoxHonestDisc| = ‖carrier(x) − carrier(x/2+1)‖` (the WindowSW
identification); the difference sum is exactly `box_disc_three_way`'s conclusion. -/
theorem hHD_of_box_disc {x z y : ℕ} {ε₀ : ℝ} {j N M a b X : ℕ} (Dset : Finset ℕ) {P : ℝ}
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * N + 1) (hxlo : x / 2 + 1 ≤ x)
    (hdiff : ∑ d ∈ Dset,
        ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
            (blockPrimeInd N) X M 2 d x
          - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
            (blockPrimeInd N) X M 2 d (x / 2 + 1)‖ ≤ P) :
    ∑ d ∈ Dset, |blockBoxHonestDisc x z y ε₀ j N M a b d| ≤ P := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun d _ => ?_))) hdiff
  have hid : ((blockBoxHonestDisc x z y ε₀ j N M a b d : ℝ) : ℂ)
      = apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
          (blockPrimeInd N) X M 2 d x
        - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
          (blockPrimeInd N) X M 2 d (x / 2 + 1) := by
    rw [blockBox_windowDisc_eq (X := X) (d := d) hz hbX hord hxlo, blockBoxHonestDisc,
      nuChen_apply]
    push_cast
    ring
  rw [← hid, Complex.norm_real, Real.norm_eq_abs]

/-- **`Plo_sym_of_box_disc`** — the symmetric band rectangles priced at the T-difference:
per `(k, d)` the landed `norm_symRect_eq` identifies `|bandSymRectDisc|` with the difference
norm; summing gives the VERBATIM `hSym` input of `BandClose.Plo_discharge`. -/
theorem Plo_sym_of_box_disc {x z y : ℕ} {ε₀ : ℝ} {j X : ℕ} (Ps : ℕ) (bound : ℝ)
    (PsymK : ℕ → ℝ) (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x)
    (hdiffK : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d x
              - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) 2 d (x / 2 + 1)‖)
          ≤ PsymK k) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandSymRectDisc x z y ε₀ j (pieceN k) (pieceM k) d| else 0)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK k := by
  classical
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [← Finset.sum_filter]
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun d _ => ?_))) (hdiffK k hk)
  exact (norm_symRect_eq hxX hxlo).symm

/-- **`Plo_low_of_box_disc`** — the low band rectangles priced at the T-difference, via the
landed `norm_lowRect_eq`; the VERBATIM `hLow` input of `BandClose.Plo_discharge` (at the
band's own `m`-window `[min(z·pieceN k + 1, x+1), x+1)`, whose `restrictAlpha` floor is the
SHARP `z·N`-shaped one). -/
theorem Plo_low_of_box_disc {x z y : ℕ} {ε₀ : ℝ} {j X : ℕ} (Ps : ℕ) (bound : ℝ)
    (PlowK : ℕ → ℝ) (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x)
    (hdiffK : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) 2 d x
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) 2 d (x / 2 + 1)‖)
          ≤ PlowK k) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandLowDisc x z y ε₀ j (pieceN k) (pieceM k)
            (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK k := by
  classical
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [← Finset.sum_filter]
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun d _ => ?_))) (hdiffK k hk)
  exact (norm_lowRect_eq (by omega) hxlo).symm

/-! ## 7. `hNum_at_op` — the per-box close, in the VERBATIM `Phi k` slot shape -/

open Classical in
/-- **`hNum_at_op` (deliverable 4, the goal's per-box form).**  The completed three-way
survivor split at the `z·y` floor, for a HIGH box `[a, b) × (N, M]`: the box's `d`-filtered
honest-discrepancy sum — the EXACT `hHigh` summand of `PieceDecomp.hBlock_of_window_prices`
(`Phi k := ∑_{i ∈ boundary} Price i`, a `≤ 3`-term sum by `dyadicBoundary_card_le_three`) —
is bounded by the boundary-survivor prices.  Composes `hHD_of_box_disc` (the WindowSW
identification at the T-difference) with `box_disc_three_way` (the split; `hsupp` :=
`medium_support_floor_high`, no hypothesis needed).  The `hprice` slot is exactly TWO
`medium_survivor_price` applications per boundary survivor (`T = x` and `T = x/2+1`, same
price — the bound is `T`-free) at `X := 2^{i+1} − 1`, where `z·y ≤ X` holds by boundary
membership and `X·M > x/2` supplies the level cut. -/
theorem hNum_at_op {x z y : ℕ} {ε₀ : ℝ} {j N M a b X : ℕ} (K Ps : ℕ) (bound : ℝ)
    (Price : ℕ → ℝ)
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * N + 1) (hxlo : x / 2 + 1 ≤ x)
    (hK : Nat.log 2 X ≤ K)
    (hiX : ∀ i ∈ dyadicBoundary N M (x / 2 + 1) x (z * y) K, 2 ^ (i + 1) ≤ X + 1)
    (hprice : ∀ i ∈ dyadicBoundary N M (x / 2 + 1) x (z * y) K,
        (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) a b)
                (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd N) (2 ^ (i + 1) - 1) M 2 d x‖)
          + (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) a b)
                  (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd N) (2 ^ (i + 1) - 1) M 2 d
                (x / 2 + 1)‖)
          ≤ Price i) :
    (∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |blockBoxHonestDisc x z y ε₀ j N M a b d| else 0)
      ≤ ∑ i ∈ dyadicBoundary N M (x / 2 + 1) x (z * y) K, Price i := by
  classical
  rw [← Finset.sum_filter]
  refine hHD_of_box_disc _ hz hbX hord hxlo ?_
  exact box_disc_three_way K hK hxlo (fun m hm => medium_support_floor_high hm) _ (fun _ => 2)
    Price hiX hprice

/-! ## 8. Composition sanity — the #check-chain into the exact `hBVblocks` shape

The `example` below is the required composition demonstration: per `(j, k)` box,
`hNum_at_op` supplies the VERBATIM `Phi k` slot of `hBlock_of_window_prices`; the band
budget `Plo j` and the conversion error are the other two legs (their own suppliers:
`Plo_sym_of_box_disc`/`Plo_low_of_box_disc` → `BandClose.Plo_discharge`, and
`GlueBV.hCE_discharge`); `hHDblocks_of_perBlock` assembles the blocks; and
`hBVblocks_of_generalBV` emits a conclusion that is character-for-character the
`hBVblocks` hypothesis of `SwitchBlocks.mainA3_of_block_remainders`.  The numeric
hypotheses (`Price`, `Plo`, `RHD`, `RCE`, `hSum`, `hNum`) are GLU-2's obligations: each
`Price j k i` is TWO `medium_survivor_price` applications at the reduced top `2^{i+1}−1`
(`≤ 3` per box, `O(log² x)` in total), and `hSum`/`hNum` are the `A ≥ 13`-family budget
row.  See the file header for the `D < N` discharge flag. -/

example (x z y : ℕ) (ε₀ : ℝ) (Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (Q : ℝ) (Dlev : ℕ) (X K : ℕ)
    (hz : 1 ≤ z) (hxlo : x / 2 + 1 ≤ x) (hxX : x ≤ X) (hK : Nat.log 2 X ≤ K)
    (hiX : ∀ k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        2 ^ (i + 1) ≤ X + 1)
    (Price : ℕ → ℕ → ℕ → ℝ)
    (hprice : ∀ j k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < Q * Dlev),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                  (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k) 2 d x‖)
          + (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < Q * Dlev),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                    (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k) 2 d (x / 2 + 1)‖)
          ≤ Price j k i)
    (Plo : ℕ → ℝ)
    (hLow : ∀ j, (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < Q * Dlev then
          |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k)
            (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0) ≤ Plo j)
    (RHD RCE : ℝ)
    (hSum : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ((∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
              Price j k i) + Plo j)) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < Q * Dlev then blockConvErr x z y ε₀ j d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) :
    -- the EXACT `hBVblocks` hypothesis of `mainA3_of_block_remainders`:
    (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        rosserRemainder (blockSwitchSieve x z y ε₀ j Ps hPs hPodd) (Q * Dlev))
      ≤ (x : ℝ) / (Real.log x) ^ 10 := by
  have hBlock : ∀ j ∈ Finset.range (maxBlock x z ε₀ + 1),
      (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < Q * Dlev then |blockHonestDisc x z y ε₀ j d| else 0)
        ≤ (∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
              Price j k i) + Plo j := by
    intro j _
    refine hBlock_of_window_prices x z y ε₀ Ps (Q * Dlev) j
      (fun k => ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        Price j k i)
      (Plo j) ?_ (hLow j)
    intro k _
    exact hNum_at_op K Ps (Q * Dlev) (Price j k) hz
      (le_trans (min_le_right _ _) (Nat.add_le_add_right hxX 1)) (min_le_left _ _)
      hxlo hK (hiX k) (hprice j k)
  exact hBVblocks_of_generalBV x z y ε₀ Ps hPs hPodd Q Dlev
    (hHDblocks_of_perBlock x z y ε₀ Ps (Q * Dlev) _ hBlock hSum) hCE hNum

/-! ## Composition sanity -/

section CompositionSanity

#check @Salt.Chen.blockAlpha_support_floor
#check @Salt.Chen.blockAlphaLow_support_floor
#check @Salt.Chen.blockAlphaSym_support_floor
#check @Salt.Chen.medium_support_floor_high
#check @Salt.Chen.medium_support_floor_low
#check @Salt.Chen.medium_support_floor_sym
#check @Salt.Chen.carrier_eq_zero_below_floor
#check @Salt.Chen.apDiscBilinCutoff_eq_of_under
#check @Salt.Chen.hdiv_direct
#check @Salt.Chen.dyadicBoundary
#check @Salt.Chen.dyadicBoundary_subset_survivors
#check @Salt.Chen.dyadicBoundary_card_le_three
#check @Salt.Chen.box_disc_three_way
#check @Salt.Chen.medium_survivor_price
#check @Salt.Chen.hHD_of_box_disc
#check @Salt.Chen.Plo_sym_of_box_disc
#check @Salt.Chen.Plo_low_of_box_disc
#check @Salt.Chen.hNum_at_op
-- the landed consumers this feeds (the VERBATIM slots):
#check @Salt.Chen.hBlock_of_window_prices
#check @Salt.Chen.Plo_discharge
#check @Salt.Chen.hHDblocks_of_perBlock
#check @Salt.Chen.hBVblocks_of_generalBV
#check @Salt.Chen.mainA3_of_block_remainders
-- the landed suppliers this composes:
#check @Salt.Chen.general_BV_cutoff_unconditional
#check @Salt.Chen.card_divisors_cube_root
#check @Salt.Chen.dyadicSurvivors_card_le
#check @Salt.Chen.subblocked_box_price_reduced

end CompositionSanity

end Salt.Chen
