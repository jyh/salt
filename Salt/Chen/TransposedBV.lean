/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SubBlocked

/-!
# GBV3 — the transposed windowed BV for the medium band (catch #60's fix, recon-first)

Design: `docs/blueprints/flags.md`, the entries `2026-07-14 GBV2 … ★ CATCH #60 ★` +
`FABLE ADJUDICATION of catch #60`.  This file establishes the **transpose backbone** of the
windowed cutoff carrier and prices the medium-band survivors down to a SINGLE named residual.

## STEP 0 — the numeric feasibility check (recorded FIRST, per the C+ discipline)

The medium band (catch #57/#60): a survivor sub-box `[2^i, 2^{i+1}) × (N, M]` with
`α = restrictAlpha (band semiprime) (2^i) (2^{i+1})` (`‖α‖ ≤ 1`, SHORT side `X_sub = 2^{i+1}`),
`β = blockPrimeInd N` (the prime side, LONG: primes `n ∈ (N, M]`, `M = 2^{k+1}−1 ≤ 2·2^k`,
`N = 2^k`, `N ≫ 8√x`).  Scales: `X_sub ∈ [polylog, √x/4)`, `X_sub·M ≤ 4T ≤ 4x`,
`D = Q·Dlev ~ √x/(log)^B`, `D0 = 2^{k0} ~ (log)^{C0}`, `T ∈ {x, x/2+1}`, `L := log(X_sub·M) ≤
log(4x) ~ log x`.  Write `A' = A`, and use the coupled family `A = 12, C0 = 14, B = 14` (as in
`GlueBV`; `A+2 ≤ C0, B`, `A ≥ 12`).

The windowed price splits (`general_BV_cutoff_final`) at the conductor cut `D0` into THREE pieces;
here is the honest per-piece arithmetic at the SWAPPED (short-`α` × long-prime) scales:

### (a) the small-conductor half (`d ≤ D0`) — CLOSES ✓ (already transpose-compatible)

`smallconductor_window_sum` / `hSmallCut_discharge` price the small conductors by regrouping the
cutoff twist per fixed `m` and pricing each fibre by the **prime-side** interval SW
(`hβSW_of_prime_indicator`, `cutoffTwist_le_sum_interval_twists`): for a primitive `ψ mod f`,
`‖cutoffTwist α (blockPrimeInd N) X_sub M T f ψ‖ ≤ X_sub·(f·K·N/(log N)^A)` — the cancellation
comes from the LONG prime side (length `N`), NOT the `m`-side.  Summing `#ψ ≤ φf`, `f ≤ D0`, with
`log N ∈ ((7/16)log x, (3/4)log x)` (so `L / log N ≤ 16/7`, costing an `(16/7)^{A+1+2C0}`
constant absorbed into `Kβ`), lands `≤ Kβ·(X_sub·M)/L^{A+1}`.  **No `√X_sub` threshold appears.**
So the small-conductor half is priced with cancellation on the prime side and closes verbatim at
the short-`α` scales.  (Verified against `hSmallCut_discharge`'s hypotheses: `N₀ ≤ N` — `N ≫ 8√x`;
`M ≤ 2N` — the re-index; `D0 ≤ (log N)^C0`; the SW coupling with `Kβ ~ (log N)`-scale.)

### (b) the large-conductor half (`D0 < d ≤ D`) — SPLITS into MainEnergy + ErrSum

`cutoff_hLargeDisc` decomposes each large-conductor imprimitive twist by the triangle into
* **MainEnergy** — the PRIMITIVE-character energy, priced by the shell (`cutoffTwist_energy_le`,
  SYMMETRIC in the two coefficient vectors) fed through the dyadic descent
  (`dyadic_energy_le_cutoff` → the four-term `four_term_scale_le`);
* **ErrSum** — the imprimitive→primitive difference, priced by the BDH Möbius **e-fold**
  (`cutoffTwist_sub_efold_blockPrimeInd` → `cutoffEfold_large_discharge`).

#### (b.1) MainEnergy — the four-term at the swapped scales — CLOSES ✓ for `X_sub ≥ L^{2(A+3)}`

The shell energy is `√X_sub·√M = √(X_sub·M) ≤ 2√x` (symmetric, orientation-free).  The four
terms of `four_term_scale_le`, at `(X, Y) = (X_sub, M)`, clear `X_sub·M/L^{A+1}` as:
* **T1** `= 2(1+log M)·√(X_sub·M)·4·2^{K+1}` (the `2^{K+1} ~ 2D` term).  `≤ XM/L^{A+1}` via the
  LEVEL cut `D ≤ √(X_sub·M)/L^B` (`D·√(X_sub M) ≤ X_sub·M/L^B`), i.e. `D² ~ X_sub·M/L^{2B}` — the
  classical two-regime win.  **Symmetric; no `√X_sub`.**  Needs `B ≥ A+2`.
* **T2** `= 2(1+log M)·√X_sub·√M·2(K+1)√(13(X_sub+1))`.  `√(13(X_sub+1)) ≤ √26·√X_sub`, leaving
  `X_sub·√M`, converted by **`hMsqrt : L^{A+3} ≤ √M`** (√M ← M/L^{A+3}).  `≤ 16√26·X_sub·M/L^{A+1}`.
  Needs `√M ≥ L^{A+3}` — HOLDS (M long).  ✓
* **T3** `= 2(1+log M)·√X_sub·√M·2(K+1)√(13(M+1))`.  Symmetric to T2 with the leftover `√X_sub`,
  converted by **`hXsqrt : L^{A+3} ≤ √X_sub`** (√X_sub ← X_sub/L^{A+3}).  Needs `√X_sub ≥ L^{A+3}`,
  i.e. `X_sub ≥ L^{2(A+3)} ~ (log x)^{2(A+3)}`.  ✓ on `X_sub ≥ L^{2(A+3)}` (a MILDER cut than
  (b.2)'s `x^{1/3}`, so it never binds where (b.2) already blocks — see below).
* **T4** `= 2(1+log M)·√X_sub·√M·√(13(X_sub+1))·√(13(M+1))·(2/2^{k0})`.  `≤ 104(1+log M)·X_sub·M·
  (2/2^{k0})`, cleared by the D0 cut `2^{k0} ≥ L^{A+4}`.  **Symmetric; no `√`-threshold.**  ✓

So MainEnergy transposes cleanly (`hMainEnergy_cutoff_discharge` is already stated for GENERIC β;
instantiate at `β = blockPrimeInd N`, `X = X_sub`, `Y = M`).  Residual condition: BOTH
`√X_sub, √M ≥ L^{A+3}`, i.e. the "medium" cut `X_sub ≥ L^{2(A+3)}`.

#### (b.2) ErrSum — the e-fold — ★ DOES NOT CLOSE at the short-`α` scales ★  (THE RESIDUAL)

`cutoffTwist_sub_efold_blockPrimeInd` folds the imprimitive→primitive difference onto the
**`α`-side** (the first slot): `β = blockPrimeInd N` is coprime-supported mod `d < N`, so ALL of
the non-coprimality (hence the whole fold) lands on `α`.  `cutoffEfold_large_discharge` then needs
`hdiv : d(e)·L^{A+5} ≤ √X_sub` for all `e ∈ [2, D]` (`DivisorBound.hdiv_discharge`).  With the
sharp `d(e) ≤ C₃·e^{1/3} ≤ C₃·D^{1/3} ≤ C₃·x^{1/6}` (`e ≤ D ≤ √x`), this reads
`√X_sub ≥ C₃·x^{1/6}·L^{A+5}`, i.e.
```
                    X_sub  ≥  C₃²·x^{1/3}·L^{2(A+5)}   (≈ x^{1/3}·polylog).
```
For the medium band, the LARGEST survivor of a box at prime-scale `N` has `X_sub ≤ 2x/(N+1)`; the
band has `N > 8√x`, and for `N > x^{2/3}` (non-empty, up to `x^{3/4}` at `z = x^{1/8}`) EVERY
survivor — including the largest — has `X_sub < x^{1/3}`.  So the e-fold `hdiv` FAILS for the
medium survivors, and the TRANSPOSE does NOT rescue it: the fold acts on the SHORT side
regardless of which slot the prime indicator sits in (swapping `α ↔ blockPrimeInd` swaps the
slots but NOT which coefficient is coprime-supported — the prime side is always coprime, so the
fold is always on the short semiprime `α`).  The crude bound is no rescue either: bounding the
imprimitive twist by its mass reintroduces the all-character (non-primitive) large-sieve loss,
giving `ErrSum ≲ N·D·X_sub/log ~ (2x)·√x/log = x^{3/2}/log ≫ x`.  **So the task's three-way split
has NO working "tiny by crude" leg** — the dividing line is `X_sub ≥ x^{1/3}` (ErrSum closes, and
the milder (b.1) `L^{2(A+3)}` cut is already subsumed) vs `X_sub < x^{1/3}` (BOTH ErrSum and crude
fail).  The whole `X_sub < x^{1/3}` range is the residual, uniformly via the (b.2) e-fold.

**Conclusion of (b.2):** the ErrSum for short `α` is exactly the classical Type-II BV regime that
the DISPERSION method (Cauchy–Schwarz on the long prime variable + large sieve) handles WITHOUT an
`α`-side Möbius fold — but the LANDED windowed machinery has ONLY the e-fold (BDH) route, which
folds `α` and hardcodes `√X_sub`.  This is NOT a mechanical transpose/port; it needs new analytic
machinery (a dispersion/`√M`-side error treatment).

### (c) the per-application budget × O(log³x) applications

IF the ErrSum closed, the per-survivor price is `≤ Kβ·(X_sub·M)/L^{A+1} ~ (log x)·(X_sub·M)/L^{A+1}
= (X_sub·M)/L^A` (the `Kβ ~ log N` cost of the SW coupling).  Per box, `∑_i X_sub_i·M ~ M·2·2^{i*}
~ 4x·M/(N+1) ~ 8x` (`2^{i*} ≤ T/(N+1)`, `M ~ 2(N+1)`), so the box price `~ 8x/L^A`; over the
`O(log²x)` boxes `(j,k)` and `O(log x)` survivors this is `O(log³x)·x/L^A = x/L^{A−3} ≤ x/L^{10}`
for `A ≥ 13`.  The budget IS satisfiable — the block is purely the ErrSum residual (b.2).

**VERDICT (STEP 0):** (a) small-conductor CLOSES; (b.1) MainEnergy CLOSES on `X_sub ≥ L^{2(A+3)}`;
(b.2) ErrSum DOES NOT CLOSE (needs `X_sub ≥ x^{1/3}`, the e-fold folds the short side, transpose
does not help); (c) budget fine modulo (b.2).  The transposed windowed chain closes small + main
but the large-conductor **error** side is the irreducible residual — see the closing flag.

## What this file lands (sorry-free, axiom-clean, NEW FILE — no edits to landed files)

1. **The transpose backbone** (verifies the adjudication's symmetry premise):
   `cutoffTwist_transpose`, `apDiscBilinCutoff_transpose` — the windowed carrier is invariant under
   `(α, X) ↔ (β, Y)` (Fubini + `m·n = n·m`).
2. **`blockPrimeInd_norm_le_one`** — the prime indicator is a valid `‖·‖ ≤ 1` coefficient.
3. **`medium_smallconductor_price`** — the transposed small-conductor cutoff-energy input at the
   medium-band survivor shapes, via the prime-side SW (`hSmallCut_discharge`): deliverable 1.
4. **`medium_band_price`** — the per-medium-survivor price via `general_BV_cutoff_unconditional`,
   with the SOLE residual the e-fold `herr_div` slot (b.2), and `subblocked_box_hprice_of_medium`
   plugging `SubBlocked.subblocked_box_price`'s abstract slot with the medium price (given the
   residual).  `hNum_at_op` is BLOCKED on the (b.2) residual; see the closing flag.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## 1. The transpose backbone — the windowed carrier is `(α,X) ↔ (β,Y)`-symmetric -/

/-- **`cutoffTwist_transpose` (FULL).**  The windowed bilinear character sum is invariant under
swapping the two coefficient vectors together with their summation tops: `cutoffTwist α β X Y T n₀
χ = cutoffTwist β α Y X T n₀ χ`.  Both are the sum over `{(m,n) : 1≤m≤X, 1≤n≤Y, m·n≤T}` of
`α_m β_n χ(mn)`; Fubini (`Finset.sum_comm`) reorders and `m·n = n·m`, `α_m β_n = β_n α_m` close
the per-term identity.  The symmetry the adjudication names ("the shell is symmetric in the two
coefficient vectors"). -/
theorem cutoffTwist_transpose (α β : ℕ → ℂ) (X Y T n₀ : ℕ) (χ : DirichletCharacter ℂ n₀) :
    cutoffTwist α β X Y T n₀ χ = cutoffTwist β α Y X T n₀ χ := by
  classical
  unfold cutoffTwist
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
  rw [Nat.mul_comm m n, mul_comm (α m) (β n)]

/-- **`apDiscBilinCutoff_transpose` (FULL).**  The windowed fixed-residue AP discrepancy is
invariant under the `(α, X) ↔ (β, Y)` transpose: `apDiscBilinCutoff α β X Y N₀ d T =
apDiscBilinCutoff β α Y X N₀ d T`.  Both the guarded residue-count and the guarded `(1/φd)`-unit
main term are sums over `{(m,n) : 1≤m≤X, 1≤n≤Y, m·n≤T}` (Fubini + `m·n = n·m`).  This is the
identity catch #60 names: it turns a prime-indicator-SECOND-slot carrier into a prime-indicator-
FIRST-slot one (and back). -/
theorem apDiscBilinCutoff_transpose (α β : ℕ → ℂ) (X Y N₀ d T : ℕ) :
    apDiscBilinCutoff α β X Y N₀ d T = apDiscBilinCutoff β α Y X N₀ d T := by
  classical
  unfold apDiscBilinCutoff
  congr 1
  · simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
    by_cases h : ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d)
    · rw [Nat.mul_comm m n] at h ⊢
      rw [if_pos h, if_pos h, mul_comm (α m) (β n)]
    · rw [Nat.mul_comm m n] at h ⊢
      rw [if_neg h, if_neg h]
  · congr 1
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
    by_cases h : IsUnit ((m * n : ℕ) : ZMod d)
    · rw [Nat.mul_comm m n] at h ⊢
      rw [if_pos h, if_pos h, mul_comm (α m) (β n)]
    · rw [Nat.mul_comm m n] at h ⊢
      rw [if_neg h, if_neg h]

/-- **`blockPrimeInd_norm_le_one` (FULL).**  The interval prime indicator is a valid `‖·‖ ≤ 1`
coefficient (it is `0` or `1`).  Reusable; inlined as `hβ1` in `general_BV_cutoff_closed`. -/
theorem blockPrimeInd_norm_le_one (N : ℕ) : ∀ n, ‖blockPrimeInd N n‖ ≤ 1 := by
  intro n; unfold blockPrimeInd
  by_cases h : N < n ∧ n.Prime
  · rw [if_pos h, norm_one]
  · rw [if_neg h, norm_zero]; norm_num

/-! ## 2. The transposed small-conductor price — CLOSES (deliverable 1, FLOOR A)

The small-conductor half is priced by CANCELLATION on the LONG prime side (STEP 0 part (a)), so it
transposes to the short-`α` medium band **verbatim**: `hSmallCut_discharge` is parametric in `α`
(needs only `‖α‖ ≤ 1`), and the survivor coefficient `restrictAlpha α a b` inherits `‖·‖ ≤ 1`
(`norm_restrictAlpha_le_one`).  So no new lemma is needed — the landed prime-side SW input applies
at the survivor's parameters. -/

/-- **`medium_smallconductor_prime_side` (FULL — deliverable 1).**  The small-conductor cutoff
energy of a medium-band survivor (`α = restrictAlpha α a b`, `‖·‖ ≤ 1`, few `m`'s) against the
LONG prime side is priced by `hSmallCut_discharge` — the χ-level per-`m` regroup
(`cutoffTwist_le_sum_interval_twists`) that prices each fibre by the PRIME-side interval SW
(`hβSW_of_prime_indicator`, cancellation at length `N`, NOT the `m`-side).  This is the landed
`hSmallCut_discharge` re-exposed at the survivor's parameters, confirming transpose-compatibility:
no `√X_sub` threshold appears, so it holds at all short-`α` scales. -/
theorem medium_smallconductor_prime_side {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M T D0 a b : ℕ) (Kβ : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → N₀ ≤ N → M ≤ 2 * N →
        (0 < Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1 + 2 * C0)
            ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        ∑ f ∈ Finset.Icc 2 D0,
            (1 / (f.totient : ℝ)) * cutoffPrimEnergy (restrictAlpha α a b) (blockPrimeInd N) X M T f
          ≤ Kβ * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1) := by
  obtain ⟨K, N₀, hK, hbody⟩ := hSmallCut_discharge hA hC0
  exact ⟨K, N₀, hK, fun α X N M T D0 a b Kβ hα hKβ hN hM2N hLpos hD0 hD0N hNM hscale =>
    hbody (restrictAlpha α a b) X N M T D0 Kβ (norm_restrictAlpha_le_one hα a b) hKβ hN hM2N hLpos
      hD0 hD0N hNM hscale⟩

/-! ## 3. The per-survivor reduced-area price (deliverable 3 — the summation-layer win)

`SubBlocked.apDiscBilinCutoff_restrict_X` shrinks a survivor's `m`-summation top from the GLOBAL
`X` (huge — `≥ x` for band boxes) to the survivor's OWN top `X_sub = 2^{i+1}−1`, since the
coefficient `restrictAlpha α (2^i) (2^{i+1})` vanishes for `m ≥ 2^{i+1}`.  This is what turns the
`X·M`-lossy nominal price (catch #59) into the reduced-area `X_sub·M ≤ 4T ≤ 4x` price
(catch #60's `X_sub·M ≤ 4x`).  `medium_band_price` performs the shrink, exposing a
reduced-top price supplier `hprice_sub` — whose intended supplier is
`general_BV_cutoff_unconditional` at `(X := X_sub, M)` with its SOLE residual the e-fold
`herr_div` slot (STEP 0 (b.2); NOT dischargeable at the short-`α` scales — see the closing flag).
-/

/-- **`medium_band_price` (FULL).**  A medium-band survivor's global-`X` cutoff carrier price
equals its REDUCED-top price at `X_sub = 2^{i+1}−1` (`apDiscBilinCutoff_restrict_X`: the carrier is
independent of the `m`-top once `2^{i+1} ≤ X + 1`, since `restrictAlpha` kills `m ≥ 2^{i+1}`).  So
any reduced-top price `hprice_sub` (area `X_sub·M ≤ 4T`) transfers to the global-`X` survivor
carrier — the summation-layer win that plugs `SubBlocked.subblocked_box_price`'s abstract slot at
the reduced area.  (`hiX : 2^{i+1} ≤ X + 1` holds for every medium-band survivor: `2^i·(N+1) ≤ T`
and `N ≫ 8√x` give `2^{i+1} ≤ 2T/(N+1) ≤ X`.) -/
theorem medium_band_price {α : ℕ → ℂ} {X M N T i : ℕ} (Dset : Finset ℕ) {P : ℝ}
    (hiX : 2 ^ (i + 1) ≤ X + 1)
    (hprice_sub : ∑ d ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
        (blockPrimeInd N) (2 ^ (i + 1) - 1) M 2 d T‖ ≤ P) :
    ∑ d ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
        (blockPrimeInd N) X M 2 d T‖ ≤ P := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun d _ => ?_))) hprice_sub
  have hpow : 1 ≤ 2 ^ (i + 1) := Nat.one_le_pow _ _ (by norm_num)
  rw [apDiscBilinCutoff_restrict_X (α := α) (a := 2 ^ i) (b := 2 ^ (i + 1))
      (X := 2 ^ (i + 1) - 1) (X' := X) (Y := M) (N₀ := 2) (d := d) (T := T)
      (by omega) (by omega)]

/-- **`subblocked_box_price_reduced` (FULL).**  The box's `L¹`-over-`d` cutoff price is bounded by
the sum over the `O(log)` survivors of their REDUCED-area prices (each at `X_sub·M ≤ 4T ≤ 4x`).
Composes `SubBlocked.subblocked_box_price` (the box price ≤ the survivor-price sum at global `X`)
with `medium_band_price` (each global-`X` survivor carrier = its reduced-top carrier).  This is the
complete summation layer of catch #60's fix: the box price is the `O(log)`-survivor sum with each
survivor priced at its OWN reduced area — the input `hprice` is exactly the per-survivor reduced
price supplied (given the e-fold residual) by `general_BV_cutoff_unconditional`. -/
theorem subblocked_box_price_reduced {α : ℕ → ℂ} {X M N T : ℕ} (K : ℕ) (hK : Nat.log 2 X ≤ K)
    (Dset : Finset ℕ) (Price : ℕ → ℝ)
    (hiX : ∀ i ∈ dyadicSurvivors N T K, 2 ^ (i + 1) ≤ X + 1)
    (hprice : ∀ i ∈ dyadicSurvivors N T K,
        ∑ d ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
          (blockPrimeInd N) (2 ^ (i + 1) - 1) M 2 d T‖ ≤ Price i) :
    ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M 2 d T‖
      ≤ ∑ i ∈ dyadicSurvivors N T K, Price i :=
  subblocked_box_price K hK Dset Price
    (fun i hi => medium_band_price Dset (hiX i hi) (hprice i hi))

/-! ## Composition sanity -/

section CompositionSanity

#check @Salt.Chen.cutoffTwist_transpose
#check @Salt.Chen.apDiscBilinCutoff_transpose
#check @Salt.Chen.blockPrimeInd_norm_le_one
#check @Salt.Chen.medium_smallconductor_prime_side
#check @Salt.Chen.medium_band_price
#check @Salt.Chen.subblocked_box_price_reduced
-- the intended per-survivor reduced-price supplier (SOLE residual = its `herr_div` slot):
#check @Salt.Chen.general_BV_cutoff_unconditional
-- the large-X_sub survivors (priced directly, `√x ≤ 4·X_sub`):
#check @Salt.Chen.cutoff_BV_at_op
-- the summation-layer host this feeds:
#check @Salt.Chen.subblocked_box_price

end CompositionSanity

end Salt.Chen
