/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.GlueBV
import Salt.Chen.SwitchStrip

/-!
# GBV2 — the dyadic `m`-sub-blocking of the window prices (catch #59's ratified fix)

Design: `docs/blueprints/flags.md`, the entries `2026-07-14 GLU-BV … ★ CATCH #59 ★` and its
`FABLE ADJUDICATION` (the `m`-sub-blocking fix).  This file re-organizes the SUMMATION layer of
the windowed-BV prices — it does NOT touch `general_BV_cutoff_unconditional` (the per-application
price is correct).  It supplies the `apDiscBilinCutoff` additivity backbone (mirroring
`SwitchStrip.apDiscBilin_sum_alpha`), the cutoff-corner vanishing lemma, and the dyadic sub-block
decomposition of a box's `L¹`-over-`d` cutoff price into a coherent sum over the `O(log)`
NON-vanishing sub-boxes.

## Numeric plan (recorded FIRST, per the C-tier discipline)

Fix a `(j, piece k)` with `N = pieceN k = 2^k − 1` (re-indexed to `N' = 2^k` via
`GlueBV.blockPrimeInd_pieceN_eq` for the `M ≤ 2N'` slot), `M = pieceM k = 2^{k+1} − 1 ≤ 2·2^k`.
The `β`-side is `blockPrimeInd N` — the indicator of primes `n ∈ (N, M]`, so its support has
`min-n = N + 1`.  The `m`-window is `[a, b)` (carried by `restrictAlpha`); the cutoff is
`m·n ≤ T ≤ x`.

### The dyadic `m`-partition and the corner test

Split `[a, b)` into dyadic sub-blocks `[2^i, 2^{i+1})`, `i = 0 … K := ⌊log₂ X⌋`.  By the
additivity `apDiscBilinCutoff_sum_alpha` (both guarded counts are LINEAR in the `m`-coefficient),
the box's cutoff disc is the sum of the sub-box discs (`sum_norm_apDiscBilinCutoff_dyadic_decomp`).
Under the cutoff, a sub-box `[2^i, 2^{i+1}) × (N, M]` with `2^i·(N+1) > T` has EVERY summand
filtered out (`min-m·min-n = 2^i·(N+1) > T`), so BOTH guarded counts are empty and the cutoff disc
VANISHES identically (`apDiscBilinCutoff_eq_zero_of_over`).

### The survivor count (`O(log)` per box)

`SurvivorSet = {i ≤ K : 2^i·(N+1) ≤ T}` (`dyadicSurvivors`).  Since `N + 1 ≥ 1`, each survivor has
`2^i ≤ T`, so `SurvivorSet ⊆ range(⌊log₂ T⌋ + 1)` and `#SurvivorSet ≤ ⌊log₂ T⌋ + 1 = O(log x)`
(`dyadicSurvivors_card_le`).  The survivors are consecutive `i`'s; the LARGEST survivor `i*` has
`2^{i*}·(N+1) ≤ T`, so its sub-block top `X_sub = 2^{i*+1} = 2·2^{i*}` gives
`X_sub·M ≤ 2·(T/(N+1))·(2·2^k) = 4T·2^k/(N+1) ≤ 4T ≤ 4x` (using `2^k ≤ N + 1`).  So EVERY
survivor sub-box has nominal area `X_sub·M ≤ 4T ≤ 4x` — the area bound Fable's adjudication names.

### The per-survivor price and the exponent budget

For a survivor sub-box, `sum_norm_apDiscBilinCutoff_dyadic_decomp` + `subblocked_box_price` reduce
the box price to `∑_{i ∈ SurvivorSet} (per-survivor price)`.  The intended per-survivor supplier is
`GlueBV.cutoff_BV_at_op` at `(X := X_sub, M)` (via `apDiscBilinCutoff_restrict_X`, which shrinks the
`m`-summation top to the sub-block top so the price sees the reduced area `X_sub·M ≤ 4x`).  With
`O(log x)` survivors per box, `O(log x)` pieces, and `O(log x)` blocks `j`, the total is `O(log³x)`
applications each `≤ K·(4x)/(log)^A`, summing to `O(log³x)·4x/(log)^A = O(x/(log)^{A−3})`, which
clears `x/(log)^{10}` for `A ≥ 13` (the `A = 14`, `C0 = 16`, `B = 16`-family: `A + 2 = 16 ≤ C0, B`,
and `A − 3 = 11 ≥ 10`).

### ★ THE RESIDUAL GAP (catch, honest-assessed — see the closing flag) ★

`cutoff_BV_at_op` is priced by CANCELLATION on the `m`-side (`X`-side): it requires
`√x ≤ 4·X` (`GlueBV.cutoff_BV_at_op`'s `hsqrt4X`, discharged through `DivisorBound.hdiv_discharge`).
Instantiated at a survivor sub-block this reads `X_sub ≥ √x/4`.  But the largest survivor of a
piece with `p₃`-scale `N` has `X_sub ≤ 2x/(N+1)`, so `X_sub ≥ √x/4 ⟺ N ≤ 8√x − 1`.  For the
non-empty MEDIUM band `√(x/z) < N ≤ x/z²` (catch #57; `≈ (x^{0.44}, x^{0.75}]` at `z = x^{1/8}`,
so `N ≫ 8√x`) EVERY survivor sub-block has `X_sub < √x/4` and NONE is `cutoff_BV_at_op`-priceable,
even though `X_sub·M ≤ 4x` holds.  The crude count is no rescue: those boxes carry `~ x/log` triples
each, and the small sub-blocks carry a `Θ(x/log)`-share (the `∑_m T/m ≤ T` cutoff-mass), so
`|disc| ≤ count` overshoots `x/(log)^{12}`.  Morally these sub-blocks ARE priceable — by
CANCELLATION on the LONG prime side `n ∈ (N, M]` (length `~ 2^k`), not the short `m`-side — but the
landed `general_BV_cutoff_unconditional`/`DivisorBound` extracts from the `m`-side only
(`blockPrimeInd` is hardcoded in the SECOND slot; a transpose `apDiscBilinCutoff α β X Y N₀ d T =
apDiscBilinCutoff β α Y X N₀ d T` would put the prime indicator in the FIRST slot, which the
theorem does not accept).
**So the `m`-sub-blocking gives the right AREA (`X_sub·M ≤ 4x`) but not the `√X ≥ √x/4` the
`DivisorBound` discharge needs; it must be PAIRED with a long-prime-side (`√M`) BV price — a change
to the LANDED `general_BV_cutoff_unconditional`/`DivisorBound` design (Fable/design-tier).**  This
file lands the summation layer honestly (`subblocked_box_price` with the per-survivor price
ABSTRACTED); `hprice` is satisfiable by `cutoff_BV_at_op` only for the `X_sub ≥ √x/4` survivors.
`hNum_at_op` (item 4) is BLOCKED on this residual.

## What this file lands (sorry-free, axiom-clean, NEW FILE — no edits to landed files)

1. **The cutoff α-additivity** (item 1): `apDiscBilinCutoff_zero`, `_congr`, `_add_left`,
   `_sum_alpha`, `_split_threshold`, and `apDiscBilinCutoff_restrict_X` (the `X`-shrink /
   `restrictAlpha`-compatibility).
2. **The sub-box vanishing** (item 2): `apDiscBilinCutoff_eq_zero_of_over`.
3. **The sub-blocked price** (item 3, structural): `dyadicSurvivors`, `dyadicSurvivors_card_le`,
   `restrictAlpha_dyadic_sum`, `sum_norm_apDiscBilinCutoff_dyadic_decomp`, `subblocked_box_price`.
   The per-survivor analytic price stays a NAMED input (the residual gap above).
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## 1. The cutoff carrier is additive in `α` (the sub-split backbone; item 1) -/

/-- **`apDiscBilinCutoff` at the zero coefficient vanishes (FULL).** -/
theorem apDiscBilinCutoff_zero (β : ℕ → ℂ) (X Y N₀ d T : ℕ) :
    apDiscBilinCutoff (fun _ => 0) β X Y N₀ d T = 0 := by
  classical
  simp [apDiscBilinCutoff]

/-- **`apDiscBilinCutoff` depends only on `α|[1,X]` (FULL).**  The `m`-summation is over `Icc 1 X`;
two coefficients agreeing there give the same cutoff carrier.  Mirror of
`SwitchStrip.apDiscBilin_congr`; the cutoff filter `m·n ≤ T` rides through untouched. -/
theorem apDiscBilinCutoff_congr {α α' β : ℕ → ℂ} {X Y N₀ d T : ℕ}
    (h : ∀ m ∈ Finset.Icc 1 X, α m = α' m) :
    apDiscBilinCutoff α β X Y N₀ d T = apDiscBilinCutoff α' β X Y N₀ d T := by
  classical
  simp only [apDiscBilinCutoff]
  have hsum : ∀ (P : ℕ → ℕ → Prop) [∀ p q, Decidable (P p q)],
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
          (if P m n then α m * β n else 0))
        = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
          (if P m n then α' m * β n else 0)) := by
    intro P _
    refine Finset.sum_congr rfl (fun m hm => ?_)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [h m hm]
  rw [hsum (fun m n => ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d)),
    hsum (fun m n => IsUnit ((m * n : ℕ) : ZMod d))]

/-- **`apDiscBilinCutoff` is additive in `α` (FULL).**  Both the guarded residue count and the
guarded `(1/φd)`-unit main term are `∑_m α_m·(…)`, linear in `α`.  Mirror of
`SwitchStrip.apDiscBilin_add_left`. -/
theorem apDiscBilinCutoff_add_left (α₁ α₂ β : ℕ → ℂ) (X Y N₀ d T : ℕ) :
    apDiscBilinCutoff (fun m => α₁ m + α₂ m) β X Y N₀ d T
      = apDiscBilinCutoff α₁ β X Y N₀ d T + apDiscBilinCutoff α₂ β X Y N₀ d T := by
  classical
  simp only [apDiscBilinCutoff]
  have hsum : ∀ (P : ℕ → ℕ → Prop) [∀ p q, Decidable (P p q)],
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
          (if P m n then (α₁ m + α₂ m) * β n else 0))
        = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
            (if P m n then α₁ m * β n else 0))
          + (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
            (if P m n then α₂ m * β n else 0)) := by
    intro P _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    split_ifs <;> ring
  rw [hsum (fun m n => ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d)),
    hsum (fun m n => IsUnit ((m * n : ℕ) : ZMod d))]
  ring

/-- **`apDiscBilinCutoff` splits over a finite `α`-partition (FULL).**  If `α = ∑_{ℓ∈s} α ℓ`
pointwise then the cutoff carrier is `∑_{ℓ∈s} apDiscBilinCutoff (α ℓ)`.  The WBV1-carrier mirror of
`SwitchStrip.apDiscBilin_sum_alpha`: the backbone turning a dyadic `m`-partition of the box into a
coherent sum of sub-box cutoff carriers. -/
theorem apDiscBilinCutoff_sum_alpha (β : ℕ → ℂ) (X Y N₀ d T : ℕ) {ι : Type*} (s : Finset ι)
    (α : ι → ℕ → ℂ) :
    apDiscBilinCutoff (fun m => ∑ ℓ ∈ s, α ℓ m) β X Y N₀ d T
      = ∑ ℓ ∈ s, apDiscBilinCutoff (α ℓ) β X Y N₀ d T := by
  classical
  induction s using Finset.induction with
  | empty => simp [apDiscBilinCutoff_zero]
  | @insert a s ha ih =>
    have hfun : (fun m => ∑ ℓ ∈ insert a s, α ℓ m) = (fun m => α a m + ∑ ℓ ∈ s, α ℓ m) := by
      funext m; rw [Finset.sum_insert ha]
    rw [hfun, apDiscBilinCutoff_add_left, ih, Finset.sum_insert ha]

/-- **The threshold split of `apDiscBilinCutoff` (FULL).**  Splitting the `m`-block at `t` splits
the cutoff carrier into the two `restrictAlpha` sub-block terms `[1, t)` and `[t, X+1)`.  Mirror of
`SwitchStrip.apDiscBilin_split_threshold`; the `restrictAlpha`-compatibility of the cutoff carrier.
-/
theorem apDiscBilinCutoff_split_threshold (α β : ℕ → ℂ) (X Y N₀ d t T : ℕ) :
    apDiscBilinCutoff α β X Y N₀ d T
      = apDiscBilinCutoff (restrictAlpha α 1 t) β X Y N₀ d T
        + apDiscBilinCutoff (restrictAlpha α t (X + 1)) β X Y N₀ d T := by
  rw [← apDiscBilinCutoff_add_left]
  refine apDiscBilinCutoff_congr (fun m hm => ?_)
  rw [Finset.mem_Icc] at hm
  unfold restrictAlpha
  by_cases hmt : m < t
  · rw [if_pos ⟨hm.1, hmt⟩, if_neg (by omega), add_zero]
  · rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, zero_add]

/-- **The `X`-shrink / `restrictAlpha`-compatibility (FULL).**  For a coefficient supported on
`[a, b)` (`restrictAlpha α a b`), the cutoff carrier is INDEPENDENT of the `m`-summation top `X`
as soon as `X ≥ b − 1` (`hbX : b ≤ X + 1`): raising `X` to any `X' ≥ X` only adds `m ≥ b`
summands, on which the coefficient vanishes.  This lets a survivor sub-box `[2^i, 2^{i+1})` be
priced at its OWN top `X_sub = 2^{i+1} − 1` (the reduced area `X_sub·M ≤ 4T`) rather than the
global `X`. -/
theorem apDiscBilinCutoff_restrict_X {α β : ℕ → ℂ} {a b X X' Y N₀ d T : ℕ}
    (hbX : b ≤ X + 1) (hXX' : X ≤ X') :
    apDiscBilinCutoff (restrictAlpha α a b) β X' Y N₀ d T
      = apDiscBilinCutoff (restrictAlpha α a b) β X Y N₀ d T := by
  classical
  simp only [apDiscBilinCutoff]
  have hkey : ∀ (P : ℕ → ℕ → Prop) [∀ p q, Decidable (P p q)],
      (∑ m ∈ Finset.Icc 1 X', ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
          (if P m n then restrictAlpha α a b m * β n else 0))
        = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m * n ≤ T),
          (if P m n then restrictAlpha α a b m * β n else 0)) := by
    intro P _
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hXX') (fun m hm hmnot => ?_)).symm
    rw [Finset.mem_Icc] at hm hmnot
    have hz : restrictAlpha α a b m = 0 := by
      unfold restrictAlpha; rw [if_neg]; rintro ⟨_, h⟩; omega
    refine Finset.sum_eq_zero (fun n _ => ?_)
    rw [hz]; simp
  rw [hkey (fun m n => ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d)),
    hkey (fun m n => IsUnit ((m * n : ℕ) : ZMod d))]

/-! ## 2. The sub-box vanishing — the corner test at the cutoff carrier (item 2) -/

/-- **`apDiscBilinCutoff_eq_zero_of_over` (FULL — item 2).**  If the sub-box's minimal product
exceeds `T`, the cutoff carrier vanishes identically.  The coefficient `restrictAlpha α a b`
vanishes for `m < a`; `blockPrimeInd N` vanishes for `n ≤ N`.  So every nonzero summand needs
`m ≥ a` and `n ≥ N + 1`, hence `m·n ≥ a·(N+1) > T`, which the cutoff filter `m·n ≤ T` excludes.
BOTH guarded counts are empty ⟹ the cutoff disc is `0 − (1/φd)·0 = 0`.  (`a = 2^i`, the sub-block
bottom; `N + 1`, the `blockPrimeInd` support floor.) -/
theorem apDiscBilinCutoff_eq_zero_of_over {α : ℕ → ℂ} {a b N X M N₀ d T : ℕ}
    (hover : T < a * (N + 1)) :
    apDiscBilinCutoff (restrictAlpha α a b) (blockPrimeInd N) X M N₀ d T = 0 := by
  classical
  simp only [apDiscBilinCutoff]
  have hkey : ∀ (P : ℕ → ℕ → Prop) [∀ p q, Decidable (P p q)],
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T),
          (if P m n then restrictAlpha α a b m * blockPrimeInd N n else 0)) = 0 := by
    intro P _
    refine Finset.sum_eq_zero (fun m _ => ?_)
    refine Finset.sum_eq_zero (fun n hn => ?_)
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    by_cases hP : P m n
    · rw [if_pos hP]
      by_cases hma : a ≤ m ∧ m < b
      · by_cases hnb : N < n ∧ n.Prime
        · exfalso
          have hmn : a * (N + 1) ≤ m * n := Nat.mul_le_mul hma.1 (by omega)
          omega
        · unfold blockPrimeInd; rw [if_neg hnb]; ring
      · unfold restrictAlpha; rw [if_neg hma]; ring
    · rw [if_neg hP]
  rw [hkey (fun m n => ((m * n : ℕ) : ZMod d) = (N₀ : ZMod d)),
    hkey (fun m n => IsUnit ((m * n : ℕ) : ZMod d))]
  ring

/-! ## 3. The sub-blocked price — the summation layer re-organization (item 3, structural) -/

/-- **The survivor sub-block set.**  The dyadic `m`-indices `i ≤ K` whose sub-box `[2^i, 2^{i+1}) ×
(N, M]` is NOT emptied by the cutoff: `2^i·(N+1) ≤ T` (the corner test of
`apDiscBilinCutoff_eq_zero_of_over`). -/
def dyadicSurvivors (N T K : ℕ) : Finset ℕ :=
  (Finset.range (K + 1)).filter (fun i => 2 ^ i * (N + 1) ≤ T)

/-- **The survivor count is `O(log)` (FULL).**  Each survivor has `2^i ≤ 2^i·(N+1) ≤ T`, so
`dyadicSurvivors N T K ⊆ range(⌊log₂ T⌋ + 1)` and `#SurvivorSet ≤ ⌊log₂ T⌋ + 1`.  With `T ≤ x`
this is `≤ ⌊log₂ x⌋ + 1` per box — the `O(log x)` sub-boxes per `(j, piece)`. -/
theorem dyadicSurvivors_card_le (N T K : ℕ) :
    (dyadicSurvivors N T K).card ≤ Nat.log 2 T + 1 := by
  have hsub : dyadicSurvivors N T K ⊆ Finset.range (Nat.log 2 T + 1) := by
    intro i hi
    rw [dyadicSurvivors, Finset.mem_filter] at hi
    rw [Finset.mem_range]
    have h2i : 2 ^ i ≤ T := by
      have h1 : 2 ^ i * 1 ≤ 2 ^ i * (N + 1) := by gcongr; omega
      simpa using le_trans h1 hi.2
    exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by norm_num) h2i)
  calc (dyadicSurvivors N T K).card
      ≤ (Finset.range (Nat.log 2 T + 1)).card := Finset.card_le_card hsub
    _ = Nat.log 2 T + 1 := Finset.card_range _

/-- **The dyadic `m`-partition of a coefficient (FULL).**  For `1 ≤ m` with `⌊log₂ m⌋ ≤ K`, the
`K + 1` dyadic sub-block restrictions of `α` sum pointwise to `α m` — `m` lands in exactly one
block `[2^{⌊log₂ m⌋}, 2^{⌊log₂ m⌋+1})`.  The pointwise partition feeding
`apDiscBilinCutoff_sum_alpha`. -/
theorem restrictAlpha_dyadic_sum {α : ℕ → ℂ} {K m : ℕ} (hm : 1 ≤ m) (hmK : Nat.log 2 m ≤ K) :
    ∑ i ∈ Finset.range (K + 1), restrictAlpha α (2 ^ i) (2 ^ (i + 1)) m = α m := by
  classical
  rw [Finset.sum_eq_single (Nat.log 2 m)]
  · unfold restrictAlpha
    rw [if_pos ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) m⟩]
  · intro i _ hine
    unfold restrictAlpha
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hine (Nat.log_eq_of_pow_le_of_lt_pow h1 h2).symm
  · intro hmem
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hmK)) hmem

/-- **`sum_norm_apDiscBilinCutoff_dyadic_decomp` (FULL — item 3, the decomposition).**  The box's
`L¹`-over-`d` cutoff price is bounded by the sum over the `O(log)` NON-vanishing dyadic
`m`-sub-boxes of their own prices.  Chains: (1) `apDiscBilinCutoff_sum_alpha` +
`apDiscBilinCutoff_congr` splits
the box carrier into the `K + 1` sub-box carriers (partition `restrictAlpha_dyadic_sum`, valid on
`Icc 1 X` since `⌊log₂ m⌋ ≤ ⌊log₂ X⌋ ≤ K`); (2) the per-`d` triangle; (3) `Finset.sum_comm`; (4)
the non-survivor sub-boxes vanish (`apDiscBilinCutoff_eq_zero_of_over`), restricting to
`dyadicSurvivors`. -/
theorem sum_norm_apDiscBilinCutoff_dyadic_decomp {α : ℕ → ℂ} {X M N T : ℕ} (K : ℕ)
    (hK : Nat.log 2 X ≤ K) (Dset : Finset ℕ) (r : ℕ → ℕ) :
    ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
      ≤ ∑ i ∈ dyadicSurvivors N T K, ∑ d ∈ Dset,
          ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd N) X M (r d) d T‖ := by
  classical
  have hstep1 : ∀ d, apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T
      = ∑ i ∈ Finset.range (K + 1),
          apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
            (blockPrimeInd N) X M (r d) d T := by
    intro d
    rw [← apDiscBilinCutoff_sum_alpha (blockPrimeInd N) X M (r d) d T (Finset.range (K + 1))
          (fun i => restrictAlpha α (2 ^ i) (2 ^ (i + 1)))]
    refine apDiscBilinCutoff_congr (fun m hm => ?_)
    rw [Finset.mem_Icc] at hm
    exact (restrictAlpha_dyadic_sum hm.1 (le_trans (Nat.log_mono_right hm.2) hK)).symm
  calc ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
      = ∑ d ∈ Dset, ‖∑ i ∈ Finset.range (K + 1),
            apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd N) X M (r d) d T‖ := by
        refine Finset.sum_congr rfl (fun d _ => ?_); rw [hstep1 d]
    _ ≤ ∑ d ∈ Dset, ∑ i ∈ Finset.range (K + 1),
            ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd N) X M (r d) d T‖ :=
        Finset.sum_le_sum (fun d _ => norm_sum_le _ _)
    _ = ∑ i ∈ Finset.range (K + 1), ∑ d ∈ Dset,
            ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd N) X M (r d) d T‖ :=
        Finset.sum_comm
    _ = ∑ i ∈ dyadicSurvivors N T K, ∑ d ∈ Dset,
            ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
              (blockPrimeInd N) X M (r d) d T‖ := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) (fun i hi hni => ?_)).symm
        have hover : T < 2 ^ i * (N + 1) := by
          by_contra h
          exact hni (Finset.mem_filter.mpr ⟨hi, by omega⟩)
        refine Finset.sum_eq_zero (fun d _ => ?_)
        rw [apDiscBilinCutoff_eq_zero_of_over hover, norm_zero]

/-- **`subblocked_box_price` (FULL — item 3, the abstracted price).**  Given, per survivor sub-box,
a price `Price i` of its `L¹`-over-`d` cutoff carrier, the box's cutoff price is bounded by the sum
of the survivor prices.  This is the SUMMATION-layer re-organization Fable's adjudication names:
the box price is the `O(log)`-survivor sum, with each survivor's price the NAMED analytic input.
The intended supplier is `GlueBV.cutoff_BV_at_op` at `(X_sub, M)` (via
`apDiscBilinCutoff_restrict_X`);
NOTE (see the file header + closing flag) it discharges `hprice` only for the `X_sub ≥ √x/4`
survivors — the medium-band small survivors are the residual gap. -/
theorem subblocked_box_price {α : ℕ → ℂ} {X M N T : ℕ} (K : ℕ) (hK : Nat.log 2 X ≤ K)
    (Dset : Finset ℕ) (r : ℕ → ℕ) (Price : ℕ → ℝ)
    (hprice : ∀ i ∈ dyadicSurvivors N T K,
        ∑ d ∈ Dset, ‖apDiscBilinCutoff (restrictAlpha α (2 ^ i) (2 ^ (i + 1)))
          (blockPrimeInd N) X M (r d) d T‖ ≤ Price i) :
    ∑ d ∈ Dset, ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
      ≤ ∑ i ∈ dyadicSurvivors N T K, Price i :=
  le_trans (sum_norm_apDiscBilinCutoff_dyadic_decomp K hK Dset r) (Finset.sum_le_sum hprice)

/-! ## Composition sanity -/

section CompositionSanity

#check @Salt.Chen.apDiscBilinCutoff_zero
#check @Salt.Chen.apDiscBilinCutoff_congr
#check @Salt.Chen.apDiscBilinCutoff_add_left
#check @Salt.Chen.apDiscBilinCutoff_sum_alpha
#check @Salt.Chen.apDiscBilinCutoff_split_threshold
#check @Salt.Chen.apDiscBilinCutoff_restrict_X
#check @Salt.Chen.apDiscBilinCutoff_eq_zero_of_over
#check @Salt.Chen.dyadicSurvivors_card_le
#check @Salt.Chen.restrictAlpha_dyadic_sum
#check @Salt.Chen.sum_norm_apDiscBilinCutoff_dyadic_decomp
#check @Salt.Chen.subblocked_box_price
-- the intended per-survivor price supplier + the consumers the sub-blocked price feeds:
#check @Salt.Chen.cutoff_BV_at_op
#check @Salt.Chen.hHD_of_generalBV_window
#check @Salt.Chen.Plo_discharge_priced

end CompositionSanity

end Salt.Chen
