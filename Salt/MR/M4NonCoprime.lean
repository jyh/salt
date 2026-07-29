/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4WaveClosed

/-!
# ⟦R2⟧ — THE NON-COPRIME CLASSES, IN MEAN-SQUARE FORM (`M4NonCoprime`)

`M4WaveClosed`'s ⟦THE FINAL REGISTER⟧ names three residues.  ⟦R2⟧ is the second: §3's
χ-reduction (`m4_classMeanSq_of_chiMeanSq`) discharges `M4ClassBlockMeanSq` only at the
classes COPRIME to `q`, because the character expansion needs `(r,q) = 1`.  This file closes
the other half — for `d₀ = (r,q) > 1` — and hands back the FULL predicate
`M4ClassBlockMeanSq R M k Bcl`, the shape `m4_blockMeanSqSupQ_of_classMeanSq` consumes.

## ⟦THE TRANSPORT⟧ — one dilation, then a `d₀`-to-one re-index of the BLOCK

`M4ClassPrice` §3's `norm_sum_windowClass_memS_dilate` is an **equality** at the residual
frequency `0`: the class `r` mod `q` of the window `(n, n+K]` IS the class `r₀ = r/d₀` mod
`q₀ = q/d₀` of the dilated window `(n/d₀, n/d₀ + dilLen K n d₀]`, at the same sieved datum.
Nothing is estimated by it.  In mean-square form the transport is taken pointwise in the
door index `n`, and then the BLOCK is re-indexed by the same map `n ↦ n/d₀`:

```
   ∑_{n ∈ (A, B]} classSup(H, n, q, r)²
     ≤ ∑_{n ∈ (A, B]} classSup(H', n/d₀, q₀, r₀)²      (§4, the pointwise transport)
     ≤ d₀ · ∑_{n' ∈ (A', B']} classSup(H', n', q₀, r₀)² (§1, the FIBRE COUNT — exact)
     ≤ d₀ · (B_cl H · H'² · A')                        (the coprime datum at (q₀, r₀))
     ≤ B_cl H · H² · A                                 (§3, THE d₀-LEDGER)
```

with `H' = ⌊H/d₀⌋ + 1` (the uniform dilated length: `dilLen K n d₀ ≤ ⌊K/d₀⌋ + 1 ≤ H'` for
every `K ≤ H`, `M4BridgeDilate.dilLen_le`), `A' = ⌊A/d₀⌋ − 1` and `B' = ⌊B/d₀⌋`.

## ⟦THE d₀-LEDGER⟧ (§3, symbolic — `d0_ledger`, `d0_ledger_sharp`)

The composed grade is **identical** to the coprime half's: no `d₀`-power is spent and none is
demanded.  Written out, with `A` the block bottom:

* the fibre map `n ↦ ⌊n/d₀⌋` is `d₀`-to-one, so the block sum costs a factor `d₀`;
* the dilated block's bottom is `A' = ⌊A/d₀⌋ − 1`, and `d₀·A' ≤ d₀·⌊A/d₀⌋ ≤ A` — an
  identity-grade inequality.  **The fibre factor `d₀` is paid EXACTLY by the dilated block's
  bottom, and by nothing else.**
* the window shrink `H ↦ H' = ⌊H/d₀⌋ + 1` is therefore pure profit, and is BANKED UNSPENT:
  the composition uses only `H' ≤ H` (`d0_ledger`).  Sharply (`d0_ledger_sharp`)

  ```
     d₀ · (B_cl · H'² · A')  ≤  B_cl · (H + d₀)² · A / d₀²
                             =  (B_cl · H² · A) · (1 + d₀/H)² / d₀² ,
  ```

  i.e. a full factor `d₀²/(1 + d₀/H)² ≥ 1` of headroom (`≥ 16/9` already at `d₀ = 2`,
  `d₀ ≤ H/2`) that the ledger does not need.  Nothing here has to close "by half an
  exponent": it closes on the nose, with `d₀²` to spare.

So the `q²` slot `M4ClassPrice` §4 opened is untouched: the split's loss is still exactly the
class count `q`, and ⟦R2⟧ contributes no factor at all.

## ⟦THE INTERFACE⟧ — `M4CoprimeBlockMeanSq`, the interval-general coprime family

The dilated block `(⌊A/d₀⌋ − 1, ⌊B/d₀⌋]` is **not** a `doorLadder` block — this is `M4Join`'s
⟦THE CLASS PRICING⟧ obstruction in its surviving, mean-square form.  So the coprime datum
this file consumes is stated at a FREE half-open interval `(A, B]` and a FREE window length
`L ≤ H`, exactly the shape `M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le` (whose `A`, `B`
and scale `X` are already free) delivers once its fit holds — and the fit is stated with
`M4ClassPrice` §5's endpoint slack, because the dilated block misses the tight
`doorLadder_fit` by a bounded amount:

* §5's `dilBlock_fit_slack` costs `3` (the honest slack is `2`);
* the re-index spends one further unit at each end — the bottom's `⌊A/d₀⌋ − 1` and the
  length's `⌊H/d₀⌋ + 1` — so the interface is stated at `B + L ≤ 2A + 4`
  (`dilBlock_reindex_fit`, §2, proved here).  `sum_Ioc_absWindowSum_sq_div_le_dropped` is the
  supplier: it is `sum_Ioc_drop_top` with `3` dropped indices; slack `4` is the same lemma
  with one more index dropped, at the same negligible `H²/X` per index.

`m4_coprimeBlockMeanSq_trivial` is the anti-vacuity witness (the house's duty): at the
trivial grade `5` the predicate holds outright, so all of its content is the grade.

## ⟦THE TWO GATES THIS FILE ADDS⟧ (both REGIME/SCALE, class (a) of ⟦THE FINAL REGISTER⟧)

Both are `H`-only, `X`-free thresholds on the window range — the class the S11 spine's
`g`-arm absorbs:

1. `hlogcap` — `log H ≤ 2^{21845}`, the dilation's own gate
   (`M4Residue`: `12·21845 = 262140 < 262144`), carried verbatim by
   `M4ClassPrice.norm_sum_windowClass_memS_dilate`.  Nothing new: every consumer of the
   dilation pays it.
2. `harc` — `2·arcDen 12 H ≤ H`, i.e. `2(log H)^{12} ≤ H`.  This is what makes the re-index
   non-degenerate: it gives `2d₀ ≤ 2q ≤ H < A`, hence `⌊A/d₀⌋ ≥ 2` and `A' ≥ 1`.  It is
   forced by the arc setup itself — `MinorArcExit` DERIVES `arcDen B₅ H ≤ H` from the mere
   existence of a large Dirichlet denominator (`hdenH`), so a major/minor split at `arcDen`
   is empty without it.

## ⟦THE TRAPS RESPECTED⟧

* **the four log scales** — this file writes `log H` only (through `arcDen 12 H` and the
  dilation's `2^{21845}` gate); no `log X`, no `log log`, and `arcDen` is never evaluated;
* **ℕ-division fibres** — the fibre of `n ↦ ⌊n/d₀⌋` over `n'` is contained in
  `[d₀n', d₀n' + d₀)` and so has card `≤ d₀` EXACTLY (`card_fibre_div_le`, from
  `Nat.div_add_mod` — no ± slack is guessed).  The image of `(A, B]` is `[⌊A/d₀⌋, ⌊B/d₀⌋]`,
  a CLOSED interval — the bottom index is hit — which is why the target block is
  `(⌊A/d₀⌋ − 1, ⌊B/d₀⌋]` and why `⌊A/d₀⌋ ≥ 1` is needed (gate 2);
* **the frequency-0 pin** — the dilation is taken at the residual frequency `d₀·0 = 0`, so no
  arc datum is transported and the enlarged cap `arcDen·(H+d₀)/H` is never incurred.  No
  `NearRatTight` hypothesis appears anywhere below;
* **strict gates** — `0 < q`, `0 < d₀`, `2 ≤ d₀` on the non-coprime branch, `R.Hlo ≤ H ≤
  R.Hhi`, `0 < A` are carried, never weakened;
* **half-open** — every window is `Finset.Ioc n (n+K)` (through `windowClass`), every block
  and every dilated block is `Finset.Ioc A B`.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE FIBRE COUNT (ℕ-division, exact)

`n ↦ ⌊n/d⌋` is `d`-to-one: its fibre over `n'` is exactly `[d·n', d·n' + d)`.  Both lemmas
below are pure `Nat` bookkeeping — no arithmetic about the summand at all. -/

/-- **THE EXACT FIBRE CARD.**  At most `d` indices of any interval share a value of
`n ↦ ⌊n/d⌋`.  Route: `Nat.div_add_mod` places the fibre inside `[d·n', d·n' + d)`. -/
theorem card_fibre_div_le {A B d : ℕ} (hd : 0 < d) (n' : ℕ) :
    ((Finset.Ioc A B).filter (fun n => n / d = n')).card ≤ d := by
  have hsub : ((Finset.Ioc A B).filter (fun n => n / d = n'))
      ⊆ Finset.Ico (d * n') (d * n' + d) := by
    intro n hn
    have hdiv : n / d = n' := (Finset.mem_filter.mp hn).2
    have hmod : d * (n / d) + n % d = n := Nat.div_add_mod n d
    rw [hdiv] at hmod
    have hlt : n % d < d := Nat.mod_lt _ hd
    rw [Finset.mem_Ico]
    constructor
    · omega
    · omega
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Nat.card_Ico]
  omega

/-- **THE FIBRE SUM.**  A nonnegative summand read at `⌊n/d⌋` over a block is under `d` times
its sum over any interval the map lands in.  This is the mean-square form of the `d₀`-to-one
re-index; `Finset.sum_fiberwise_of_maps_to` does the partition, `card_fibre_div_le` the
count. -/
theorem sum_Ioc_comp_div_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {A B A' B' d : ℕ} (hd : 0 < d)
    (hmaps : ∀ n ∈ Finset.Ioc A B, n / d ∈ Finset.Ioc A' B') :
    ∑ n ∈ Finset.Ioc A B, f (n / d) ≤ (d : ℝ) * ∑ n' ∈ Finset.Ioc A' B', f n' := by
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => f (n / d)), Finset.mul_sum]
  refine Finset.sum_le_sum fun n' _ => ?_
  have hcong : ∑ n ∈ (Finset.Ioc A B).filter (fun n => n / d = n'), f (n / d)
      = (((Finset.Ioc A B).filter (fun n => n / d = n')).card : ℝ) * f n' := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl fun n hn => by rw [(Finset.mem_filter.mp hn).2]
  rw [hcong]
  refine mul_le_mul_of_nonneg_right ?_ (hf n')
  exact_mod_cast card_fibre_div_le hd n'

/-! ## §2 — THE RE-INDEXED BLOCK: where it lands, and its fit

The image of the half-open block `(A, B]` under `n ↦ ⌊n/d⌋` is the CLOSED interval
`[⌊A/d⌋, ⌊B/d⌋]` — the bottom index IS hit (take `A = 4`, `d = 3`, `n = 5`).  Written
half-open, that is `(⌊A/d⌋ − 1, ⌊B/d⌋]`, and the `−1` is legitimate exactly when
`⌊A/d⌋ ≥ 1`, i.e. `d ≤ A`. -/

private lemma two_mul_lt {e d : ℕ} (h : e < d) : 2 * e < 2 * d := by omega

private lemma add_le_of_lt_two {u v : ℕ} (h : v < 2) : u + v ≤ u + 1 := by omega

private lemma fit_arith {a b h : ℕ} (h1 : 1 ≤ a) (hkey : b + h ≤ 2 * a + 1) :
    b + (h + 1) ≤ 2 * (a - 1) + 4 := by omega

/-- Doubling costs at most `1` to the floor: `⌊2A/d⌋ ≤ 2⌊A/d⌋ + 1` (the `2`-analogue of
`M4ClassPrice.three_mul_div_le`). -/
theorem two_mul_div_le (A : ℕ) {d : ℕ} (hd : 0 < d) : 2 * A / d ≤ 2 * (A / d) + 1 := by
  have hAd : A = d * (A / d) + A % d := (Nat.div_add_mod A d).symm
  have hdec : 2 * A = d * (2 * (A / d)) + 2 * (A % d) :=
    calc 2 * A = 2 * (d * (A / d) + A % d) := by rw [← hAd]
      _ = d * (2 * (A / d)) + 2 * (A % d) := by ring
  have hmod : A % d < d := Nat.mod_lt _ hd
  have hlt : 2 * (A % d) / d < 2 := by
    rw [Nat.div_lt_iff_lt_mul hd]
    exact two_mul_lt hmod
  rw [hdec, Nat.mul_add_div hd]
  exact add_le_of_lt_two hlt

/-- **WHERE THE RE-INDEX LANDS.**  For `d ≤ A`, the block `(A, B]` maps into the half-open
dilated block `(⌊A/d⌋ − 1, ⌊B/d⌋]`. -/
theorem div_mem_reindexed {A B d n : ℕ} (hd : 0 < d) (hdA : d ≤ A)
    (hn : n ∈ Finset.Ioc A B) : n / d ∈ Finset.Ioc (A / d - 1) (B / d) := by
  rw [Finset.mem_Ioc] at hn ⊢
  have h1 : 1 ≤ A / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  have hAn : A / d ≤ n / d := Nat.div_le_div_right hn.1.le
  exact ⟨by omega, Nat.div_le_div_right hn.2⟩

/-- **THE RE-INDEXED BLOCK'S FIT**, at the uniform dilated length `⌊H/d⌋ + 1`.  Against the
TIGHT `doorLadder_fit` `B + H ≤ 2A` the re-indexed block misses by at most `4`:

```
   ⌊B/d⌋ + (⌊H/d⌋ + 1)  ≤  2(⌊A/d⌋ − 1) + 4 .
```

`M4ClassPrice` §5's `dilBlock_fit_slack` is the same computation at slack `3`, at the
`n`-dependent length `dilLen H A d`; the extra unit here is the price of the two uniform
endpoints (the length's `+1`, the bottom's `−1`).  Every step is a floor identity:
`⌊u/d⌋ + ⌊v/d⌋ ≤ ⌊(u+v)/d⌋`, then `two_mul_div_le`. -/
theorem dilBlock_reindex_fit {A B H d : ℕ} (hd : 0 < d) (hdA : d ≤ A)
    (hfit : B + H ≤ 2 * A) : B / d + (H / d + 1) ≤ 2 * (A / d - 1) + 4 := by
  have h1 : 1 ≤ A / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  have hbh : B / d + H / d ≤ (B + H) / d := div_add_div_le_add_div B H hd
  have hle : (B + H) / d ≤ 2 * A / d := Nat.div_le_div_right hfit
  have h2 : 2 * A / d ≤ 2 * (A / d) + 1 := two_mul_div_le A hd
  exact fit_arith h1 (le_trans (le_trans hbh hle) h2)

/-! ## §3 — THE `d₀`-LEDGER (symbolic)

The fibre factor `d₀` against the dilated block's bottom, and the window shrink banked
unspent.  Both statements are grade-generic: `B_cl` enters only as a nonnegative real. -/

/-- **THE LEDGER, as the composition spends it.**  `d₀·(B·H'²·A') ≤ B·H²·A` at
`H' = ⌊H/d₀⌋ + 1 ≤ H` and `A' = ⌊A/d₀⌋ − 1`.  The whole `d₀` is paid by
`d₀·(⌊A/d₀⌋ − 1) ≤ d₀·⌊A/d₀⌋ ≤ A`; the window shrink is not spent. -/
theorem d0_ledger {A H d : ℕ} (hd : 0 < d) (hHH : H / d + 1 ≤ H) {Bc : ℝ} (hBc : 0 ≤ Bc) :
    (d : ℝ) * (Bc * ((H / d + 1 : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ))
      ≤ Bc * (H : ℝ) ^ 2 * (A : ℝ) := by
  have hdA : (d : ℝ) * ((A / d - 1 : ℕ) : ℝ) ≤ (A : ℝ) := by
    have hn : d * (A / d - 1) ≤ A := by
      have h1 : d * (A / d - 1) ≤ d * (A / d) := Nat.mul_le_mul le_rfl (Nat.sub_le _ _)
      have h2 : d * (A / d) ≤ A := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self A d
      exact h1.trans h2
    exact_mod_cast hn
  have hH' : ((H / d + 1 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHH
  have hH'0 : (0 : ℝ) ≤ ((H / d + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : ((H / d + 1 : ℕ) : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 := by nlinarith
  have hA'0 : (0 : ℝ) ≤ (d : ℝ) * ((A / d - 1 : ℕ) : ℝ) := by positivity
  calc (d : ℝ) * (Bc * ((H / d + 1 : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ))
      = Bc * ((H / d + 1 : ℕ) : ℝ) ^ 2 * ((d : ℝ) * ((A / d - 1 : ℕ) : ℝ)) := by ring
    _ ≤ Bc * (H : ℝ) ^ 2 * (A : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsq hBc) hdA hA'0
          (mul_nonneg hBc (sq_nonneg _))

/-- **THE LEDGER, SHARP** — what the transport actually delivers, stated once so the banked
profit is on the record:

```
   d₀ · (B·H'²·A')  ≤  B · (H + d₀)² · A / d₀²  =  (B·H²·A) · (1 + d₀/H)²/d₀² .
```

At `2 ≤ d₀ ≤ H/2` the factor `(1 + d₀/H)²/d₀² ≤ (5/4)²/4 < 1/2`: the composition above throws
away a factor `≥ 2`, and at large `d₀` a factor `≍ d₀²`.  Nothing in the M4 budget needs it,
so `d0_ledger` — not this — is what `m4_nonCoprime_classMeanSq` uses. -/
theorem d0_ledger_sharp {A H d : ℕ} (hd : 0 < d) {Bc : ℝ} (hBc : 0 ≤ Bc) :
    (d : ℝ) * (Bc * ((H / d + 1 : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ))
      ≤ Bc * ((H : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hH' : ((H / d + 1 : ℕ) : ℝ) ≤ ((H : ℝ) + (d : ℝ)) / (d : ℝ) := by
    have h := Nat.cast_div_le (α := ℝ) (m := H) (n := d)
    have heq : ((H : ℝ) + (d : ℝ)) / (d : ℝ) = (H : ℝ) / (d : ℝ) + 1 := by
      field_simp
    rw [heq]
    push_cast
    linarith
  have hA' : ((A / d - 1 : ℕ) : ℝ) ≤ (A : ℝ) / (d : ℝ) := by
    have h1 : ((A / d - 1 : ℕ) : ℝ) ≤ ((A / d : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le (A / d) 1
    exact h1.trans (Nat.cast_div_le (α := ℝ))
  have hH'0 : (0 : ℝ) ≤ ((H / d + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA'0 : (0 : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : ((H / d + 1 : ℕ) : ℝ) ^ 2 ≤ (((H : ℝ) + (d : ℝ)) / (d : ℝ)) ^ 2 := by nlinarith
  have hstep : Bc * ((H / d + 1 : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ)
      ≤ Bc * (((H : ℝ) + (d : ℝ)) / (d : ℝ)) ^ 2 * ((A : ℝ) / (d : ℝ)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hsq hBc) hA' hA'0
      (mul_nonneg hBc (sq_nonneg _))
  calc (d : ℝ) * (Bc * ((H / d + 1 : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ))
      ≤ (d : ℝ) * (Bc * (((H : ℝ) + (d : ℝ)) / (d : ℝ)) ^ 2 * ((A : ℝ) / (d : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep hd0.le
    _ = Bc * ((H : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2 := by
        field_simp

/-! ## §4 — THE POINTWISE TRANSPORT

`M4ClassPrice.norm_sum_windowClass_memS_dilate` at every sub-window length `K ≤ H`, then the
sup re-read at the uniform dilated length `⌊H/d₀⌋ + 1`.  The transport is an EQUALITY; the
only inequality spent is the enlargement of the sup's length range, and
`dilLen K n d₀ ≤ ⌊K/d₀⌋ + 1 ≤ ⌊H/d₀⌋ + 1` makes it legitimate. -/

/-- The class sup is monotone in its window length (a sup over a longer `Icc 0 ·`). -/
theorem classSup_mono_len (a : ℕ → ℂ) (n q r : ℕ) {L H : ℕ} (h : L ≤ H) :
    classSup a L n q r ≤ classSup a H n q r :=
  classSup_le fun _K hK => le_classSup a H n q r (hK.trans h)

/-- **THE POINTWISE TRANSPORT.**  The class sup at `(q, r)` and base `n` is under the class
sup at the reduced pair `(q/d₀, r/d₀)` and base `⌊n/d₀⌋`, read at the uniform dilated length
`⌊H/d₀⌋ + 1`.  Loss-free at every length: the underlying step is the equality of
`M4ClassPrice` §3, taken at the residual frequency `0` (no arc datum, hence no enlarged
cap). -/
theorem classSup_le_dilate {M H q r n : ℕ} (hM : 1 ≤ M) (hq : 0 < q)
    (h1 : 1 ≤ Real.log (H : ℝ)) (h2 : Real.log (H : ℝ) ≤ (2 : ℝ) ^ (21845 : ℕ))
    (hqW : (q : ℝ) ≤ Real.log (H : ℝ) ^ (12 : ℕ)) :
    classSup (doorSievedCoeff M) H n q r
      ≤ classSup (doorSievedCoeff M) (H / Nat.gcd r q + 1) (n / Nat.gcd r q)
          (q / Nat.gcd r q) (r / Nat.gcd r q) := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  refine classSup_le fun K hK => ?_
  have heq := norm_sum_windowClass_memS_dilate (M := M) (J := 2) (q := q) (r := r)
    (H := K) (n := n) (Hr := (H : ℝ)) hM hq h1 h2 hqW
  have hlen : dilLen K n (Nat.gcd r q) ≤ H / Nat.gcd r q + 1 :=
    le_trans (dilLen_le K n hd) (Nat.add_le_add_right (Nat.div_le_div_right hK) 1)
  simp only [doorSievedCoeff]
  rw [heq]
  exact le_classSup _ _ _ _ _ hlen

/-! ## §5 — THE COPRIME FAMILY, AND ⟦R2⟧ CLOSED

The interval-general coprime datum, and the theorem that turns it into `M4ClassBlockMeanSq`
at EVERY class of `q`. -/

/-- **THE COPRIME FAMILY** (the interval-general, length-general coprime block mean square).

Three generalisations against `M4WaveClosed.M4ClassBlockMeanSq`, each forced by the
re-index and by nothing else:

* the block is a FREE half-open interval `(A, B]` with `0 < A` — the dilated block is not a
  `doorLadder` block;
* the window length is a FREE `L ≤ H`, priced at its OWN `L²` — the dilated window has
  length `≈ H/d₀`;
* the fit carries `M4ClassPrice` §5's endpoint slack, at `4` (see `dilBlock_reindex_fit`).

The modulus range is unchanged (`0 < q'`, `q' ≤ arcDen 12 H`), and it covers every reduced
modulus `q₀ = q/d₀ ≤ q` the transport can produce — this is the "at all `q' ≤ q`" of the
freeze.  The grade is read at the AMBIENT `H`, so no monotonicity of `B_cl` is assumed
anywhere. -/
def M4CoprimeBlockMeanSq (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H → ∀ r, r < q → Nat.Coprime q r →
      ∀ A B : ℕ, 0 < A → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff M) L n q r) ^ 2
          ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-- **THE ANTI-VACUITY WITNESS** (the house's duty, mirroring
`M4WaveClosed.m4_classBlockMeanSq_trivial`).  At the trivial grade `5` the predicate holds
outright: each class sup is `≤ L`, and the fit plus `0 < A` bound the block's cardinality by
`5A`.  So the interface is not satisfiable-by-nobody — ALL of its content is the grade. -/
theorem m4_coprimeBlockMeanSq_trivial (R : ChowlaRegime) (M : ℕ) :
    M4CoprimeBlockMeanSq R M (fun _ => 5) := by
  intro _ _ _ L _ q _ _ r _ _ A B hA hfit
  have hterm : ∀ n ∈ Finset.Ioc A B,
      (classSup (doorSievedCoeff M) L n q r) ^ 2 ≤ (L : ℝ) ^ 2 := by
    intro n _
    have h := classSup_le_of_norm_le_one (norm_doorSievedCoeff_le_one M) L n q r
    have h0 := classSup_nonneg (doorSievedCoeff M) L n q r
    nlinarith
  have hsum : ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff M) L n q r) ^ 2
      ≤ ((Finset.Ioc A B).card : ℝ) * (L : ℝ) ^ 2 := by
    calc ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff M) L n q r) ^ 2
        ≤ ∑ _n ∈ Finset.Ioc A B, (L : ℝ) ^ 2 := Finset.sum_le_sum hterm
      _ = ((Finset.Ioc A B).card : ℝ) * (L : ℝ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc A B).card : ℝ) ≤ 5 * (A : ℝ) := by
    rw [Nat.card_Ioc]
    have hn : B - A ≤ 5 * A := by omega
    exact_mod_cast hn
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := sq_nonneg _
  nlinarith

/-- **⟦R2⟧ — `m4_nonCoprime_classMeanSq`.**  The coprime family gives `M4ClassBlockMeanSq` at
EVERY class of `q`, at the SAME grade:

* `d₀ = (r,q) = 1` — the datum is read at `L = H`, `(A, B] = ` the door block, verbatim
  (the door block's `doorLadder_fit` is the interface's fit with slack to spare);
* `d₀ > 1` — the pointwise transport (§4), the `d₀`-to-one fibre count (§1) onto the
  re-indexed block (§2), the datum at `(q/d₀, r/d₀)`, and ⟦THE d₀-LEDGER⟧ (§3).

**No loss.**  The output grade is `B_cl H · H² · X_{i+1}`, identical to the coprime half's,
so the `q²` slot `M4ClassPrice` §4 opened is untouched and the composed drift price is
unchanged.  The two added hypotheses are the module header's ⟦THE TWO GATES⟧ — both
`H`-only regime thresholds of ⟦THE FINAL REGISTER⟧'s class (a). -/
theorem m4_nonCoprime_classMeanSq {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hlogcap : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.log (H : ℝ) ≤ (2 : ℝ) ^ (21845 : ℕ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ))
    (hcp : M4CoprimeBlockMeanSq R M Bcl) :
    M4ClassBlockMeanSq R M k Bcl := by
  intro H hlo hhi q hq hqQ i _ r hrq
  -- ⟦the block, and the ladder's two facts⟧
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the datum, read at the door block
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]; exact hcase
    exact hcp H hlo hhi H le_rfl q hq hqQ r hrq hcopqr
      (doorLadder R.x H (i + 1)) (doorLadder R.x H i) hApos (by omega)
  · -- ⟦d₀ > 1⟧ ONE dilation, then the `d₀`-to-one re-index of the block
    have hd2 : 2 ≤ Nat.gcd r q := by omega
    -- ⟦the modulus gates⟧
    have hdq : Nat.gcd r q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)
    have h2q : 2 * q ≤ H := by
      have hR : ((2 * q : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hdA : Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hdA2 : 2 * Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / Nat.gcd r q :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hA'pos : 0 < doorLadder R.x H (i + 1) / Nat.gcd r q - 1 := by omega
    -- ⟦the reduced pair⟧
    have hq₀ : 0 < q / Nat.gcd r q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)) hd
    have hq₀Q : ((q / Nat.gcd r q : ℕ) : ℝ) ≤ arcDen 12 H := by
      refine le_trans ?_ hqQ
      exact_mod_cast Nat.div_le_self q (Nat.gcd r q)
    have hr₀q₀ : r / Nat.gcd r q < q / Nat.gcd r q := by
      rcases Nat.lt_or_ge (r / Nat.gcd r q) (q / Nat.gcd r q) with hlt | hcon
      · exact hlt
      refine absurd hrq (not_lt.mpr ?_)
      have hqd : Nat.gcd r q * (q / Nat.gcd r q) = q :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right r q)
      have h1 : Nat.gcd r q * (q / Nat.gcd r q)
          ≤ Nat.gcd r q * (r / Nat.gcd r q) := Nat.mul_le_mul le_rfl hcon
      have h2 : Nat.gcd r q * (r / Nat.gcd r q) ≤ r := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self r (Nat.gcd r q)
      rw [← hqd]
      exact h1.trans h2
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    -- ⟦the dilated window length⟧
    have hH'H : H / Nat.gcd r q + 1 ≤ H := by
      have hstep : H / Nat.gcd r q ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    -- ⟦the dilation's own gates⟧
    have hL1 : (1 : ℝ) ≤ Real.log (H : ℝ) := by
      have hLexp : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
      have he : (1 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      linarith
    have harcnp : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
      rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hqW : (q : ℝ) ≤ Real.log (H : ℝ) ^ (12 : ℕ) := by rw [← harcnp]; exact hqQ
    -- ⟦the pointwise transport, then the fibre count, then the datum, then the ledger⟧
    have hpt : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff M) H n q r) ^ 2
          ≤ (fun n' => (classSup (doorSievedCoeff M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2) (n / Nat.gcd r q) := by
      intro n _
      have hle := classSup_le_dilate (M := M) (H := H) (q := q) (r := r) (n := n)
        hM hq hL1 (hlogcap H hlo hhi) hqW
      have h0 := classSup_nonneg (doorSievedCoeff M) H n q r
      simp only
      nlinarith
    have hmaps : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        n / Nat.gcd r q ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
          (doorLadder R.x H i / Nat.gcd r q) := fun n hn => div_mem_reindexed hd hdA hn
    have hdatum := hcp H hlo hhi (H / Nat.gcd r q + 1) hH'H (q / Nat.gcd r q) hq₀ hq₀Q
      (r / Nat.gcd r q) hr₀q₀ hcop₀ (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
      (doorLadder R.x H i / Nat.gcd r q) hA'pos (dilBlock_reindex_fit hd hdA hfit)
    have hd0R : (0 : ℝ) ≤ (Nat.gcd r q : ℝ) := Nat.cast_nonneg _
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff M) H n q r) ^ 2
        ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) (H / Nat.gcd r q + 1) (n / Nat.gcd r q)
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 := Finset.sum_le_sum hpt
      _ ≤ (Nat.gcd r q : ℝ)
            * ∑ n' ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
                (doorLadder R.x H i / Nat.gcd r q),
              (classSup (doorSievedCoeff M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 :=
          sum_Ioc_comp_div_le
            (f := fun n' => (classSup (doorSievedCoeff M) (H / Nat.gcd r q + 1) n'
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2)
            (fun _ => sq_nonneg _) (d := Nat.gcd r q) hd hmaps
      _ ≤ (Nat.gcd r q : ℝ)
            * (Bcl H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) ^ 2
                * ((doorLadder R.x H (i + 1) / Nat.gcd r q - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdatum hd0R
      _ ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) :=
          d0_ledger hd hH'H (hBcl0 H)

/-! ## §6 — ⟦THE NARROWED TWIN⟧ (`M4CoprimeBlockMeanSqN`)

⟦COPRIME-SCOPE⟧'s finding: `M4CoprimeBlockMeanSq` as stated above is **over-general** — its
grade's small-length summand is off by `H/L` for ANY route, unconditionally, so no supplier
can meet it at a free `L`.  Iron rule 1 keeps the interface standing (it is load-bearing in
the landed close); this section lands the twin BESIDE it, with **one** hypothesis added:

  `(H : ℝ) ≤ arcDen 12 H · L`   — ⟦THE NARROWING⟧,

i.e. the free window length is at least `H/(log H)^{12}`.  Nothing else moves: the block is
still free, the modulus range is still the arc's, and the grade slot is still read at the
ambient `H`, so `d0_ledger` is untouched and the register's lines do not move.

⟦WHY IT COSTS NOTHING⟧ the twin's two consumption sites — `m4_nonCoprime_classMeanSq_N`
below — are the ONLY places the interface is read, and at both the narrowing is DISCHARGED
from facts already in scope:

* the coprime branch reads `L = H`, where the narrowing is `1 ≤ arcDen 12 H`, i.e.
  `1 ≤ log H`, which is `M4Close.exp_one_le_log_of_regime_le`;
* the dilated branch reads `L = ⌊H/d₀⌋ + 1`, where `d₀·L ≥ H` is ℕ-division and
  `d₀ ≤ q ≤ arcDen 12 H` is the modulus gate.

So no consumer pays for the narrowing, and a supplier may use it. -/

/-- **THE NARROWED COPRIME FAMILY** (`M4CoprimeBlockMeanSqN`) — `M4CoprimeBlockMeanSq` with
⟦THE NARROWING⟧ `(H : ℝ) ≤ arcDen 12 H · L` inserted directly after `L ≤ H`, and NOTHING
else changed.  Strictly weaker as a hypothesis on a supplier, strictly stronger as a demand
on a consumer — and `m4_nonCoprime_classMeanSq_N` shows the demand is free. -/
def M4CoprimeBlockMeanSqN (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → (H : ℝ) ≤ arcDen 12 H * (L : ℝ) →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H → ∀ r, r < q → Nat.Coprime q r →
      ∀ A B : ℕ, 0 < A → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff M) L n q r) ^ 2
          ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-- The narrowed family is implied by the full one — the twin adds a hypothesis and nothing
else, so any supplier of the (unattainable) general interface supplies this one too. -/
theorem m4_coprimeBlockMeanSqN_of_full {R : ChowlaRegime} {M : ℕ} {Bcl : ℕ → ℝ}
    (h : M4CoprimeBlockMeanSq R M Bcl) : M4CoprimeBlockMeanSqN R M Bcl :=
  fun H hlo hhi L hLH _ q hq hqQ r hrq hcop A B hA hfit =>
    h H hlo hhi L hLH q hq hqQ r hrq hcop A B hA hfit

/-- **THE ANTI-VACUITY WITNESS** for the twin, at the trivial grade `5` — the house's duty
carried over from `m4_coprimeBlockMeanSq_trivial`. -/
theorem m4_coprimeBlockMeanSqN_trivial (R : ChowlaRegime) (M : ℕ) :
    M4CoprimeBlockMeanSqN R M (fun _ => 5) :=
  m4_coprimeBlockMeanSqN_of_full (m4_coprimeBlockMeanSq_trivial R M)

/-- `1 ≤ arcDen 12 H` past the regime's window floor: `arcDen` is a POSITIVE power of
`log H`, and `e ≤ log H` there (`M4Close.exp_one_le_log_of_regime_le`).  Named once — both
narrowing discharges below and every supplier's regime step read it. -/
theorem one_le_arcDen_of_regime {R : ChowlaRegime} {H : ℕ} (hlo : R.Hlo ≤ H) :
    (1 : ℝ) ≤ arcDen 12 H := by
  have hLexp : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
  have he : (1 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hL1 : (1 : ℝ) ≤ Real.log (H : ℝ) := le_trans he.le hLexp
  have harcnp : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [harcnp]
  exact one_le_pow₀ hL1

/-- **⟦R2⟧, AT THE NARROWED TWIN** (`m4_nonCoprime_classMeanSq_N`).  Byte-for-byte
`m4_nonCoprime_classMeanSq` with its coprime datum read at `M4CoprimeBlockMeanSqN`: the SAME
hypothesis list, the SAME conclusion `M4ClassBlockMeanSq R M k Bcl`, the SAME grade — the
narrowing is discharged inside, at each of the two sites, from facts the proof already had.

* `d₀ = 1`, `L = H`: `(H:ℝ) ≤ arcDen 12 H · H` is `one_le_arcDen_of_regime`;
* `d₀ > 1`, `L = ⌊H/d₀⌋ + 1`: `H ≤ d₀·L` is `Nat.div_add_mod` + `Nat.mod_lt`, and
  `d₀ ≤ q ≤ arcDen 12 H` is `Nat.gcd_dvd_right` + the modulus gate. -/
theorem m4_nonCoprime_classMeanSq_N {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hlogcap : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.log (H : ℝ) ≤ (2 : ℝ) ^ (21845 : ℕ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ))
    (hcp : M4CoprimeBlockMeanSqN R M Bcl) :
    M4ClassBlockMeanSq R M k Bcl := by
  intro H hlo hhi q hq hqQ i _ r hrq
  -- ⟦the block, and the ladder's two facts⟧
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hH0R : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the datum, read at the door block, `L = H`
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]; exact hcase
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * (H : ℝ) := by nlinarith
    exact hcp H hlo hhi H le_rfl hnarrow q hq hqQ r hrq hcopqr
      (doorLadder R.x H (i + 1)) (doorLadder R.x H i) hApos (by omega)
  · -- ⟦d₀ > 1⟧ ONE dilation, then the `d₀`-to-one re-index of the block
    have hd2 : 2 ≤ Nat.gcd r q := by omega
    -- ⟦the modulus gates⟧
    have hdq : Nat.gcd r q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)
    have h2q : 2 * q ≤ H := by
      have hR : ((2 * q : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hdA : Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hdA2 : 2 * Nat.gcd r q ≤ doorLadder R.x H (i + 1) := by omega
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / Nat.gcd r q :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hA'pos : 0 < doorLadder R.x H (i + 1) / Nat.gcd r q - 1 := by omega
    -- ⟦the reduced pair⟧
    have hq₀ : 0 < q / Nat.gcd r q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)) hd
    have hq₀Q : ((q / Nat.gcd r q : ℕ) : ℝ) ≤ arcDen 12 H := by
      refine le_trans ?_ hqQ
      exact_mod_cast Nat.div_le_self q (Nat.gcd r q)
    have hr₀q₀ : r / Nat.gcd r q < q / Nat.gcd r q := by
      rcases Nat.lt_or_ge (r / Nat.gcd r q) (q / Nat.gcd r q) with hlt | hcon
      · exact hlt
      refine absurd hrq (not_lt.mpr ?_)
      have hqd : Nat.gcd r q * (q / Nat.gcd r q) = q :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right r q)
      have h1 : Nat.gcd r q * (q / Nat.gcd r q)
          ≤ Nat.gcd r q * (r / Nat.gcd r q) := Nat.mul_le_mul le_rfl hcon
      have h2 : Nat.gcd r q * (r / Nat.gcd r q) ≤ r := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self r (Nat.gcd r q)
      rw [← hqd]
      exact h1.trans h2
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    -- ⟦the dilated window length⟧
    have hH'H : H / Nat.gcd r q + 1 ≤ H := by
      have hstep : H / Nat.gcd r q ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    -- ⟦THE NARROWING, at the dilated length: `H ≤ d₀·L ≤ arcDen·L`⟧
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
      have hexp : Nat.gcd r q * (H / Nat.gcd r q + 1)
          = Nat.gcd r q * (H / Nat.gcd r q) + Nat.gcd r q := by ring
      have hdm : Nat.gcd r q * (H / Nat.gcd r q) + H % Nat.gcd r q = H :=
        Nat.div_add_mod H (Nat.gcd r q)
      have hmod : H % Nat.gcd r q < Nat.gcd r q := Nat.mod_lt _ hd
      have hnat : H ≤ Nat.gcd r q * (H / Nat.gcd r q + 1) := by omega
      have hR : (H : ℝ) ≤ (Nat.gcd r q : ℝ) * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hdR : (Nat.gcd r q : ℝ) ≤ arcDen 12 H := by
        refine le_trans ?_ hqQ
        exact_mod_cast hdq
      have hL0 : (0 : ℝ) ≤ ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    -- ⟦the dilation's own gates⟧
    have hL1 : (1 : ℝ) ≤ Real.log (H : ℝ) := by
      have hLexp : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
      have he : (1 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      linarith
    have harcnp : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
      rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hqW : (q : ℝ) ≤ Real.log (H : ℝ) ^ (12 : ℕ) := by rw [← harcnp]; exact hqQ
    -- ⟦the pointwise transport, then the fibre count, then the datum, then the ledger⟧
    have hpt : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff M) H n q r) ^ 2
          ≤ (fun n' => (classSup (doorSievedCoeff M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2) (n / Nat.gcd r q) := by
      intro n _
      have hle := classSup_le_dilate (M := M) (H := H) (q := q) (r := r) (n := n)
        hM hq hL1 (hlogcap H hlo hhi) hqW
      have h0 := classSup_nonneg (doorSievedCoeff M) H n q r
      simp only
      nlinarith
    have hmaps : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        n / Nat.gcd r q ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
          (doorLadder R.x H i / Nat.gcd r q) := fun n hn => div_mem_reindexed hd hdA hn
    have hdatum := hcp H hlo hhi (H / Nat.gcd r q + 1) hH'H hnarrow (q / Nat.gcd r q) hq₀ hq₀Q
      (r / Nat.gcd r q) hr₀q₀ hcop₀ (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
      (doorLadder R.x H i / Nat.gcd r q) hA'pos (dilBlock_reindex_fit hd hdA hfit)
    have hd0R : (0 : ℝ) ≤ (Nat.gcd r q : ℝ) := Nat.cast_nonneg _
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (classSup (doorSievedCoeff M) H n q r) ^ 2
        ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff M) (H / Nat.gcd r q + 1) (n / Nat.gcd r q)
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 := Finset.sum_le_sum hpt
      _ ≤ (Nat.gcd r q : ℝ)
            * ∑ n' ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
                (doorLadder R.x H i / Nat.gcd r q),
              (classSup (doorSievedCoeff M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2 :=
          sum_Ioc_comp_div_le
            (f := fun n' => (classSup (doorSievedCoeff M) (H / Nat.gcd r q + 1) n'
              (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2)
            (fun _ => sq_nonneg _) (d := Nat.gcd r q) hd hmaps
      _ ≤ (Nat.gcd r q : ℝ)
            * (Bcl H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) ^ 2
                * ((doorLadder R.x H (i + 1) / Nat.gcd r q - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdatum hd0R
      _ ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) :=
          d0_ledger hd hH'H (hBcl0 H)

end Salt.MR

end
