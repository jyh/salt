/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FrameWitness
import Salt.MR.T0BandCapFree
import Salt.MR.M4Dyadic

/-!
# `M4MeanSq` — THE SUMMIT AT THE M4 DATUM (`m4_meansq_per_chi_gen`)

`ThmA2.thm_a2'_of_rows` is the frozen five-summand mean-square interface.  Until this file
it had no instance: its `hrows` slot wanted a cap-free seam-row family, its `hT0band` slot
wanted a `T₀`-band datum, and both wanted the SAME coefficient sequence `a`.  Wave 2 landed
all three suppliers.  This file does the joint instantiation — no new analysis, only binder
discipline.

## THE ENTRY ROUTE

```
                       a2Frame3_witness      (FrameWitness §9)     ─┐
                       row_ladder_at_witness (FrameWitness §10)    ─┤
                       capFreeFloor3_liouChi_all (CapFreeAssembly) ─┼→ a2Rows_of_capfree3
                                                                    │        │
                                                                    │        ↓ hrows
  cfb_t0band_supply_chi (T0BandCapFree §5) ─→ m4_t0band_at_datum ──┐│
                                                                   ↓↓
                            m4_t0band_of_live ──→ hT0band ──→ thm_a2'_of_rows
```

Three of the four suppliers are composed INSIDE `m4_meansq_per_chi_gen`.  The fourth — the
`T₀`-band — is entered at the M4 datum by `m4_t0band_at_datum` (§5) and delivered into the
capstone's `hT0band` slot by `m4_t0band_of_live`, because of THE A2-5 SEAM below.

## ⚠ THE A2-5 SEAM (why the band is a slot and not an inlined supplier)

`ThmA2`'s own header names it: *"the `𝒮_K`↔seam-datum identification is the A2-5/Route-III
seam: the statement's `a` is the coefficient sequence, and the two readings of it —
`1_{𝒮_K}·F` … and the station/band datum `seamCoeff (ellLin g) 1 t₀` — are supplied to the
two consumers, never derived from one another here."*  At the landed statements the two
readings are not merely underived, they are **contradictory**:

* `FrameWitness.err_at_witness` (hence `a2Frame3_witness`, hence `a2Rows_of_capfree3`)
  demands `hsupp : ∀ n, a n ≠ 0 → 1 ≤ blockOmega P P n` — `a` is SUPPORTED ON MULTIPLES OF
  the block prime `P`;
  ⟦R3a, 2026-07-28 — SUPERSEDED ON THE `_mr` ROUTE⟧ `err_at_witness_mr`/`a2Frame3_witness`
  and both capstones below no longer demand that pin at all: the coprime tail is PRICED
  (`M4ErrRewire.E_priced_mr` at `ramCopTail_moment`) against a carried mass budget
  `M_tail`, whose `(2X+20N)·M_tail` rides the ε-graded `EP₂` slot (⟦R3c⟧).  The legacy
  `err_at_witness` above keeps the pin and is untouched;
* `T0BandCapFree.cfb_t0band_supply` demands
  `hDatum : ∀ n, X < n → a n = seamCoeff (ellLin g) 1 t₀ n` — `a` is the UNSIEVED seam
  coefficient above `X`, which is non-zero at squarefree `n ∤ P` coprime to `q`.

(The narrower clash with `hasupp`'s `n ≤ 2X_d` cut-off is repaired here — see §2 — but the
sieve clash is not repairable by a congruence.)  So a single theorem discharging BOTH from
the landed suppliers would have jointly unsatisfiable hypotheses, i.e. be vacuous.  The file
therefore keeps `hT0band` as an explicit slot of the capstone and lands the band route
separately, with `m4_t0band_of_live`'s `hlive` (agreement on the LIVE RANGE `X < n ≤ N`) as
the single named binder the A2-5 identification must supply.  Nothing here is weakened: the
supplier's output type IS the slot's type at `C₁′ = cfbC₁ X C₁`, `M₀ = cfbM0 K q X`.

## ⟦THE BAND RE-CUT⟧ (2026-07-28) — the Ramaré block is a BAND, `Q` pinned at `⌊Q₈₃ X⌋₊`

Until this wave the capstone read `ramI (H83 X θ₂₉₃) P P` — a POINT, TLGATES-SCOPE's
"easiest witness".  The door datum calls it: at a point the Ramaré block-free mass is
`≍ 1/X_d`, so the coprime tail's charge `(2X+20N)·M_tail` is `O(1)` and no ε-window absorbs
it (`M4RowSupply`'s point-vs-band note).  The chain is now cut at the BAND `[P, Q]`:

* `FrameWitness` §2′ replaces the singleton collapse by the SANDWICH
  `P ≤ ramQbase H P j ≤ Q` (C2/C6 up from `P`, C3/C4/C5 down from `Q`);
* `FrameWitness` §3′ reads the `h`-ceiling at the band top: `log h + 30·(log X/loglog X)
  ≤ log X` — the minimal charge, which is why `Q` is PINNED at `⌊Q₈₃ X⌋₊`, not free;
* the row (`ThmA2Rows.a2Rows_of_capfree3`), the socket, the err supply and the whole
  `hUG34`/`seam_row` chain were already `(P,Q)`-general: they take `Q` and nothing else moves;
* the tail's own supply — the mass, its nonnegativity, the `EP₂` budget line at the two §8.3
  pins under the ONE new threshold `2688·C·loglog X ≤ (log X)^ε` — is `M4RowSupply` §4;
* the datum side (`SeamCoefW` on the whole band, at the un-phased `doorChiCoeff`) is
  `M4Band`, whose band gate is the K-calibration's own `𝒬K_j < P₈₃ X θ₂₉₃ ≤ P`.

## THE TWO PINS (forced, not chosen)

`a2Frame3_witness` asks `X ≤ X_d`, `2X_d ≤ N` and `N ≤ 2X_d`; `a2Rows_of_capfree3` asks
`X ≤ N` and `N ≤ 2X`.  Together: `N = 2X_d` and `X ≤ X_d`, `2X_d = N ≤ 2X`, so

  **`X_d = X`  and  `N = 2X_d = 2X`.**

Both are carried as the named binders `hXd`/`hNXd` (FRAME's report, "the `X_d = X`, `N = 2X`
joint pin").  Every other scale relation between `N`, `X_d`, `X` is then arithmetic.

## THE DATUM RULE (the `lam` collision, flags `2e3b8fe`)

The row's `g`-slot is SUMMED over integers, so it is `liouChi χ = λ·χ̄`
(`CapFreeAssembly.liouChi`), never `lamChi`.  `capFreeFloor3_liouChi_all` is the floor in
exactly that shape; `pretDistSq_liouChi_eq` is the bridge that made it available.

## THE LIVE-RANGE BAND DATUM (§2 — the one genuine repair here)

`cfb_t0band_supply_chi`'s `hDatum` pins `a n = seamCoeff (ellLin (liouChi χ)) 1 t₀ n` for
EVERY `n > X`, while `a2Rows_of_capfree3`'s `hasupp` forces `a n = 0` for `n > 2X_d = N`.
Those two are jointly unsatisfiable at any single `a` (the seam coefficient does not vanish
above `N`).  The repair is a congruence, not a weakening: `dpolyA a (seamS0 N X) t` reads
`a` only on `seamS0 N X ⊆ [1, N]`, so the band supplier is fed the UNTRUNCATED datum
`m4BandDatum χ t₀ X` and the result transported to `a` by `dpolyA_congr`.  What `a` must
satisfy is then only the LIVE-RANGE agreement `hlive` (`X < n ≤ N`), which IS compatible
with `hasupp` — though not, at the landed statements, with the sieve support (see the A2-5
seam above).

## THE `Cq` RULE (K6)

`Cq` and `cq` are bound by `a2Rows_of_capfree3`'s own existential and are opaque
(flags, K6).  Both gates (`hcqgate` at the block base, `hCqgate` at the `𝒰`-leg) are
therefore stated INSIDE the capstone's existential scope, in terms of the obtained
constants — which is why `m4_meansq_per_chi_gen` opens with `∃ Cq cq …` and carries the
gates as hypotheses of the inner `∀`.

## THE BINDER → SUPPLIER TABLE

`a2Rows_of_capfree3`'s hypothesis list, in file order.  "carried" = a named binder of
`m4_meansq_per_chi_gen` (a scale gate the door numerology clears, or an S8 datum) — never
evaluated here.

| # | binder | supplier |
|---|---|---|
| 1 | `hg` (‖g p‖ ≤ 1) | `norm_liouChi_le_one` |
| 2 | `hc1` (‖c n‖ ≤ 1) | carried `hcf1` |
| 3 | `hb1` (‖b n‖ ≤ 1) | `ellLin_norm_le_one` ∘ `norm_liouChi_le_one` |
| 4 | `hcf1` | carried `hcf1` |
| 5 | `hM` (1 ≤ M) | carried |
| 6 | `hXdQ` (`Q₂ ≤ X_d`) | carried |
| 7 | `F : A2Frame3 …` | `a2Frame3_witness` (see the second table) |
| 8 | `hH2` (2 ≤ H₈₃) | carried |
| 9 | `hXe` (e ≤ X) | `hXee` (e^e ≤ X), monotonicity |
| 10 | `hlX2` (e² ≤ log X) | carried |
| 11 | `hh4` (4 ≤ h) | carried |
| 12 | `hQ1h` (Q₁ ≤ h) | carried |
| 13 | `hLe` (e ≤ L) | carried |
| 14 | `hVJg` | carried |
| 15 | `hMs` | `row_ladder_at_witness`.1 |
| 16 | `hm₀2` | `row_ladder_at_witness`.2.1 |
| 17 | `hm₀` | `row_ladder_at_witness`.2.2.1 |
| 18 | `hMs4` | `row_ladder_at_witness`.2.2.2 |
| 19–21 | `hV1`, `hVδ`, `hlogV` | carried |
| 22 | `hCb0` | carried |
| 23 | `hPlow` (P₈₃ ≤ P) | carried |
| 24 | `hQ0` (0 < Q) | `hP3` (3 ≤ P) |
| 25 | `hQhigh` (Q ≤ Q₈₃) | carried `hPhigh` (Q := P) |
| 26 | `hPQ83` (P ≤ Q) | `le_rfl` (the witness pins `P = Q`) |
| 27 | `hfloor` (`CapFreeFloor3 g X`) | `capFreeFloor3_liouChi_all` + carried `hcff` |
| 28–30 | `hR0`, `hRrad`, `hRlow` | carried |
| 31 | `hCbound` (`ShortIntervalDatum Cb`) | carried |
| 32–35 | `hX₀k`, `hMfl0`, `hk2`, `hkX` | carried |
| 36 | `hkk` (`kmin ≤ kk j`) | carried (at `witKk`) |
| 37 | `hMtpin` (`pin2Gate ≤ Mt j`) | carried (at `witMt`) — shared with the frame |
| 38 | `hMt` (`Mt j ≤ Ymax`) | carried (at `witMt`) |
| 39–43 | `hgateW`, `hYpin`, `hWY`, `hXY`, `hthr` | carried |
| 44 | `hCqgate` | carried, INSIDE the existential (K6) |
| 45–47 | `hε0`, `habs`, `hEP2` | carried (the ε-window) |
| 48 | `hXN` (X ≤ N) | the two pins |
| 49 | `hN2` (N ≤ 2X) | the two pins |
| 50 | `hsupp` (`a` above `X`) | carried `hsupp0` |
| 51 | `hNXd` (2X_d ≤ N) | the `N = 2X_d` pin |
| 52 | `hcoef` (band factorisation) | carried `hcoefBand` (S8), ON-WINDOW (§3′) |
| 53 | ~~`hwin`~~ (band window) | **DELETED** — ⟦WALL 1⟧'s repair, see §3‴′ |
| 54–55 | `hQXd`, `hXdbig` | carried |
| 56 | `hN4` (N ≤ 4X_d) | the `N = 2X_d` pin |
| 57 | `hdom` | carried |
| 58 | `ha1` (‖a n‖ ≤ 1) | carried |
| 59 | `hasupp` (`a` in `[X_d, 2X_d]`) | carried (S8) |

`a2Frame3_witness`'s own list (FrameWitness §9's three classes):

| binder | supplier |
|---|---|
| `hX0`, `hh0`, `hLX0`, `hXd1`, `hXdX` | arithmetic from the pins and the scale page |
| `hLXL`, `hTann`, `hceil5`, `hT₀le`, `hTbot` | carried |
| `hhceil` (the `h`-ceiling, K8/law #253) | carried — structural, never derived |
| `hH2`, `hP3`, `hlogP2`, `hPbot`, `hPlog`, `hPL` | carried |
| `hcqgate` | carried, INSIDE the existential (K6) |
| `hW4` | `hW5` (the row ladder's own floor), `linarith` |
| `hkth`, `hMtX`, `hC16`, `hRrad0`, `hRradW` | carried |
| `hMN` (2X_d ≤ N), `hN2` (N ≤ 2X_d) | the `N = 2X_d` pin |
| `hPj1`, `hthinpin` | carried |
| `hXthr`, `hMtpin` | carried |
| `hδsq`, `hlog2X`, `hksthr` | carried (`hlog2X` is arithmetic) |
| `hHX` (H₈₃ ≤ X_d) | carried |
| `hcoefW` at the pin `p = P` | carried `hcoefPin` (S8) — `hwinPin` is GONE, see §3″ |
| `ha`, `hb`, `hc` | `ha1`, `ellLin_norm_le_one`, `hcf1` |
| `hasupp`, `hsupp` (blockOmega) | carried (S8) |
| `hEP2` (`witEP2 ≤ EP2`) | carried |

`cfb_t0band_supply_chi`'s list (§5, `m4_t0band_at_datum`): `hX1`/`hXb`/`hXee` the three
scale floors, `hXN`/`hN2X` the pins, `hC₁`, `ht₀` (the band-geometry gate
`|t₀| ≤ seamT0 X + 1`), the four `Y`-gates, `hRHS` (per band frequency — the whole cost of
going cap-free), `hbthr`; its `hsupp`/`hDatum` slots are discharged by §2's `m4BandDatum`,
and `m4_t0band_of_live` transports the result by `dpolyA_congr`.

`thm_a2'_of_rows`'s remaining own list: `hX3` (3 ≤ X, from `e^e ≤ X`), `hhX` (Lemma 14's
window frame), `hgP1`, `hgRows`, `hεwin`, `hL4096` — all carried.

## THE TRIVIAL BRANCH

`m4_meansq_or_trivial` is the case split the dyadic consumer (M4-7) takes: below the
freeze's `trivThresh H d₀ W` the window is discarded against `M4Dyadic`'s
`integral_logMeasure_absWindowSum_le_thresh` (no analysis at all); at or above it the
capstone fires.  The dyadic COVER is deliberately NOT baked in — `m4_meansq_per_chi_gen` is
the per-scale statement at a general `X` clearing the gates, so M4-7 owns the summation.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the `dpolyA` congruence

`dpolyA a s₀ t = ∑_{m ∈ s₀} a_m/m^{1+it}` reads `a` only on `s₀`.  That is the whole content
of the live-range repair. -/

/-- `dpolyA` depends on the coefficient sequence only through its values on the index set. -/
theorem dpolyA_congr {a b : ℕ → ℂ} {s0 : Finset ℕ} (h : ∀ m ∈ s0, a m = b m) (t : ℝ) :
    dpolyA a s0 t = dpolyA b s0 t :=
  Finset.sum_congr rfl fun m hm => by rw [h m hm]

/-- Membership in the seam index set, unfolded once. -/
theorem mem_seamS0 {N n : ℕ} {X : ℝ} (hn : n ∈ seamS0 N X) : 1 ≤ n ∧ n ≤ N ∧ X < (n : ℝ) := by
  rw [seamS0, Finset.mem_filter, Finset.mem_Icc] at hn
  exact ⟨hn.1.1, hn.1.2, hn.2⟩

/-! ## §2 — THE BAND DATUM

The untruncated seam coefficient, cut off below `X`.  It satisfies `cfb_t0band_supply_chi`'s
`hsupp` and `hDatum` by construction — and, unlike the row's `a`, it is NOT required to
vanish above `N`, which is exactly why the two suppliers can be composed. -/

/-- **THE BAND DATUM** `m4BandDatum χ t₀ X`: the seam coefficient of `ellLin (liouChi χ)` at
the centre `t₀`, forced to `0` on `n ≤ X`. -/
def m4BandDatum {q : ℕ} (χ : DirichletCharacter ℂ q) (t₀ X : ℝ) : ℕ → ℂ :=
  fun n => if (n : ℝ) ≤ X then 0 else seamCoeff (ellLin (liouChi χ)) (fun _ => 1) t₀ n

theorem m4BandDatum_supp {q : ℕ} (χ : DirichletCharacter ℂ q) (t₀ X : ℝ) :
    ∀ n : ℕ, (n : ℝ) ≤ X → m4BandDatum χ t₀ X n = 0 := fun _ hn => if_pos hn

theorem m4BandDatum_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (t₀ X : ℝ) :
    ∀ n : ℕ, X < (n : ℝ) →
      m4BandDatum χ t₀ X n = seamCoeff (ellLin (liouChi χ)) (fun _ => 1) t₀ n :=
  fun _ hn => if_neg (not_le.mpr hn)

/-- **THE LIVE-RANGE TRANSPORT.**  If `a` agrees with the seam coefficient on `X < n ≤ N`
then its band polynomial is the band datum's, frequency by frequency. -/
theorem dpolyA_seamS0_bandDatum {q : ℕ} (χ : DirichletCharacter ℂ q) {t₀ X : ℝ} {N : ℕ}
    {a : ℕ → ℂ}
    (hlive : ∀ n : ℕ, X < (n : ℝ) → n ≤ N →
      a n = seamCoeff (ellLin (liouChi χ)) (fun _ => 1) t₀ n) (t : ℝ) :
    dpolyA (m4BandDatum χ t₀ X) (seamS0 N X) t = dpolyA a (seamS0 N X) t := by
  refine dpolyA_congr (fun m hm => ?_) t
  obtain ⟨-, hmN, hmX⟩ := mem_seamS0 hm
  rw [m4BandDatum_eq χ t₀ X m hmX, hlive m hmX hmN]

/-! ## §3 — the scale-page arithmetic

Three facts extracted from `e^e ≤ X` alone (`thm_a2'_of_rows` wants `3 ≤ X`, the row wants
`e ≤ X`, and the frame wants `0 < X`). -/

theorem exp_exp_one_gt_three : (3 : ℝ) < Real.exp (Real.exp 1) := by
  have h1 : Real.exp 1 + 1 ≤ Real.exp (Real.exp 1) := Real.add_one_le_exp _
  have h2 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  linarith

theorem exp_one_le_exp_exp_one : Real.exp 1 ≤ Real.exp (Real.exp 1) :=
  Real.exp_le_exp.mpr (Real.one_le_exp (by norm_num))

/-! ## §3′ — THE WINDOW-WIDENING OF A COEFFICIENT LAW (the capstone binder repair)

**THE DEFECT** (SEAM's finding, kernel-checked as `M4Seam.m4_row_cf_block_eq_zero`).  The
capstone's coefficient binders used to quantify over ALL cofactors `m`.  At `m = 1` that
reads `a p = ellLin g 1 · cf p`; but `hsupp0` forces `a n = 0` for `n ≤ X`, and the block
prime obeys `p ≤ 2(X/h) ≤ X/2 < X` (likewise every band prime, `p ≤ Q₂ ≤ X_d = X`).  So the
binder set could only be inhabited by data with `cf p = 0` at every prime in range — it
could not host the intended `P`-exact datum.  The binders are now RESTRICTED to the window
`X_d ≤ p·m ≤ 2X_d` (`hwin`'s own range, byte-identical casts): the defect point `m = 1`
falls outside it, and nothing is lost, because —

**⟦THE WALL⟧'s SEQUEL (§3″, below).**  The narrowing of §3′ repaired the `m = 1` collapse on
the `hcoefPin` side but NOT on the `hwinPin` side: `M4Seam.m4_row_cf_block_eq_zero` reads the
WINDOW law alone and still forces `cf P = 0` at every block prime under the row's pins.  The
capstone's pin-chain binder `hwinPin` is therefore DELETED outright (§3″), which is possible
because `FrameWitness.err_at_witness_mr` — the `hwin`-free err supply built on
`M4ErrRewire.ramP2massMR_direct` — needs only the on-window factorization `hcoefPin`, i.e.
`SeamRowWindowed.SeamCoefW`.  ⟦WALL 1⟧ (below) does the same to the BAND chain: `hwinBand`
is DELETED and the row's Lemma-12 exit re-cut at MR's own cofactor range, so `hcoefBand`
survives alone, on-window.

**THE WIDENING** (`coef_widen_of_window`).  Outside the window the law is FREE: below it
`hsupp0` kills `a (p·m)` and `hwin`'s lower bound kills `cf p · b m`; above it `hasupp`
kills `a (p·m)` and `hwin`'s upper bound kills `cf p · b m`.  So the restricted law implies
the unrestricted one at the capstone's own data, and every downstream consumer
(`a2Frame3_witness`, `a2Rows_of_capfree3`) is fed exactly what it was fed before.  The
repair is therefore pure hypothesis-weakening: the conclusion is untouched, and any supplier
of the old binder still supplies the new one by dropping two arguments. -/

/-- **THE WINDOW-WIDENING OF A COEFFICIENT LAW** (`coef_widen_of_window`).  A factorisation
law `a (p·m) = b m · cf p` known only on the support window `X_d ≤ p·m ≤ 2X_d` holds
everywhere in the range `R`, because off the window both sides vanish — the left by the
support laws `hsupp0`/`hasupp` of `a`, the right by the window law `hwin` of `cf · b`. -/
theorem coef_widen_of_window {a b cf : ℕ → ℂ} {Xd : ℕ} {X : ℝ} {R : ℕ → ℕ → Prop}
    (hXd : (Xd : ℝ) = X)
    (hsupp0 : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hwin : ∀ p m : ℕ, R p m → cf p * b m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    (hcoef : ∀ p m : ℕ, R p m → (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) →
      (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) → a (p * m) = b m * cf p) :
    ∀ p m : ℕ, R p m → a (p * m) = b m * cf p := by
  intro p m hR
  have hpm : ((p * m : ℕ) : ℝ) = (p : ℝ) * (m : ℝ) := by push_cast; ring
  by_cases hlo : (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ)
  · by_cases hhi : (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)
    · exact hcoef p m hR hlo hhi
    · -- ⟦above the window: `hasupp` kills the left, `hwin`'s top kills the right⟧
      have hb0 : b m * cf p = 0 := by
        rw [mul_comm]
        by_contra hne
        exact hhi (hwin p m hR hne).2
      have ha0 : a (p * m) = 0 := by
        by_contra hne
        have hle : p * m ≤ 2 * Xd := (hasupp _ hne).2
        have : ((p * m : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast hle
        rw [hpm] at this
        push_cast at this
        exact hhi this
      rw [ha0, hb0]
  · -- ⟦below the window: `hsupp0` kills the left, `hwin`'s bottom kills the right⟧
    have hb0 : b m * cf p = 0 := by
      rw [mul_comm]
      by_contra hne
      exact hlo (hwin p m hR hne).1
    have ha0 : a (p * m) = 0 := by
      refine hsupp0 _ ?_
      rw [hpm, ← hXd]
      linarith [not_le.mp hlo]
    rw [ha0, hb0]

/-! ## §3″ — ⟦THE WALL⟧: THE PIN CHAIN LOSES ITS WINDOW LAW

The capstone's err-side binder pair at the block pin `P = Q` is now the SINGLE relativized
law `SeamRowWindowed.SeamCoefW X_d P Q a b cf` (the BAND form) — byte-identical to the
old `hcoefPin`, and the old `hwinPin` is deleted.  Three consequences, all in the honest
direction:

* `m4_meansq_per_chi_gen` and `m4_meansq_or_trivial` are strictly STRONGER theorems (one
  hypothesis fewer, none added); every existing supplier still supplies.
* the `m = 1` collapse `M4Seam.m4_row_cf_block_eq_zero` no longer applies to the binder set:
  its hypothesis is exactly the deleted `hwinPin`.
* the widening `coef_widen_of_window` is no longer needed on the pin chain (the err route
  consumes the window-restricted law directly); it remains the BAND chain's bridge.

**WHAT STILL BLOCKS THE DOOR DATUM.**  `M4ErrRewire.doorDatum_inhabits_err_binders` shows
the door's sieved, phased `λχ̄` meets the surviving pair law at every cofactor.  It does NOT
meet it with the cofactor slot equal to `ellLin (liouChi χ)`, and `CapFreeArm3.A2Frame3.err`
pins that slot.  Freeing it — the `b`-slot generalization — is a statement change in
`CapFreeArm3`, outside this wave.

## §3‴′ — ⟦WALL 1⟧: THE BAND CHAIN LOSES ITS WINDOW LAW TOO

`M4DoorRow` §6 (`band_window_ratio_lock`) is the kernel witness that `hwinBand` locks any two
LIVE block primes into a factor `2`, while `door_block_one_wide` shows the door's level-1
K-block spans `2^{(M−1)·2^18}`.  So the door datum cannot inhabit `hwinBand` at all, and the
binder is DELETED here — exactly as `hwinPin` was in §3″, and for the same reason.

What pays for it is `M4RowMR`: the seam row's Lemma-12 exit is re-cut at MR's own cofactor
range (`SeamRowWindowed.ramErr_moment_split_mr_windowed`, four rows at prefactor `4`), where
the window lives in the INDEX SET.  The `p²` row is then `M4P2MR.ramP2massMR_direct` and the
block-free row `TypicalDensity.blockfree_sum_le` — neither reads a window law.  The price is
`480 → 960` on the row summand of `CapFreeArm3.seam_row_number_capfree3`, which
`ThmA2Rows.a2_term3_weigh_mr` absorbs inside `a2Mrow`'s existing `5760` (⟦AMENDMENT G⟧'s `×4`
cover of `1440`): **no interface numeral moves, and this capstone's conclusion is byte-identical
to its pre-repair self.**  `coef_widen_of_window` (§3′) loses its last consumer with the
deletion and is kept as a documented dead stone. -/

/-! ## §3‴ — ⟦THE SOCKET CUT⟧: THE ROW'S CO-FACTOR DATUM, SUPPLIED HERE

`CapFreeArm3`'s row no longer reads the multiplicative datum at all: it carries
`CofactorSocket … R̄ b`, the single pointwise fact `‖R_{j,H}(1+it)‖ ≤ R̄` off the seam ball
(ROW-GENERICITY, 2026-07-28).  At THIS capstone the datum is still `ellLin (liouChi χ)`, so
the socket is discharged from the landed cap-free machinery — the floor kills the pocket at
every damping, `CaseASocket.caseASocket2_discharged` gives CASE A, the frame gives the `3X`
box and the §8.3 block gates, `USetGradedPrice.Rbd34loc_uniform` the uniform ceiling.

The two stones below carry that supply in an ISOLATED context (the capstone's ~80-binder
context makes `linarith` blow its budget; law #253's arithmetic is unchanged). -/

/-- **`R̄ ≥ 0` AT THE UNIFORM CORNER** (`m4_rbar_nonneg`).  `cofactorRbd34loc_nonneg` at the
pin `c = 1/e`, in the shape the capstone's grade slot wants. -/
theorem m4_rbar_nonneg {Cb X kmin Ymax Rrad : ℝ} (hCb0 : 0 ≤ Cb) (hk2 : 2 ≤ kmin) :
    0 ≤ cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
      (Tstar2 Ymax (Real.log Ymax)) Rrad := by
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  exact cofactorRbd34loc_nonneg hc1 hCb0 (by linarith)

/-- **THE CO-FACTOR SOCKET AT THE WITNESS LADDER** (`m4_cofactorSocket_at_witness`).
`CapFreeArm3.cofactorSocket_of_ellLin` at `b := ellLin (liouChi χ)`, `t₁ := 0`, the annulus
height `Tann := X` (the window's TOP — the row reads it antitonely), `Mt/kk := witMt/witKk`,
and `R̄` the uniform corner `cofactorRbd34loc(1/e, C_b, X, θ₂₉₃, kmin, Ymax, T*₂(Ymax), Rrad)`.

`hsockA` is `CaseASocket.caseASocket2_discharged`'s body at the capstone's own `X₀`. -/
theorem m4_cofactorSocket_at_witness {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {cf a : ℕ → ℂ} {N Xd P Q M : ℕ}
    {X h δ' VJ L Cb Rrad kmin Ymax EP2 cq T₀ X₀ : ℝ}
    (hsockA : ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (P' Q' : ℕ) (c' Cb' X' θ' : ℝ) (k₀' M' : ℕ) (t : ℝ),
        0 < c' → c' ≤ 1 / Real.exp 1 → 2 * c' < 1 → 0 ≤ Cb' → ShortIntervalDatum Cb' →
        X₀ ≤ (k₀' : ℝ) → pin2Gate ≤ (k₀' : ℝ) → k₀' ≤ M' → (M' : ℝ) ≤ 2 * (k₀' : ℝ) →
        0 ≤ cofactorMfl X' θ' (k₀' : ℝ) →
        CaseASocket2 g P' Q' c' Cb' X' θ' k₀' M' t)
    (F : A2Frame3 (ellLin (liouChi χ)) cf a N Xd P Q (Adoor M) (3072 * M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1door M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀)
    (hX0 : 0 < X) (hh4 : 4 ≤ h) (hLXe : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X theta293 ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : CapFreeFloor3 (liouChi χ) X)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb) (hRrad0 : 0 < Rrad)
    (hX₀k : X₀ ≤ kmin) (hMfl0 : 0 ≤ cofactorMfl X theta293 kmin) (hk2 : 2 ≤ kmin)
    (hkk : ∀ j ∈ ramI (H83 X theta293) P Q,
      kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ))
    (hMtpin : ∀ j ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ))
    (hMtY : ∀ j ∈ ramI (H83 X theta293) P Q,
      ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) :
    CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0
      (cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
        (Tstar2 Ymax (Real.log Ymax)) Rrad) (ellLin (liouChi χ)) := by
  have hgl : ∀ p : ℕ, p.Prime → ‖liouChi χ p‖ ≤ 1 := fun p _ => norm_liouChi_le_one χ p
  have he1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hh0 : (0 : ℝ) < h := by linarith
  -- ⟦the annulus at the window's TOP⟧ `2·(X/h) ≤ X` from `4 ≤ h`
  have h2aX : 2 * (X / h) ≤ X := by
    rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ hh0]
    nlinarith
  have hblkX := F.blocks X h2aX le_rfl
  -- ⟦SUPPLIER 1⟧ the collision socket, VACUOUSLY, at the centre `0`
  have hsockP : PocketSocket3 (liouChi χ) P Q X theta293 0 :=
    pocketSocket_of_floor3 hgl theta293_pos (le_of_lt theta293_lt_one_div_32) hLXe hPlow
      hQhigh hPQ hfloor 0
  -- ⟦SUPPLIER 2⟧ CASE A, from the discharged slice
  have hA2 : ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ,
      CaseASocket2 (liouChi χ) P Q (1 / Real.exp 1) Cb X theta293
        (witKk (H83 X theta293) Xd j) (witMt (H83 X theta293) Xd j) t := by
    intro j hj t
    obtain ⟨-, -, -, -, -, -, hk₀th, -, hk₀lo, hk₀hi, -, -, hhigh, hMtop, -, -, -⟩ :=
      hblkX j hj
    have hk₀pin : pin2Gate ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans pin2Gate_le_ballQuarterThreshold hk₀th
    have hk3 : (3 : ℝ) ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans three_le_ballQuarterThreshold hk₀th
    have hkMR : ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)
        ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) := by linarith
    have hkM : witKk (H83 X theta293) Xd j ≤ witMt (H83 X theta293) Xd j := by
      exact_mod_cast hkMR
    have hM2k : ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)
        ≤ 2 * ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) := by linarith
    have hX₀kk : X₀ ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) := le_trans hX₀k (hkk j hj)
    have hMflkk : (0 : ℝ) ≤ cofactorMfl X theta293 ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans hMfl0 (cofactorMfl_mono X theta293 (hkk j hj))
    exact hsockA (liouChi χ) hgl P Q (1 / Real.exp 1) Cb X theta293
      (witKk (H83 X theta293) Xd j) (witMt (H83 X theta293) Xd j) t hc0 le_rfl hc1 hCb0
      hCbound hX₀kk hk₀pin hkM hM2k hMflkk
  -- ⟦SUPPLIER 3⟧ the uniform ceiling
  have hMt1 : ∀ j ∈ ramI (H83 X theta293) P Q,
      (1 : ℝ) ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) := by
    intro j hj
    have h1 : (1 : ℝ) ≤ pin2Gate := Real.one_le_exp (by norm_num)
    exact le_trans h1 (hMtpin j hj)
  have hRbdU := Rbd34loc_uniform (H83 X theta293) P Q (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) (1 / Real.exp 1) Cb X theta293 Rrad kmin Ymax hc0 hc1 hCb0
    (by linarith) hMtpin hkk hMt1 hMtY
  exact cofactorSocket_of_ellLin hgl hc1 hCb0 hRrad0 hsockP hblkX F.box hA2 hRbdU

/-! ## §4 — THE SUMMIT

Every hypothesis below is either arithmetic from the two pins, or a named binder in the
sense of the header table.  Nothing is evaluated. -/

set_option maxHeartbeats 1600000 in
-- the ~75-binder joint instantiation: elaborating the three suppliers' argument lists
-- against one statement is what costs the heartbeats, not any tactic search
/-- **THE FIVE-SUMMAND MEAN SQUARE AT THE M4 DATUM** (`m4_meansq_per_chi_gen`).

For every Dirichlet character `χ mod q` in the door's modulus range `q ≤ Qm`, at every scale
`X` clearing the gates, and at any `T₀`-band bound `t0BandB X C₁′ M₀` the consumer holds:

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁′²·exp(−M₀/e)`
  `   + 1787702400·(log Q₁)^{1/3}/P₁^{1/12}`
  `   + 188133·(log X)^{−1/500}`
  `   + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
  `   + 6315000/h`,

which is `ThmA2.thm_a2'_of_rows`' conclusion verbatim (M4-7 does arithmetic on the raw
summands, so nothing is re-shaped here).  This is the PER-SCALE statement: the dyadic cover
of `M4Dyadic` is the consumer's, not this theorem's.

`§5`'s `m4_t0band_at_datum` + `m4_t0band_of_live` are the `hT0band` slot's supplier, at
`C₁′ = cfbC₁ X C₁` and `M₀ = cfbM0 K q X`; the slot is explicit rather than inlined because
of the A2-5 seam (module docstring).

See the module docstring for the binder → supplier table. -/
theorem m4_meansq_per_chi_gen :
    ∃ (Cq cq T₀ X₀ Cs Ccc : ℝ) (Kfl : ℕ → ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      ∀ (Qm q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ : ℝ),
            -- ⟦the two pins (FRAME's joint instantiation)⟧
            (Xd : ℝ) = X → N = 2 * Xd →
            -- ⟦the scale page⟧
            Real.exp (Real.exp 1) ≤ X → Real.exp 2 ≤ Real.log X →
            4 ≤ h → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
            Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X →
            TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
            T₀ ≤ 2 * (X / h) → Real.exp 1 ≤ 2 * (X / h) →
            Real.log X ≤ L → Real.exp 1 ≤ L →
            -- ⟦the door and the block pin `P = Q`⟧
            1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
            ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                        (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                    / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
            -- ⟦the window floors, at the witness ladder⟧
            (∀ j ∈ ramI (H83 X theta293) P Q, 5 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd j ≤ X) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              18 + Real.log (Real.log X)
                  - Real.log (Real.log (ramRbot (H83 X theta293) Xd j - 1))
                ≤ 32 * theta293 * Real.log (Real.log X)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              Rrad ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (3072 * M) 2)
                  (calQK (Adoor M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
                ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) →
            -- ⟦the calibration, the radius, the short-interval datum⟧
            0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
            1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
            δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)) →
            656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293) →
            Real.exp (mrAlpha (1 / 12) 2
                * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
            0 ≤ Cb → ShortIntervalDatum Cb →
            2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X →
            -- ⟦the `kmin`/`Ymax` ladder⟧
            X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
            (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
            pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
            Real.log X ≤ Real.log Ymax →
            32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
            -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6) — inside the existential scope⟧
            420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2 →
            1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
            -- ⟦the ε-window and the Perron budget⟧
            0 ≤ ε → ε ≤ theta293 - 1 / 500 → 8640 ≤ (Real.log X) ^ ε →
            12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
            witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail) ≤ EP2 →
            -- ⟦the S8 datum⟧
            (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
            (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
            (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
            -- ⟦R3a⟧ the coprime-tail MASS, in place of the single-`P` support pin
            0 ≤ Mtail →
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤ Mtail →
            -- ⟦W1 — THE CARRIED `b`-SLOT⟧ the co-factor datum, its level family, its socket
            -- and its grade are all CARRIED now: the capstone manufactures none of them, so
            -- the row is available at ANY datum meeting them (the door's, in particular).
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
              p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m →
              (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
              a (p * m) = bfam j m * cf p) →
            -- ⟦THE PIN CHAIN, `hwin`-FREE (⟦THE WALL⟧'s rewire): the on-window
            -- factorization ALONE.  `hwinPin` is GONE — see §3″⟧
            SeamCoefW Xd P Q a b cf →
            -- ⟦the `T₀`-band datum: `m4_t0band_at_datum` is the supplier, and §2's
            -- `dpolyA_seamS0_bandDatum` the bridge — see the header on the A2-5 seam⟧
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X C₁' M₀ →
            -- ⟦the cap-free floor's threshold⟧
            40 * Real.log (Real.log (Real.log X))
                + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
                    + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl Qm + 25)
              < Real.log (Real.log X) →
            -- ⟦the interface's two grading gates and the `4096` room⟧
            374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ)))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1 M
                + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3
  -- ⟦THE SOCKET CUT⟧ the CASE-A discharge is the SUPPLIER's now, so its `X₀` is taken here
  obtain ⟨X₀, hX₀0, -⟩ := caseASocket2_discharged
  -- ⟦THE SKOLEM CUT⟧ the cap-free floor constant is chosen as a FUNCTION of the modulus
  -- range, so `Qm` may be quantified inside (`M4Spine`'s ⟦WALL C⟧, the `Qm` half)
  choose Kfl hKfl0 _hcap using capFreeFloor3_liouChi_all
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, ?_⟩
  intro Qm q _ _χ _hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin _hkk _hMtY
    hRrad0 hRrad _hRlow hV1 hVδ hlogV hδsq hksthr hVJg _hCb0 _hCbound hXthr
    _hX₀k _hMfl0 _hk2 _hkX _hgateW _hYpin _hWY _hXY _hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band _hcff hgP1 hgRows hL4096
  -- ⟦THE SCALE PAGE⟧
  have hXe : Real.exp 1 ≤ X := le_trans exp_one_le_exp_exp_one hXee
  have hX3 : (3 : ℝ) ≤ X := le_of_lt (lt_of_lt_of_le exp_exp_one_gt_three hXee)
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hLX0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 2) hlX2
  -- ⟦THE TWO PINS, in every shape the suppliers want⟧
  have hXdX : X ≤ (Xd : ℝ) := le_of_eq hXd.symm
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by rw [hXd]; linarith
  have hXd1 : 1 ≤ Xd := by exact_mod_cast hXd1'
  have hNcast : (N : ℝ) = 2 * X := by rw [hNXd]; push_cast; rw [hXd]
  have hMN : 2 * Xd ≤ N := le_of_eq hNXd.symm
  have hNle : (N : ℝ) ≤ 2 * (Xd : ℝ) := by rw [hNcast, hXd]
  have hXN : X ≤ (N : ℝ) := by rw [hNcast]; linarith
  have hN2X : (N : ℝ) ≤ 2 * X := le_of_eq hNcast
  have hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ) := by rw [hNcast, hXd]; linarith
  -- ⟦THE FRAME'S REMAINING ARITHMETIC⟧
  have hW4 : ∀ j ∈ ramI (H83 X theta293) P Q, 4 ≤ ramRbot (H83 X theta293) Xd j :=
    fun j hj => by linarith [hW5 j hj]
  have hlog2X : (0 : ℝ) ≤ 1 + Real.log (2 * X) := by
    have : (0 : ℝ) ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
    linarith
  -- ⟦⟦WALL 1⟧'s REWIRE⟧ the window-restricted BAND law is consumed AS IS now: the row's
  -- `hwin`-free four-row exit (`M4RowMR`) reads only the on-window factorization, so the
  -- widening `coef_widen_of_window` is no longer on the path (it stays as the historical
  -- instance) and `hwinBand` — ⟦THE WALL⟧'s second head — is DELETED from the statement
  -- ⟦FIELD 1–4: THE FRAME⟧ — at the CO-FACTOR DATUM `ellLin (liouChi χ)` (the socket cut's
  -- `b`-slot; the frame no longer takes a multiplicative generator)
  have F : A2Frame3 b cf a N Xd P Q (Adoor M) (3072 * M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1door M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hgP1 hgRows ⟨hε0, hεup⟩ hL4096


/-! ## §5 — SUPPLIER (4) AT THE M4 DATUM

`cfb_t0band_supply_chi` with its two coefficient slots discharged by §2.  What comes out is
*literally* `m4_meansq_per_chi_gen`'s `hT0band` slot at

  `C₁′ = cfbC₁ X C₁ = (C₁+1)(log X)^{1/30}`,   `M₀ = cfbM0 K q X`,

so the plug is an instantiation, not a re-statement.  Two binders fewer than upstream: the
band datum's own support and datum laws are `rfl`-level. -/

/-- **THE `T₀`-BAND AT THE M4 DATUM** (`m4_t0band_at_datum`).  `cfb_t0band_supply_chi`
evaluated at `a := m4BandDatum χ t₀ X`; the remaining binders are upstream's own (the three
scale floors, the pins, `1 ≤ C₁`, the band-geometry gate `|t₀| ≤ seamT0 X + 1`, the four
`Y`-gates, `hRHS` at every band frequency, and the `cfb_ballerr_le` side condition). -/
theorem m4_t0band_at_datum (Qm : ℕ) :
    ∃ K Xb : ℝ, 0 ≤ K ∧ 0 < Xb ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t₀ : ℝ) (Y : ℝ → ℝ), q ≤ Qm →
        ∃ X₁ : ℝ, 0 < X₁ ∧
          ∀ (X : ℝ) (N : ℕ) (C₁ : ℝ),
            X₁ ≤ X → Xb ≤ X → Real.exp (Real.exp 1) ≤ X →
            X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 1 ≤ C₁ → |t₀| ≤ seamT0 X + 1 →
            (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → 10 ≤ Y (k : ℝ)) →
            (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
            (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
            (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
                Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
            (∀ t : ℝ, |t| ≤ seamT0 X → ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
                ‖prop21RHS (fun p => liouChi χ p * (p : ℂ) ^ (-((t₀ + t : ℝ) : ℂ) * Complex.I))
                    (t₀ + t) (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
                    (1 + 1 / Real.log (k : ℝ)) (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
                  ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
                      * pretDistSq (seamCoeff (ellLin (liouChi χ)) (fun _ => 1) t₀)
                          (costwist t) X)) →
            4 ≤ Real.log X ^ ((315 : ℝ) / 1000) →
            (∫ t in (-(seamT0 X))..(seamT0 X),
                ‖dpolyA (m4BandDatum χ t₀ X) (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X (cfbC₁ X C₁) (cfbM0 K q X) := by
  obtain ⟨K, Xb, hK0, hXb0, hband⟩ := cfb_t0band_supply_chi Qm
  refine ⟨K, Xb, hK0, hXb0, ?_⟩
  intro q _ χ t₀ Y hq
  obtain ⟨X₁, hX₁0, hbandX⟩ := hband q χ t₀ Y hq
  refine ⟨X₁, hX₁0, fun X N C₁ hX1 hXb hXee hXN hN2 hC₁ ht₀ hY10 hYsq hYlow hYlog hRHS
    hbthr => ?_⟩
  exact hbandX X N C₁ (m4BandDatum χ t₀ X) hX1 hXb hXee hXN hN2 hC₁ ht₀
    (m4BandDatum_supp χ t₀ X) (m4BandDatum_eq χ t₀ X) hY10 hYsq hYlow hYlog hRHS hbthr

/-- **THE BRIDGE INTO THE `hT0band` SLOT** (`m4_t0band_of_live`).  Any coefficient sequence
agreeing with the seam coefficient on the LIVE RANGE `X < n ≤ N` inherits the band datum's
bound — `dpolyA` never reads `a` off `seamS0 N X`.  This is the A2-5 seam in its weakest
usable form (see the header). -/
theorem m4_t0band_of_live {q : ℕ} (χ : DirichletCharacter ℂ q) {t₀ X : ℝ} {N : ℕ}
    {a : ℕ → ℂ} {B : ℝ}
    (hlive : ∀ n : ℕ, X < (n : ℝ) → n ≤ N →
      a n = seamCoeff (ellLin (liouChi χ)) (fun _ => 1) t₀ n)
    (hb : (∫ t in (-(seamT0 X))..(seamT0 X),
            ‖dpolyA (m4BandDatum χ t₀ X) (seamS0 N X) t‖ ^ 2) ≤ B) :
    (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ B := by
  have hfun : (fun t : ℝ => ‖dpolyA (m4BandDatum χ t₀ X) (seamS0 N X) t‖ ^ 2)
      = fun t : ℝ => ‖dpolyA a (seamS0 N X) t‖ ^ 2 := by
    funext t
    rw [dpolyA_seamS0_bandDatum χ hlive t]
  rwa [hfun] at hb

/-! ## §6 — THE TRIVIAL BRANCH AND THE DICHOTOMY

Below the freeze's threshold `trivThresh H d₀ W = H·d₀/W³` the M4 obligation is discharged
with no analysis: the window carries at most `H′` unimodular terms, and the door's measure is
a probability measure (`M4Dyadic.integral_logMeasure_absWindowSum_le_thresh`).  The wrapper
below is the case split the dyadic consumer takes; the mean-square branch is
`m4_meansq_per_chi_gen`'s conclusion, unchanged. -/

/-- **THE SMALL BRANCH** (`m4_trivial_branch`).  A window shorter than the freeze's
threshold is discarded outright. -/
theorem m4_trivial_branch {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) {xw ω H' : ℕ}
    (hx : 2 ≤ xw) (hω : 2 ≤ ω) {Hp d₀ W : ℝ} (hH' : (H' : ℝ) ≤ trivThresh Hp d₀ W)
    (α : ℝ) :
    (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W :=
  integral_logMeasure_absWindowSum_le_thresh hx hω ha hH' α

set_option maxHeartbeats 1600000 in
-- same cause as `m4_meansq_per_chi_gen`: the binder list is re-elaborated once per branch
/-- **THE M4 PER-SCALE DICHOTOMY** (`m4_meansq_or_trivial`).  At a fixed scale the consumer
takes exactly one of two branches: the window is below the freeze's trivial threshold and is
discarded (`m4_trivial_branch`), or it is not and the five-summand mean square fires
(`m4_meansq_per_chi_gen`).  The mean-square gates are hypotheses in both branches — the split
is on the window length alone, which is what makes it usable inside the dyadic cover. -/
theorem m4_meansq_or_trivial (Qm : ℕ) :
    ∃ Cq cq T₀ X₀ Cs Ccc Kfl : ℝ,
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      ∀ (q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ : ℝ)
            (xw ω H' : ℕ) (α Hp d₀ W : ℝ),
            2 ≤ xw → 2 ≤ ω →
            (Xd : ℝ) = X → N = 2 * Xd →
            Real.exp (Real.exp 1) ≤ X → Real.exp 2 ≤ Real.log X →
            4 ≤ h → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
            Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X →
            TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
            T₀ ≤ 2 * (X / h) → Real.exp 1 ≤ 2 * (X / h) →
            Real.log X ≤ L → Real.exp 1 ≤ L →
            1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
            ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                        (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                    / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 5 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd j ≤ X) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              18 + Real.log (Real.log X)
                  - Real.log (Real.log (ramRbot (H83 X theta293) Xd j - 1))
                ≤ 32 * theta293 * Real.log (Real.log X)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              Rrad ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (3072 * M) 2)
                  (calQK (Adoor M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
                ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) →
            0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
            1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
            δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)) →
            656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293) →
            Real.exp (mrAlpha (1 / 12) 2
                * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
            0 ≤ Cb → ShortIntervalDatum Cb →
            2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X →
            X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
            (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
            pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
            Real.log X ≤ Real.log Ymax →
            32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
            420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2 →
            1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
            0 ≤ ε → ε ≤ theta293 - 1 / 500 → 8640 ≤ (Real.log X) ^ ε →
            12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
            witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail) ≤ EP2 →
            (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
            (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
            (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
            -- ⟦R3a⟧ the coprime-tail MASS, in place of the single-`P` support pin
            0 ≤ Mtail →
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤ Mtail →
            -- ⟦W1 — THE CARRIED `b`-SLOT⟧ the co-factor datum, its level family, its socket
            -- and its grade are all CARRIED now: the capstone manufactures none of them, so
            -- the row is available at ANY datum meeting them (the door's, in particular).
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (3072 * M) j ≤ p →
              p ≤ calQK (Adoor M) (3072 * M) M j → ¬ p ∣ m →
              (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
              a (p * m) = bfam j m * cf p) →
            SeamCoefW Xd P Q a b cf →
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X C₁' M₀ →
            40 * Real.log (Real.log (Real.log X))
                + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
                    + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
              < Real.log (Real.log X) →
            374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            5760 * (a2RowsSum M Xd + Ccc * (2 / (M : ℝ)))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1 M
                    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl Qm, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0 Qm, ?_⟩
  intro q _ χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ xw ω H' α Hp d₀ W hxw hω
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
    hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band hcff hgP1 hgRows hL4096
  rcases le_or_gt ((H' : ℝ)) (trivThresh Hp d₀ W) with hshort | hlong
  · exact Or.inl ⟨hshort, m4_trivial_branch ha1 hxw hω hshort α⟩
  · refine Or.inr ⟨hlong, ?_⟩
    exact hper Qm q χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
      C₁' M₀
      hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
      hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
      hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
      hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
      hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
      hε0 hεup habs hEP2 hEP2w
      ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
      hcoefBand hcoefPin
      hT0band hcff hgP1 hgRows hL4096

/-! ## §GK — the G-lever twin

The M4 mean-square page at `G := s13GK K M` (`GLever`).  All three statements are the landed
ones with `3072 * M` replaced by `s13GK K M`; the suppliers are the levered ones
(`ThmA2Rows.a2Rows_of_capfree3_gk`, `ThmA2.thm_a2'_of_rows_gk`), and every level-1 object
(`H1door M`, `a2Level1 M`) keeps its landed name.  The side condition `K ≤ 1.7·10⁸` is the
frame's, inherited through `ThmA2.calFrameK_doorH1_at_gk`. -/

theorem m4_cofactorSocket_at_witness_gk (K : ℕ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    {cf a : ℕ → ℂ} {N Xd P Q M : ℕ}
    {X h δ' VJ L Cb Rrad kmin Ymax EP2 cq T₀ X₀ : ℝ}
    (hsockA : ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (P' Q' : ℕ) (c' Cb' X' θ' : ℝ) (k₀' M' : ℕ) (t : ℝ),
        0 < c' → c' ≤ 1 / Real.exp 1 → 2 * c' < 1 → 0 ≤ Cb' → ShortIntervalDatum Cb' →
        X₀ ≤ (k₀' : ℝ) → pin2Gate ≤ (k₀' : ℝ) → k₀' ≤ M' → (M' : ℝ) ≤ 2 * (k₀' : ℝ) →
        0 ≤ cofactorMfl X' θ' (k₀' : ℝ) →
        CaseASocket2 g P' Q' c' Cb' X' θ' k₀' M' t)
    (F : A2Frame3 (ellLin (liouChi χ)) cf a N Xd P Q (Adoor M) (s13GK K M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1door M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀)
    (hX0 : 0 < X) (hh4 : 4 ≤ h) (hLXe : Real.exp 1 ≤ Real.log X)
    (hPlow : P83 X theta293 ≤ (P : ℝ)) (hQhigh : (Q : ℝ) ≤ Q83 X) (hPQ : P ≤ Q)
    (hfloor : CapFreeFloor3 (liouChi χ) X)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb) (hRrad0 : 0 < Rrad)
    (hX₀k : X₀ ≤ kmin) (hMfl0 : 0 ≤ cofactorMfl X theta293 kmin) (hk2 : 2 ≤ kmin)
    (hkk : ∀ j ∈ ramI (H83 X theta293) P Q,
      kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ))
    (hMtpin : ∀ j ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ))
    (hMtY : ∀ j ∈ ramI (H83 X theta293) P Q,
      ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) :
    CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0
      (cofactorRbd34loc (1 / Real.exp 1) Cb X theta293 kmin Ymax
        (Tstar2 Ymax (Real.log Ymax)) Rrad) (ellLin (liouChi χ)) := by
  have hgl : ∀ p : ℕ, p.Prime → ‖liouChi χ p‖ ≤ 1 := fun p _ => norm_liouChi_le_one χ p
  have he1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hh0 : (0 : ℝ) < h := by linarith
  -- ⟦the annulus at the window's TOP⟧ `2·(X/h) ≤ X` from `4 ≤ h`
  have h2aX : 2 * (X / h) ≤ X := by
    rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ hh0]
    nlinarith
  have hblkX := F.blocks X h2aX le_rfl
  -- ⟦SUPPLIER 1⟧ the collision socket, VACUOUSLY, at the centre `0`
  have hsockP : PocketSocket3 (liouChi χ) P Q X theta293 0 :=
    pocketSocket_of_floor3 hgl theta293_pos (le_of_lt theta293_lt_one_div_32) hLXe hPlow
      hQhigh hPQ hfloor 0
  -- ⟦SUPPLIER 2⟧ CASE A, from the discharged slice
  have hA2 : ∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ,
      CaseASocket2 (liouChi χ) P Q (1 / Real.exp 1) Cb X theta293
        (witKk (H83 X theta293) Xd j) (witMt (H83 X theta293) Xd j) t := by
    intro j hj t
    obtain ⟨-, -, -, -, -, -, hk₀th, -, hk₀lo, hk₀hi, -, -, hhigh, hMtop, -, -, -⟩ :=
      hblkX j hj
    have hk₀pin : pin2Gate ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans pin2Gate_le_ballQuarterThreshold hk₀th
    have hk3 : (3 : ℝ) ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans three_le_ballQuarterThreshold hk₀th
    have hkMR : ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)
        ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) := by linarith
    have hkM : witKk (H83 X theta293) Xd j ≤ witMt (H83 X theta293) Xd j := by
      exact_mod_cast hkMR
    have hM2k : ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)
        ≤ 2 * ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) := by linarith
    have hX₀kk : X₀ ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) := le_trans hX₀k (hkk j hj)
    have hMflkk : (0 : ℝ) ≤ cofactorMfl X theta293 ((witKk (H83 X theta293) Xd j : ℕ) : ℝ) :=
      le_trans hMfl0 (cofactorMfl_mono X theta293 (hkk j hj))
    exact hsockA (liouChi χ) hgl P Q (1 / Real.exp 1) Cb X theta293
      (witKk (H83 X theta293) Xd j) (witMt (H83 X theta293) Xd j) t hc0 le_rfl hc1 hCb0
      hCbound hX₀kk hk₀pin hkM hM2k hMflkk
  -- ⟦SUPPLIER 3⟧ the uniform ceiling
  have hMt1 : ∀ j ∈ ramI (H83 X theta293) P Q,
      (1 : ℝ) ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) := by
    intro j hj
    have h1 : (1 : ℝ) ≤ pin2Gate := Real.one_le_exp (by norm_num)
    exact le_trans h1 (hMtpin j hj)
  have hRbdU := Rbd34loc_uniform (H83 X theta293) P Q (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) (1 / Real.exp 1) Cb X theta293 Rrad kmin Ymax hc0 hc1 hCb0
    (by linarith) hMtpin hkk hMt1 hMtY
  exact cofactorSocket_of_ellLin hgl hc1 hCb0 hRrad0 hsockP hblkX F.box hA2 hRbdU

set_option maxHeartbeats 1600000 in
theorem m4_meansq_per_chi_gen_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ (Cq cq T₀ X₀ Cs Ccc : ℝ) (Kfl : ℕ → ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      ∀ (Qm q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ : ℝ),
            -- ⟦the two pins (FRAME's joint instantiation)⟧
            (Xd : ℝ) = X → N = 2 * Xd →
            -- ⟦the scale page⟧
            Real.exp (Real.exp 1) ≤ X → Real.exp 2 ≤ Real.log X →
            4 ≤ h → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
            Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X →
            TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
            T₀ ≤ 2 * (X / h) → Real.exp 1 ≤ 2 * (X / h) →
            Real.log X ≤ L → Real.exp 1 ≤ L →
            -- ⟦the door and the block pin `P = Q`⟧
            1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) j)
                        (calQK (Adoor M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (Adoor M) (s13GK K M) M j : ℕ) : ℝ))) →
            -- ⟦the window floors, at the witness ladder⟧
            (∀ j ∈ ramI (H83 X theta293) P Q, 5 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd j ≤ X) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              18 + Real.log (Real.log X)
                  - Real.log (Real.log (ramRbot (H83 X theta293) Xd j - 1))
                ≤ 32 * theta293 * Real.log (Real.log X)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              Rrad ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
                  (calQK (Adoor M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
                ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) →
            -- ⟦the calibration, the radius, the short-interval datum⟧
            0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
            1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
            δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)) →
            656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293) →
            Real.exp (mrAlpha (1 / 12) 2
                * Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
            0 ≤ Cb → ShortIntervalDatum Cb →
            2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X →
            -- ⟦the `kmin`/`Ymax` ladder⟧
            X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
            (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
            pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
            Real.log X ≤ Real.log Ymax →
            32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
            -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6) — inside the existential scope⟧
            420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2 →
            1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
            -- ⟦the ε-window and the Perron budget⟧
            0 ≤ ε → ε ≤ theta293 - 1 / 500 → 8640 ≤ (Real.log X) ^ ε →
            12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
            witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail) ≤ EP2 →
            -- ⟦the S8 datum⟧
            (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
            (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
            (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
            -- ⟦R3a⟧ the coprime-tail MASS, in place of the single-`P` support pin
            0 ≤ Mtail →
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤ Mtail →
            -- ⟦W1 — THE CARRIED `b`-SLOT⟧ the co-factor datum, its level family, its socket
            -- and its grade are all CARRIED now: the capstone manufactures none of them, so
            -- the row is available at ANY datum meeting them (the door's, in particular).
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
              p ≤ calQK (Adoor M) (s13GK K M) M j → ¬ p ∣ m →
              (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
              a (p * m) = bfam j m * cf p) →
            -- ⟦THE PIN CHAIN, `hwin`-FREE (⟦THE WALL⟧'s rewire): the on-window
            -- factorization ALONE.  `hwinPin` is GONE — see §3″⟧
            SeamCoefW Xd P Q a b cf →
            -- ⟦the `T₀`-band datum: `m4_t0band_at_datum` is the supplier, and §2's
            -- `dpolyA_seamS0_bandDatum` the bridge — see the header on the A2-5 seam⟧
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X C₁' M₀ →
            -- ⟦the cap-free floor's threshold⟧
            40 * Real.log (Real.log (Real.log X))
                + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
                    + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl Qm + 25)
              < Real.log (Real.log X) →
            -- ⟦the interface's two grading gates and the `4096` room⟧
            374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            5760 * (a2RowsSum_gk K M Xd + Ccc * (2 / (M : ℝ)))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
            1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
              ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + 1787702400 * a2Level1 M
                + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
                + 304128 * ballSupC ^ 2
                    * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                + 6315000 / h := by
  obtain ⟨Cq, cq, T₀, -, Cs, Ccc, hCq, hcq, hT₀, -, hCs, hCcc, hrow⟩ :=
    a2Rows_of_capfree3_gk K hK
  -- ⟦THE SOCKET CUT⟧ the CASE-A discharge is the SUPPLIER's now, so its `X₀` is taken here
  obtain ⟨X₀, hX₀0, -⟩ := caseASocket2_discharged
  -- ⟦THE SKOLEM CUT⟧ the cap-free floor constant is chosen as a FUNCTION of the modulus
  -- range, so `Qm` may be quantified inside (`M4Spine`'s ⟦WALL C⟧, the `Qm` half)
  choose Kfl hKfl0 _hcap using capFreeFloor3_liouChi_all
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, ?_⟩
  intro Qm q _ _χ _hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin _hkk _hMtY
    hRrad0 hRrad _hRlow hV1 hVδ hlogV hδsq hksthr hVJg _hCb0 _hCbound hXthr
    _hX₀k _hMfl0 _hk2 _hkX _hgateW _hYpin _hWY _hXY _hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band _hcff hgP1 hgRows hL4096
  -- ⟦THE SCALE PAGE⟧
  have hXe : Real.exp 1 ≤ X := le_trans exp_one_le_exp_exp_one hXee
  have hX3 : (3 : ℝ) ≤ X := le_of_lt (lt_of_lt_of_le exp_exp_one_gt_three hXee)
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hLX0 : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 2) hlX2
  -- ⟦THE TWO PINS, in every shape the suppliers want⟧
  have hXdX : X ≤ (Xd : ℝ) := le_of_eq hXd.symm
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by rw [hXd]; linarith
  have hXd1 : 1 ≤ Xd := by exact_mod_cast hXd1'
  have hNcast : (N : ℝ) = 2 * X := by rw [hNXd]; push_cast; rw [hXd]
  have hMN : 2 * Xd ≤ N := le_of_eq hNXd.symm
  have hNle : (N : ℝ) ≤ 2 * (Xd : ℝ) := by rw [hNcast, hXd]
  have hXN : X ≤ (N : ℝ) := by rw [hNcast]; linarith
  have hN2X : (N : ℝ) ≤ 2 * X := le_of_eq hNcast
  have hN4 : (N : ℝ) ≤ 4 * (Xd : ℝ) := by rw [hNcast, hXd]; linarith
  -- ⟦THE FRAME'S REMAINING ARITHMETIC⟧
  have hW4 : ∀ j ∈ ramI (H83 X theta293) P Q, 4 ≤ ramRbot (H83 X theta293) Xd j :=
    fun j hj => by linarith [hW5 j hj]
  have hlog2X : (0 : ℝ) ≤ 1 + Real.log (2 * X) := by
    have : (0 : ℝ) ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
    linarith
  -- ⟦⟦WALL 1⟧'s REWIRE⟧ the window-restricted BAND law is consumed AS IS now: the row's
  -- `hwin`-free four-row exit (`M4RowMR`) reads only the on-window factorization, so the
  -- widening `coef_widen_of_window` is no longer on the path (it stays as the historical
  -- instance) and `hwinBand` — ⟦THE WALL⟧'s second head — is DELETED from the statement
  -- ⟦FIELD 1–4: THE FRAME⟧ — at the CO-FACTOR DATUM `ellLin (liouChi χ)` (the socket cut's
  -- `b`-slot; the frame no longer takes a multiplicative generator)
  have F : A2Frame3 b cf a N Xd P Q (Adoor M) (s13GK K M) M 2
      (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd) (witKk (H83 X theta293) Xd)
      (H1door M) X h δ' VJ L (1 / 12) Cb Rrad EP2 cq T₀ :=
    a2Frame3_witness hX0 hh0 hLX0 hLXL hXd1 hXdX hTann hceil5 hT₀le hTbot hhceil hH2 hP3
      hlogP2 hQ0 hPQ hcq.le hQbot hQlog hQL hcqgate hW4 hkth hMN hMtX hC16 hRrad0 hRradW
      hPj1 hthinpin hXthr hMtpin hδsq hlog2X hksthr hNle hHX hcoefPin ha1 hb1 hcf1 hasupp
      Mtail hMtail0 hMtail hEP2w
  -- ⟦THE ROW LADDER⟧
  obtain ⟨hMs, hm₀2, hm₀, hMs4⟩ :=
    row_ladder_at_witness (H := H83 X theta293) (N := N) (Xd := Xd) (P := P) (Q := Q) hW5
  -- ⟦THE ROW FAMILY⟧ at the CARRIED socket (W1: no in-file manufacture — see the
  -- `liouChi` instance `m4_cofactorSocket_at_witness` / `m4_rbar_nonneg`)
  have hrows := hrow cf a b cf bfam
    hcf1 hb1 hcf1 hbf1 N Xd P Q M
    (witM0 (H83 X theta293) Xd) (witMs (H83 X theta293) Xd) (witMt (H83 X theta293) Xd)
    (witKk (H83 X theta293) Xd) X h δ' V VJ L Cb Rrad Rbar ε EP2
    hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2X hsupp0 hMN
    hcoefBand hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE FROZEN INTERFACE⟧
  exact thm_a2'_of_rows_gk K hM hXe hX3 hh4 hhX ha1 hsupp0 hN2X hTann hceil5 hrows hT0band
    hgP1 hgRows ⟨hε0, hεup⟩ hL4096

set_option maxHeartbeats 1600000 in
theorem m4_meansq_or_trivial_gk (K : ℕ) (hK : K ≤ 170000000) (Qm : ℕ) :
    ∃ Cq cq T₀ X₀ Cs Ccc Kfl : ℝ,
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      ∀ (q : ℕ) [NeZero q] (_χ : DirichletCharacter ℂ q), q ≤ Qm →
          ∀ (N Xd P Q M : ℕ) (a cf b : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ)
            (X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail C₁' M₀ : ℝ)
            (xw ω H' : ℕ) (α Hp d₀ W : ℝ),
            2 ≤ xw → 2 ≤ ω →
            (Xd : ℝ) = X → N = 2 * Xd →
            Real.exp (Real.exp 1) ≤ X → Real.exp 2 ≤ Real.log X →
            4 ≤ h → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
            Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X →
            TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
            T₀ ≤ 2 * (X / h) → Real.exp 1 ≤ 2 * (X / h) →
            Real.log X ≤ L → Real.exp 1 ≤ L →
            1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
            ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
            3 ≤ P → 2 ≤ Real.log (P : ℝ) → (Q : ℝ) ≤ 2 * (X / h) →
            Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X) →
            Real.log (Q : ℝ) ≤ L →
            P83 X theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → 0 < Q →
            H83 X theta293 ≤ (Xd : ℝ) → 2 ≤ H83 X theta293 →
            1 < ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) →
            Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
              ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
            (∀ j ∈ Finset.Icc 1 2,
              ((Nat.sqrt Xd : ℝ) + 1)
                  * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) j)
                        (calQK (Adoor M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
                ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ)
                    / Real.log ((calQK (Adoor M) (s13GK K M) M j : ℕ) : ℝ))) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 5 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd j ≤ X) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              18 + Real.log (Real.log X)
                  - Real.log (Real.log (ramRbot (H83 X theta293) Xd j - 1))
                ≤ 32 * theta293 * Real.log (Real.log X)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              Rrad ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              thinBundleG X VJ (calH (H1door M) 2) (calP (Adoor M) (s13GK K M) 2)
                  (calQK (Adoor M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
                ≤ ramRbot (H83 X theta293) Xd j) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              pin2Gate ≤ ((witMt (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              kmin ≤ ((witKk (H83 X theta293) Xd j : ℕ) : ℝ)) →
            (∀ j ∈ ramI (H83 X theta293) P Q,
              ((witMt (H83 X theta293) Xd j : ℕ) : ℝ) ≤ Ymax) →
            0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
            1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
            δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ)) →
            656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293) →
            Real.exp (mrAlpha (1 / 12) 2
                * Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
            0 ≤ Cb → ShortIntervalDatum Cb →
            2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X →
            X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
            (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
            pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
            Real.log X ≤ Real.log Ymax →
            32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
            420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2 →
            1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
            0 ≤ ε → ε ≤ theta293 - 1 / 500 → 8640 ≤ (Real.log X) ^ ε →
            12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
            witEP2 X N Xd P + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * Mtail) ≤ EP2 →
            (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
            (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
            (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
            -- ⟦R3a⟧ the coprime-tail MASS, in place of the single-`P` support pin
            0 ≤ Mtail →
            (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤ Mtail →
            -- ⟦W1 — THE CARRIED `b`-SLOT⟧ the co-factor datum, its level family, its socket
            -- and its grade are all CARRIED now: the capstone manufactures none of them, so
            -- the row is available at ANY datum meeting them (the door's, in particular).
            -- `m4_rbar_nonneg` / `m4_cofactorSocket_at_witness` remain as the `liouChi`
            -- instance that used to be built here
            (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
            0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
            CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
            (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (Adoor M) (s13GK K M) j ≤ p →
              p ≤ calQK (Adoor M) (s13GK K M) M j → ¬ p ∣ m →
              (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
              a (p * m) = bfam j m * cf p) →
            SeamCoefW Xd P Q a b cf →
            (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
              ≤ t0BandB X C₁' M₀ →
            40 * Real.log (Real.log (Real.log X))
                + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
                    + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
              < Real.log (Real.log X) →
            374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            5760 * (a2RowsSum_gk K M Xd + Ccc * (2 / (M : ℝ)))
              ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
            4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
            ((H' : ℝ) ≤ trivThresh Hp d₀ W ∧
                (∫ n, ‖absWindowSum a H' n α‖ ∂(logMeasure xw ω)) ≤ trivThresh Hp d₀ W)
              ∨ (trivThresh Hp d₀ W < (H' : ℝ) ∧
                1 / X * (∫ x in X..(2 * X),
                    ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
                  ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                    + 1787702400 * a2Level1 M
                    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
                    + 304128 * ballSupC ^ 2
                        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
                    + 6315000 / h) := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0, hper⟩ :=
    m4_meansq_per_chi_gen_gk K hK
  refine ⟨Cq, cq, T₀, X₀, Cs, Ccc, Kfl Qm, hCq, hcq, hT₀, hX₀0, hCs, hCcc, hKfl0 Qm, ?_⟩
  intro q _ χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
    C₁' M₀ xw ω H' α Hp d₀ W hxw hω
    hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
    hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
    hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 hEP2w
    ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
    hcoefBand hcoefPin
    hT0band hcff hgP1 hgRows hL4096
  rcases le_or_gt ((H' : ℝ)) (trivThresh Hp d₀ W) with hshort | hlong
  · exact Or.inl ⟨hshort, m4_trivial_branch ha1 hxw hω hshort α⟩
  · refine Or.inr ⟨hlong, ?_⟩
    exact hper Qm q χ hq N Xd P Q M a cf b bfam X h δ' V VJ L Cb Rrad Rbar kmin Ymax ε EP2 Mtail
      C₁' M₀
      hXd hNXd hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe
      hM hXdQ hQ1h hP3 hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
      hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkk hMtY
      hRrad0 hRrad hRlow hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
      hX₀k hMfl0 hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
      hε0 hεup habs hEP2 hEP2w
      ha1 hcf1 hsupp0 hasupp hMtail0 hMtail hb1 hbf1 hRbar0 hRgrade hsockR
      hcoefBand hcoefPin
      hT0band hcff hgP1 hgRows hL4096

-- #audit (temporary)

end Salt.MR
