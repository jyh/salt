/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Collapse

/-!
# `M4BaseNarrow` — ⟦BASE-NARROW⟧: the row datum's FREE BASE tied to the ladder, and THE COLLAPSE

`M4Collapse.m4_wave_closed_coprime_discharged` left ONE analytic item carried —
`M4CoprimeSupply.M4ChiFreeRowMeanSq R M MS`, the door's own row mean square at a **free**
block bottom — and named ⟦THE WALL⟧: no register discharges a free base, because at
`A ≍ 2^j` the row mean square is `≍ 1` while the grade `MS j H` above the floor is a saving,
and the capstone is silent there anyway (its coupling gate `h ≤ X(log X)^{−1/5}` fails at
`X ≍ h`).  This file performs the ruled repair and closes the M4/S9 road:

* the row datum is read AT ONE BASE (`M4RowDatumAt`), which is the currency the per-instance
  register actually speaks;
* `M4CoprimeSupply` §2/§3/§1 are re-run at that currency — each step consumes its input at
  the SAME `A` it concludes at, so the thread is mechanical and the base rides through;
* `M4NonCoprime.m4_nonCoprime_classMeanSq_N`'s two consumption sites are met from the
  register's ladder bases and their DILATIONS (⟦W5⟧'s ruled `∀d` quantifier);
* the result is `m4_wave_collapsed` — **regime + witnessed only, ZERO analytic arms**.

## ⟦WHY THE BASE IS FIXED AND NOT NARROWED BY AN INEQUALITY⟧

⟦THE WALL⟧'s repair was ruled as a base-narrowed TWIN of the row interface,
`M4ChiFreeRowMeanSqN` below: `M4ChiFreeRowMeanSq` with `Φ H · L ≤ A` inserted after
`0 < A`, at a named floor parameter `Φ : ℕ → ℝ` (the WALL's own written shape).  That twin is
what the CHAIN needs, and it is landed here (§6) together with the whole chain at it.

It is **not** what closes the register, and the reason is worth recording:
`M4ChiFreeRowMeanSqN` still quantifies over every `A` above the floor, while a register
supplies its datum at a LIST of bases.  A floor cannot turn a list into a half-line.  What
the two consumption sites of `m4_nonCoprime_classMeanSq_N` actually read is

* `A = doorLadder R.x H (i+1)`, `L = H` (the coprime branch), and
* `A = ⌊doorLadder R.x H (i+1)/d₀⌋ − 1`, `L = ⌊H/d₀⌋ + 1`, `2 ≤ d₀ ≤ arcDen 12 H` (the
  dilated branch),

and BOTH are single bases.  So the load-bearing currency here is `M4RowDatumAt` — the row
mean square at ONE `(H, L, χ, A)`, quantified over the dyadic lengths `j ≤ log₂L` and the
shifts `s ≤ L` and nothing else.  The narrowing `Φ H · L ≤ A` is then not a hypothesis of the
chain at all (the chain never inspects `A` beyond `0 < A` and the fit): it is exactly the
side condition a bundled interface must check at each site, and §6 discharges it there from
`M4Collapse.doorLadder_pow_lower`.  The honest parametrisation is therefore: **the chain at a
fixed base, the bundled twin as a corollary.**

## ⟦W5 — THE REGISTER'S `∀d` LINE⟧ (the ruled statement change, taken ADDITIVELY)

The landed exits read the per-instance register at the ladder bases,

  `∀ j ≤ log₂H, doorRowFloor M ≤ j → ∀ s ≤ H, DoorRowCarriedT0 … (X_{i+1} + s) j (MS j H)`.

`m4_wave_collapsed` reads it at the DILATED bases,

  `∀ j ≤ log₂H, doorRowFloor M ≤ j → ∀ d, 0 < d → (d:ℝ) ≤ arcDen 12 H →
     ∀ s ≤ ⌊H/d⌋ + 1, DoorRowCarriedT0 … (⌊X_{i+1}/d⌋ − 1 + s) j (MS j H)`,

i.e. the ruled `∀d` quantifier, the base dilated, the shift range dilated — and **nothing
else moves**: the `j`-range is the landed one, every conjunct of `DoorRowCarriedT0` is
untouched, and the grade slot is still `MS j H`.  The `d = 1` instance REPRODUCES the landed
line (`⌊X_{i+1}/1⌋ − 1 + (s+1) = X_{i+1} + s` and `s + 1 ≤ H + 1`), so the extension is a
strict strengthening of the demand with the landed line inside it — which is why this file
does not touch `M4DoorClose` or `M4T0Discharge`: it re-composes off
`M4DoorClose.m4_door_meansq_carried` and `M4T0Discharge.doorRowCarried_of_t0free` directly,
and both landed exits stand byte-identical.

⟦THE GATES, VERIFIED⟧ the coupling gates of `DoorRowCarriedT0` are RATIOS (`h ≤ X(log X)^{−1/5}`,
`log h + 30·log X/loglog X ≤ log X`, `T₀ ≤ 2X/h`, …) and the dilation divides `A` and the
window range by the same `d`; the ABSOLUTE thresholds (`e^e ≤ X`, `256 ≤ log X`,
`𝒬K_2 ≤ X_d`, …) are met at the dilated floor because
`⌊X_{i+1}/d⌋ − 1 ≥ R.x/(4·R.ω·arcDen 12 H) − 2` (`M4Collapse.doorLadder_pow_lower` with
`M4Close.M4DoorGates.hcount`'s `2^k ≤ 4R.ω`), and `R.x` is the consumer's own through the
`g`-arm `g R.Hhi R.ω ≤ R.x`.

## ⟦THE LEDGER IS UNCHANGED⟧

Nothing about the pricing moves: the grade emitted at each site is
`m4BclGraded (doorRowFloor M) (2·MSan) (2·MStr) H · L² · A`, verbatim
`M4CoprimeSupply.m4_coprimeN_supplied`'s, so `M4NonCoprime`'s `d0_ledger` closes the dilated
branch on the nose with `d₀²` to spare, the `q²` slot stays open, and the drift line of the
register does not move.  The three class-(a) gates ⟦G1⟧ `arcDen 12 H ^ 2 ≤ MStr H`, ⟦G2⟧
`12·MSan H + 24 ≤ 4^{j₀}` and ⟦the regime fact⟧ `8·arcDen 12 H ≤ H` are carried exactly as
`M4Collapse` carries them.

## ⟦THE TRAPS RESPECTED⟧

* **half-open** — every window is `Finset.Ioc n (n+K)` (`doorSievedWindow`), every block and
  every dilated block is `Finset.Ioc A B`;
* **the log scales** — `Nat.log 2` for the dyadic index, `arcDen 12 H` (never evaluated) for
  the modulus range, `log H` only through `arcDen` and the dilation's `M`-relative cap; no
  `log X`, no `loglog`;
* **`liouChi` only**, never `lamChi`; the datum is `doorChiCoeff χ M` BARE at frequency `0`;
* **strict gates** — `0 < q`, `0 < A`, `R.Hlo ≤ H ≤ R.Hhi`, `2 ≤ d₀` on the dilated branch,
  never weakened;
* **the ℕ-floor bookkeeping** — `⌊H/d⌋ + 1 ≤ H` needs `2 ≤ d` and `2 ≤ H`;
  `2 ≤ ⌊X_{i+1}/d⌋` needs `2d ≤ X_{i+1}`, which is `2·arcDen 12 H ≤ H < X_{i+1}`; the `±1`s
  are spent explicitly and never guessed;
* **K6** — every opaque constant (`Cq … Ctail`, `Kbox`, `X₀w`, `Cg`, `δ₀`) is bound OUTSIDE
  the instance quantifiers, its gates INSIDE.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE ROW DATUM AT ONE BASE

`M4CoprimeSupply.M4ChiFreeRowMeanSq` with the base FIXED: the mean square of the door's
sieved, χ-twisted, UN-PHASED datum in `ThmA2.thm_a2'_of_rows`' own currency, at the window
length `h = 2^j` (`j ≤ log₂L`) and the scale `X = A + s` (`s ≤ L`), with the capstone's two
pins `X_d = X` and `N = 2X_d` intact at every instance.  LENGTH-GRADED (`MS j H`, ⟦WALL 2⟧). -/

/-- **THE ROW DATUM AT ONE BASE** (`M4RowDatumAt`).  One `(H, L, χ, A)`; the dyadic lengths
`j ≤ log₂L` and the shifts `s ≤ L` are the only quantifiers left.  This is what the
per-instance register speaks, and what §2–§4 consume. -/
def M4RowDatumAt (M : ℕ) (MS : ℕ → ℕ → ℝ) (H L : ℕ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (A : ℕ) : Prop :=
  ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
    1 / ((A + s : ℕ) : ℝ)
        * (∫ y in ((A + s : ℕ) : ℝ)..(2 * ((A + s : ℕ) : ℝ)),
            ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                * shortSum (doorChiCoeff χ M)
                    (seamS0 (2 * (A + s)) ((A + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H

/-! ## §2 — THE SHIFTED BRIDGE, AT ONE BASE

`M4CoprimeSupply.m4_chiFreeShiftBlock_of_freeRow` with `(H, L, q, χ, A, B)` fixed: the free
block's slack-`4` fit is paid by `M4ClassPrice.sum_Ioc_absWindowSum_sq_div_le_slack4` (whose
coverage runs on the DROPPED block `(A+s, B+s−4]`) and the harmonic→flat exchange runs
against `B + s ≤ 2(A+s)`, which is `4 ≤ L` and nothing else. -/

/-- **THE FREE SHIFTED BRIDGE, AT ONE BASE** (`m4_freeShiftBlock_at`).  `M4CoprimeSupply` §2
at a fixed base: the per-length, per-shift row mean square becomes the shifted block sum of
squared sieved-twisted window sums, at the grade `2·MS` plus the explicit slack residue
`(2·(2·MS) + 8)·(2^j)²` — neither residue term carries a factor `A`. -/
theorem m4_freeShiftBlock_at {M H L q : ℕ} {χ : DirichletCharacter ℂ q} {MS : ℕ → ℕ → ℝ}
    {A B : ℕ} (hA : 0 < A) (hL4 : 4 ≤ L) (hfit : B + L ≤ 2 * A + 4)
    (hrow : M4RowDatumAt M MS H L χ A) :
    ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∑ n ∈ Finset.Ioc (A + s) (B + s),
          ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
  intro j hjL s hsL
  have hL0 : 0 < L := by omega
  have h2j : 2 ^ j ≤ L :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjL) (Nat.pow_log_le_self 2 hL0.ne')
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAs : 0 < A + s := by omega
  have hAsR : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by exact_mod_cast hAs
  -- ⟦the fit, at the interface's slack⟧
  have hfitS : (B + s) + 2 ^ j ≤ 2 * (A + s) + 4 := by omega
  -- ⟦the coverage, on the DROPPED block⟧
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s - 4), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff χ M m = 0 := by
    intro n hn m hm hns
    have hn' := Finset.mem_Ioc.mp hn
    have hne : A + s < B + s - 4 := lt_of_lt_of_le hn'.1 hn'.2
    exact absurd (mem_seamS0_of_block_window (X := (((A + s : ℕ)) : ℝ))
      (N := 2 * (A + s)) le_rfl (by omega) hn hm) hns
  -- ⟦the row datum, read at the removed phase⟧
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H := by
    rw [doorCoeffPhase_zero]
    exact hrow j hjL s hsL
  have hMS0 : (0 : ℝ) ≤ MS j H :=
    le_trans (meanSq_nonneg (doorCoeffPhase (doorChiCoeff χ M) 0)
      (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) ((2 ^ j : ℕ) : ℝ) hAsR) hMSrow
  -- ⟦the slack-`4` block bound⟧
  have hslack := sum_Ioc_absWindowSum_sq_div_le_slack4
    (c := doorChiCoeff χ M) (fun m => norm_doorChiCoeff_le_one χ M m)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (MS := MS j H) hh0 hAs hfitS hcov hMSrow
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H
          + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg _)
  -- ⟦the two comparisons the free block affords⟧
  have hBs2 : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) + 4 := by
    have hnat : B + s ≤ 2 * A + 4 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hBAs : (((B + s : ℕ)) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ) := by positivity
  have h1 : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
      ≤ (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) :=
    mul_le_mul_of_nonneg_right hBs2 (by positivity)
  have h2 : (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      ≤ 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) :=
    mul_le_mul_of_nonneg_right hBAs (by positivity)
  have h3 : 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    field_simp
    ring
  have hsplit : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H
        + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
        + (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    ring
  have hr : (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
      = 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + 4 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    rw [hsplit] at hex
    have hgoal : 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2
        = (2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + 4 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2) + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
    rw [hgoal, ← hr, ← h3]
    linarith
  simpa only [absWindowSum_doorChiCoeff_zero] using hfinal

/-! ## §3 — THE MAXIMAL STEP, AT ONE BASE

`M4CoprimeSupply.m4_coprimeChiN_of_freeShiftBlock` with `(H, L, q, χ, A, B)` fixed.  The
ledger is that file's, at ⟦LEVER 1′⟧'s weighted head: the analytic half lands on the nose
against the CONSTANT first summand, the trivial half is charged at the ABSOLUTE grade `1`
(no row datum is read below `j₀`), the slack-`4` residue shares the head's `(4/3)^{j₀}`
summand with it (⟦G2⟧ is that comparison), and the head's `(8/3)^{j₀}` summand is what
forces ⟦G1⟧ up to `arcDen²`. -/

set_option maxHeartbeats 1600000 in
-- the dyadic assembly is `M4Maximal`'s at a free block: the triple-nested `Finset` sums are
-- re-elaborated against the free `(A, B]` and `L`, which is what costs the heartbeats
/-- **THE FREE MAXIMAL STEP, AT ONE BASE** (`m4_chiBlock_at`).  The χ-layer of the narrowed
coprime family at a fixed base, from the shifted fixed-length datum, at the graded price
`m4BclGraded j₀ Fan Ftr`. -/
theorem m4_chiBlock_at {R : ChowlaRegime} {M H L q : ℕ} {χ : DirichletCharacter ℂ q}
    {F : ℕ → ℕ → ℝ} {Fan Ftr : ℕ → ℝ} (j₀ : ℕ) {A B : ℕ}
    (hlo : R.Hlo ≤ H) (hnar : (H : ℝ) ≤ arcDen 12 H * (L : ℝ))
    (hA : 0 < A) (hfit : B + L ≤ 2 * A + 4)
    (hFan0 : 0 ≤ Fan H) (hFtr0 : 0 ≤ Ftr H)
    (han : ∀ j : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (hG1 : 2 * arcDen 12 H ^ 2 ≤ Ftr H)
    (hG2 : 108 / 5 * Fan H + 432 / 5 ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : 8 * arcDen 12 H ≤ (H : ℝ))
    (hfix : ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∑ n ∈ Finset.Ioc (A + s) (B + s),
          ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * F j H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2)
    (hLH : L ≤ H) :
    ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
  classical
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hBcl0 : (0 : ℝ) ≤ m4BclGraded j₀ Fan Ftr H := m4BclGraded_nonneg hFan0 hFtr0
  -- ⟦THE NARROWING, read against the arc gate: the free length cannot be short⟧
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left (by linarith : arcDen 12 H * 8 ≤ arcDen 12 H * (L : ℝ)) harc0
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hL0 : 0 < L := by omega
  have hL0R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  by_cases hAB : B < A
  · -- ⟦the empty block⟧
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hBcl0 (sq_nonneg _)) (Nat.cast_nonneg _)
  rw [Nat.not_lt] at hAB
  -- ⟦the non-empty block: the fit's three consequences⟧
  have hA4 : 4 ≤ A := by omega
  have hB2A : B ≤ 2 * A := by omega
  have hL2A : (L : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : L ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set Lg := Nat.log 2 L with hLg
  set X : ℕ → ℕ → ℕ → ℝ := fun j t n =>
    ‖∑ m ∈ doorSievedWindow M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  set SL : ℝ := ∑ j ∈ Finset.range (Lg + 1), (3 / 2 : ℝ) ^ j with hSL
  have hSL0 : (0 : ℝ) ≤ SL := (geom_weight_sum_pos Lg).le
  -- ⟦STEP 1⟧ the pointwise maximal bound, at the free length and the geometric weights
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B, SL
          * ∑ j ∈ Finset.range (Lg + 1),
              (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j :=
    Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic χ M L n
  -- ⟦STEP 2⟧ the sums commute (the weight rides the `j`-index only)
  have hswap : ∑ n ∈ Finset.Ioc A B, SL
        * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j
      = SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, X j t n) * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  -- ⟦STEP 3⟧ each (scale, offset) pair is a shifted fixed-length block sum
  have hsle : ∀ j t : ℕ, t ≤ L / 2 ^ (j + 1) → 2 ^ (j + 1) * t ≤ L := by
    intro j t ht
    calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (L / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht
      _ = L / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
      _ ≤ L := Nat.div_mul_le_self L (2 ^ (j + 1))
  have hshift : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, X j t n
      = ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
          ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2 := fun j t =>
    sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2) A B _
  -- ⟦the analytic half: the datum, read through the envelope⟧
  have hjtL : ∀ j t : ℕ, j ≤ Lg → j₀ ≤ j → t ≤ L / 2 ^ (j + 1) →
      ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * Fan H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t hjLg hj₀ ht
    rw [hshift j t]
    have hd := hfix j hjLg (2 ^ (j + 1) * t) (hsle j t ht)
    have hFle := han j hj₀
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hP0 hA0R]
  -- ⟦the trivial half: the ABSOLUTE grade `1`, no row datum consulted⟧
  have hjtS : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, X j t n
      ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t
    rw [hshift j t]
    have hterm : ∀ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
        ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
      intro n _
      have h := norm_sum_doorSievedWindow_le χ M (2 ^ j) n
      have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ := norm_nonneg _
      nlinarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hcast : ((B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) : ℕ) : ℝ) ≤ (A : ℝ) := by
      have hnat : B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) ≤ A := by omega
      exact_mod_cast hnat
    have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
    nlinarith
  -- ⟦STEP 4⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j =>
    (((L / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg L j
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hjL : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hjmem := Finset.mem_filter.mp hjm
    have hjLg : j ≤ Lg := by have := Finset.mem_range.mp hjmem.1; omega
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            (Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
              + (2 * Fan H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum fun t ht =>
        hjtL j t hjLg hjmem.2 (by have := Finset.mem_range.mp ht; omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  have hjS : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j _
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1), (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun t _ => hjtS j t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (A : ℝ) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((A : ℝ) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 5⟧ THE SPLIT, at the geometric weights
  have hCan0 : (0 : ℝ) ≤ Fan H * (A : ℝ) + (2 * Fan H + 8) := by nlinarith
  have hlarge : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8))
          * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum hjL
      _ ≤ ∑ j ∈ Finset.range (Lg + 1),
            (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hCan0 (hWw0 j))
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hsub : (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
            (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := Finset.sum_le_sum hjS
      _ ≤ ∑ j ∈ Finset.range j₀, (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg hA0R (hWw0 j))
      _ = (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (Lg + 1),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
        + (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Lg + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ §4's two weighted counts, then the ledger
  have hLgN : Nat.log 2 L ≤ Nat.log 2 H := Nat.log_mono_right hLH
  have hgl1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ Lg := one_le_pow₀ (by norm_num)
  have hglg : (3 / 2 : ℝ) ^ Lg ≤ (3 / 2 : ℝ) ^ (Nat.log 2 H) := by
    rw [hLg]; gcongr; norm_num
  have hfull : SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
      ≤ 54 / 5 * (L : ℝ) ^ 2 := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_le hL0
  have hhead : SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_small_le hL0 j₀
  -- ⟦G1, STRENGTHENED⟧ the two consequences the weighted head needs
  have hFtrL : 2 * (H : ℝ) ≤ Ftr H * (L : ℝ) := by
    have h2 : 2 * arcDen 12 H * (L : ℝ) ≤ Ftr H * (L : ℝ) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hL0R.le
    linarith [hnar]
  have hFtrL2 : (H : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
    have hsq : (H : ℝ) ^ 2 ≤ (arcDen 12 H * (L : ℝ)) ^ 2 := by nlinarith [hnar, hH0R.le]
    nlinarith [hsq, sq_nonneg ((L : ℝ))]
  -- ⟦the first budget line⟧ the trivial head's `(4/3)^{j₀}` half AND the slack residue
  have hEkey : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 :=
    by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hH0R]
    have hstep : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (H : ℝ)
        ≤ 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (H : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hglg
        (by positivity : (0 : ℝ) ≤ 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ))
      nlinarith [h, hH0R.le]
    have hmain : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (H : ℝ)
        ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ * Ftr H * (L : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hFtrL
        (by positivity : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀
          * (L : ℝ))
      nlinarith [h]
    linarith
  have hres : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2
        + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hstep : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2
        ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ)) := by
      have h1 : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2 ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hG2 (sq_nonneg ((L : ℝ)))
        nlinarith [this]
      nlinarith [mul_le_mul_of_nonneg_left hL2A
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ))]
    have hgl : (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ))
        ≤ (2 / 9) * ((A : ℝ) * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg)) := by
      nlinarith [mul_le_mul_of_nonneg_left hgl1
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (A : ℝ))]
    have hbud := mul_le_mul_of_nonneg_left hEkey hA0R
    nlinarith [hstep, hgl, hbud]
  -- ⟦the second budget line⟧ the trivial head's `(8/3)^{j₀}` half — ⟦G1⟧ at `arcDen²`
  have hres2 : (A : ℝ) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    have hkey : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) := by
      have h1 : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hglg
          (by positivity : (0 : ℝ) ≤ 9 / 5 * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2)
        nlinarith [h]
      have h2 : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hFtrL2 (by positivity)
      linarith
    have hdiv : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2) := by
      have hrw : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2)
          = (9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2))
              / (H : ℝ) ^ 2 := by
        field_simp
      rw [hrw, le_div_iff₀ hH2]
      linarith [hkey]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hA0R]
  have hfinal : (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (54 / 5 * (L : ℝ) ^ 2)
        + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
          + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hexp : m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ)
        = 54 / 5 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
          + 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ) := by
      unfold m4BclGraded m4Cmax
      ring
    rw [hexp]
    nlinarith [hres, hres2]
  calc ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j := by
        rw [← hswap]; exact hstep1
    _ ≤ SL * ((Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
          + (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hSL0
    _ = (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * (SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j)
          + (A : ℝ) * (SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by ring
    _ ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (54 / 5 * (L : ℝ) ^ 2)
          + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hCan0
        have h2 := mul_le_mul_of_nonneg_left hhead hA0R
        linarith
    _ ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := hfinal

/-! ## §4 — THE χ-REDUCTION AND THE ASSEMBLED SUPPLY, AT ONE BASE

`M4CoprimeSupply` §1 at a fixed base — every χ-layer stone is base- and length-generic, so
this is a verbatim mirror and there is NO loss: the `1/φ(q)` of the decomposition cancels
against the character count exactly.  Then §2 ∘ §3 ∘ §1 composed. -/

/-- **THE χ-REDUCTION AT ONE BASE** (`m4_classBlock_at`).  The class sup's block mean square
from the χ-layer's, at the SAME grade. -/
theorem m4_classBlock_at {M L q : ℕ} (hq : 0 < q) {r : ℕ} (hcop : Nat.Coprime q r)
    {A B : ℕ} {Bc : ℝ}
    (hchi : ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2 ≤ Bc * (L : ℝ) ^ 2 * (A : ℝ)) :
    ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff M) L n q r) ^ 2
      ≤ Bc * (L : ℝ) ^ 2 * (A : ℝ) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hpt : ∀ n : ℕ, (classSup (doorSievedCoeff M) L n q r) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup χ M L n) ^ 2 := by
    intro n
    have hle := classSup_le_inv_totient_sum_doorChiSup hcop M L n
    have h0 := classSup_nonneg (doorSievedCoeff M) L n q r
    have hsq : (classSup (doorSievedCoeff M) L n q r) ^ 2
        ≤ ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup χ M L n) ^ 2 := by
      nlinarith
    exact hsq.trans (sq_inv_totient_sum_le_sum_sq (fun χ => doorChiSup χ M L n))
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff M) L n q r) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B,
          (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup χ M L n) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc A B,
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup χ M L n) ^ 2
      = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hswap] at hstep1
  exact hstep1.trans (inv_totient_sum_le hchi)

/-- **THE COPRIME BLOCK MEAN SQUARE, AT ONE BASE** (`m4_coprimeBlock_at`) — §2 ∘ §3 ∘ §4
composed at a fixed `(H, L, q, r, A, B)`, at the grade
`m4BclGraded (doorRowFloor M) (2·MSan) (2·MStr)` — **verbatim** the grade the register
carries, so no register line moves. -/
theorem m4_coprimeBlock_at {R : ChowlaRegime} {M H L q r A B : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ}
    (hlo : R.Hlo ≤ H) (hLH : L ≤ H) (hnar : (H : ℝ) ≤ arcDen 12 H * (L : ℝ))
    (hq : 0 < q) (hcop : Nat.Coprime q r) (hA : 0 < A) (hfit : B + L ≤ 2 * A + 4)
    (hMSan0 : 0 ≤ MSan H) (hMStr0 : 0 ≤ MStr H)
    (han : ∀ j : ℕ, doorRowFloor M ≤ j → MS j H ≤ MSan H)
    (hG1 : arcDen 12 H ^ 2 ≤ MStr H)
    (hG2 : 44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloor M)
    (harc8 : 8 * arcDen 12 H ≤ (H : ℝ))
    (hrow : ∀ χ : DirichletCharacter ℂ q, M4RowDatumAt M MS H L χ A) :
    ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff M) L n q r) ^ 2
      ≤ m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left (by linarith : arcDen 12 H * 8 ≤ arcDen 12 H * (L : ℝ)) harc0
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hFan0 : (0 : ℝ) ≤ 2 * MSan H := mul_nonneg (by norm_num) hMSan0
  have hFtr0 : (0 : ℝ) ≤ 2 * MStr H := mul_nonneg (by norm_num) hMStr0
  have hG1' : 2 * arcDen 12 H ^ 2 ≤ 2 * MStr H := by linarith
  have hG2' : 108 / 5 * (2 * MSan H) + 432 / 5 ≤ (4 / 3 : ℝ) ^ doorRowFloor M := by linarith
  refine m4_classBlock_at hq hcop (fun χ => ?_)
  refine m4_chiBlock_at (R := R) (F := fun j _ => 2 * MS j H) (doorRowFloor M)
    hlo hnar hA hfit hFan0 hFtr0 (fun j hj => ?_) hG1' hG2' harc8 ?_ hLH
  · have := han j hj; linarith
  · exact m4_freeShiftBlock_at hA (by omega) hfit (hrow χ)

/-! ## §5 — ⟦R2⟧ AT THE LADDER AND ITS DILATIONS

`M4NonCoprime.m4_nonCoprime_classMeanSq_N` re-run with §4's per-base supply at each of its two
consumption sites.  The dilated branch's row datum is read at `(⌊H/d₀⌋ + 1, ⌊X_{i+1}/d₀⌋ − 1)`
and the reduced modulus `q/d₀`; ⟦THE d₀-LEDGER⟧ (`M4NonCoprime.d0_ledger`) closes it at the
SAME grade — the fibre factor `d₀` is paid exactly by the dilated block's bottom. -/

set_option maxHeartbeats 1600000 in
-- `M4NonCoprime.m4_nonCoprime_classMeanSq_N`'s own cause: the dilated branch's `calc` carries
-- four nested `classSup` sums over re-indexed blocks; no tactic search happens below
/-- **⟦R2⟧ FROM THE LADDER'S ROW DATA** (`m4_classBlockMeanSq_of_rowDatum`).
`M4ClassBlockMeanSq` at EVERY class of `q`, from the row datum at the ladder bases and at
their dilations.  The two consumption sites of `m4_nonCoprime_classMeanSq_N`, and nothing
else, are what the two hypotheses `hrow1`/`hrowd` feed. -/
theorem m4_classBlockMeanSq_of_rowDatum {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ}
    (hM : 1 ≤ M) (hMSan0 : ∀ H : ℕ, 0 ≤ MSan H) (hMStr0 : ∀ H : ℕ, 0 ≤ MStr H)
    (han : ∀ j H : ℕ, doorRowFloor M ≤ j → MS j H ≤ MSan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloor M)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ))
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
    (harc : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ))
    (hrow1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
        M4RowDatumAt M MS H H χ (doorLadder R.x H (i + 1)))
    (hrowd : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ arcDen 12 H →
        M4RowDatumAt M MS H (H / d + 1) χ (doorLadder R.x H (i + 1) / d - 1)) :
    M4ClassBlockMeanSq R M k
      (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) := by
  intro H hlo hhi q hq hqQ i hik r hrq
  -- ⟦the block, and the ladder's two facts⟧
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
  have hfit : doorLadder R.x H i + H ≤ 2 * doorLadder R.x H (i + 1) := doorLadder_fit R.x H i
  have hApos : 0 < doorLadder R.x H (i + 1) := by omega
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have hH0R : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the datum at the door block, `L = H`
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]; exact hcase
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * (H : ℝ) := by nlinarith
    exact m4_coprimeBlock_at (R := R) hlo le_rfl hnarrow hq hcopqr hApos (by omega)
      (hMSan0 H) (hMStr0 H) (fun j hj => han j H hj) (hG1 H hlo hhi) (hG2 H hlo hhi)
      (harc8 H hlo hhi) (fun χ => hrow1 H hlo hhi q hq hqQ i hik χ)
  · -- ⟦d₀ > 1⟧ ONE dilation, then the `d₀`-to-one re-index of the block
    have hd2 : 2 ≤ Nat.gcd r q := by omega
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
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    -- ⟦the dilated window length⟧
    have hH'H : H / Nat.gcd r q + 1 ≤ H := by
      have hstep : H / Nat.gcd r q ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    -- ⟦THE NARROWING, at the dilated length: `H ≤ d₀·L ≤ arcDen·L`⟧
    have hdR : (Nat.gcd r q : ℝ) ≤ arcDen 12 H := by
      refine le_trans ?_ hqQ
      exact_mod_cast hdq
    have hnarrow : (H : ℝ) ≤ arcDen 12 H * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
      have hexp : Nat.gcd r q * (H / Nat.gcd r q + 1)
          = Nat.gcd r q * (H / Nat.gcd r q) + Nat.gcd r q := by ring
      have hdm : Nat.gcd r q * (H / Nat.gcd r q) + H % Nat.gcd r q = H :=
        Nat.div_add_mod H (Nat.gcd r q)
      have hmod : H % Nat.gcd r q < Nat.gcd r q := Nat.mod_lt _ hd
      have hnat : H ≤ Nat.gcd r q * (H / Nat.gcd r q + 1) := by omega
      have hR : (H : ℝ) ≤ (Nat.gcd r q : ℝ) * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hL0 : (0 : ℝ) ≤ ((H / Nat.gcd r q + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    -- ⟦the pointwise transport, then the fibre count, then the datum, then the ledger⟧
    have hpt : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff M) H n q r) ^ 2
          ≤ (fun n' => (classSup (doorSievedCoeff M) (H / Nat.gcd r q + 1) n'
                (q / Nat.gcd r q) (r / Nat.gcd r q)) ^ 2) (n / Nat.gcd r q) := by
      intro n _
      have hle := classSup_le_dilate (M := M) (H := H) (q := q) (r := r) (n := n)
        (W := arcDen 12 H) hM hq hqQ (hgate H hlo hhi)
      have h0 := classSup_nonneg (doorSievedCoeff M) H n q r
      simp only
      nlinarith
    have hmaps : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        n / Nat.gcd r q ∈ Finset.Ioc (doorLadder R.x H (i + 1) / Nat.gcd r q - 1)
          (doorLadder R.x H i / Nat.gcd r q) := fun n hn => div_mem_reindexed hd hdA hn
    have hdatum := m4_coprimeBlock_at (R := R) (MS := MS) (MSan := MSan) (MStr := MStr)
      hlo hH'H hnarrow hq₀ hcop₀ hA'pos (dilBlock_reindex_fit hd hdA hfit)
      (hMSan0 H) (hMStr0 H) (fun j hj => han j H hj) (hG1 H hlo hhi) (hG2 H hlo hhi)
      (harc8 H hlo hhi)
      (fun χ => hrowd H hlo hhi (q / Nat.gcd r q) hq₀ hq₀Q i hik χ (Nat.gcd r q) hd2 hdR)
    have hd0R : (0 : ℝ) ≤ (Nat.gcd r q : ℝ) := Nat.cast_nonneg _
    have hBcl0 : (0 : ℝ) ≤ m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H)
        (fun H => 2 * MStr H) H :=
      m4BclGraded_nonneg (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
        (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
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
            * (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
                * ((H / Nat.gcd r q + 1 : ℕ) : ℝ) ^ 2
                * ((doorLadder R.x H (i + 1) / Nat.gcd r q - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdatum hd0R
      _ ≤ m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
            * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) :=
          d0_ledger hd hH'H hBcl0

/-! ## §6 — ⟦THE BASE-NARROWED TWIN⟧ (the ruled interface, and the chain at it)

The bundled form ⟦THE WALL⟧'s repair was ruled as: `M4CoprimeSupply.M4ChiFreeRowMeanSq` with
`Φ H · L ≤ A` inserted after `0 < A`.  It is landed here beside the per-base currency, with
the whole chain at it, and the narrowing DISCHARGED at both consumption sites from
`M4Collapse.doorLadder_pow_lower`'s ladder floor.  See ⟦WHY THE BASE IS FIXED⟧ in the module
header for why the register closes through §5 and not through this. -/

/-- **THE BASE-NARROWED ROW INTERFACE** (`M4ChiFreeRowMeanSqN`) —
`M4CoprimeSupply.M4ChiFreeRowMeanSq` with ⟦THE BASE NARROWING⟧ `Φ H · L ≤ A` inserted
directly after `0 < A`, and NOTHING else changed.  Strictly weaker as a hypothesis on a
supplier, strictly stronger as a demand on a consumer. -/
def M4ChiFreeRowMeanSqN (R : ChowlaRegime) (M : ℕ) (MS : ℕ → ℕ → ℝ) (Φ : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 L,
      ∀ A : ℕ, 0 < A → Φ H * (L : ℝ) ≤ (A : ℝ) → ∀ s ≤ L,
        1 / ((A + s : ℕ) : ℝ)
            * (∫ y in ((A + s : ℕ) : ℝ)..(2 * ((A + s : ℕ) : ℝ)),
                ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                    * shortSum (doorChiCoeff χ M)
                        (seamS0 (2 * (A + s)) ((A + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
          ≤ MS j H

/-- The narrowed row interface, read at ONE base above its floor: the bridge into §1's
currency. -/
theorem m4_rowDatumAt_of_freeRowN {R : ChowlaRegime} {M : ℕ} {MS : ℕ → ℕ → ℝ} {Φ : ℕ → ℝ}
    (hrow : M4ChiFreeRowMeanSqN R M MS Φ) {H : ℕ} (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    {L : ℕ} (hLH : L ≤ H) {q : ℕ} (hq : 0 < q) (hqQ : (q : ℝ) ≤ arcDen 12 H)
    (χ : DirichletCharacter ℂ q) {A : ℕ} (hA : 0 < A) (hΦ : Φ H * (L : ℝ) ≤ (A : ℝ)) :
    M4RowDatumAt M MS H L χ A :=
  fun j hjL s hsL => hrow H hlo hhi L hLH q hq hqQ χ j hjL A hA hΦ s hsL

/-- **THE NARROWED COPRIME FAMILY, BASE-NARROWED** (`M4CoprimeBlockMeanSqNN`) —
`M4NonCoprime.M4CoprimeBlockMeanSqN` with ⟦THE BASE NARROWING⟧ `Φ H · L ≤ A` inserted
directly after `0 < A`. -/
def M4CoprimeBlockMeanSqNN (R : ChowlaRegime) (M : ℕ) (Φ : ℕ → ℝ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → (H : ℝ) ≤ arcDen 12 H * (L : ℝ) →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H → ∀ r, r < q → Nat.Coprime q r →
      ∀ A B : ℕ, 0 < A → Φ H * (L : ℝ) ≤ (A : ℝ) → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff M) L n q r) ^ 2
          ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-- **THE CHAIN AT THE BASE-NARROWED INTERFACE** (`m4_coprimeNN_supplied`) —
`M4CoprimeSupply.m4_coprimeN_supplied`'s composition with the base narrowing riding through
as a carried inequality, at the SAME grade. -/
theorem m4_coprimeNN_supplied {R : ChowlaRegime} {M : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ} {Φ : ℕ → ℝ}
    (hMSan0 : ∀ H : ℕ, 0 ≤ MSan H) (hMStr0 : ∀ H : ℕ, 0 ≤ MStr H)
    (han : ∀ j H : ℕ, doorRowFloor M ≤ j → MS j H ≤ MSan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloor M)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ))
    (hrow : M4ChiFreeRowMeanSqN R M MS Φ) :
    M4CoprimeBlockMeanSqNN R M Φ
      (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) := by
  intro H hlo hhi L hLH hnar q hq hqQ r _ hcop A B hA hΦ hfit
  exact m4_coprimeBlock_at (R := R) hlo hLH hnar hq hcop hA hfit (hMSan0 H) (hMStr0 H)
    (fun j hj => han j H hj) (hG1 H hlo hhi) (hG2 H hlo hhi) (harc8 H hlo hhi)
    (fun χ => m4_rowDatumAt_of_freeRowN hrow hlo hhi hLH hq hqQ χ hA hΦ)

/-- **THE DILATED FLOOR** (`narrow_dilate`) — the base narrowing survives the `d`-dilation:
if `Φ·H + (Φ+2)·d ≤ A` then `Φ·(⌊H/d⌋ + 1) ≤ ⌊A/d⌋ − 1`.  The two ℕ-floors are spent
explicitly — `⌊H/d⌋ ≤ H/d` costs the `Φ·d`, `⌊A/d⌋ ≥ (A − d + 1)/d` and the `−1` cost the
`2d` — and one unit is left over. -/
theorem narrow_dilate {Φ : ℝ} (hΦ0 : 0 ≤ Φ) {A H d : ℕ} (hd : 0 < d) (h1 : 1 ≤ A / d)
    (hkey : Φ * (H : ℝ) + (Φ + 2) * (d : ℝ) ≤ (A : ℝ)) :
    Φ * ((H / d + 1 : ℕ) : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hHd : ((H / d : ℕ) : ℝ) ≤ (H : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hAd : (A : ℝ) - (d : ℝ) + 1 ≤ (d : ℝ) * ((A / d : ℕ) : ℝ) := by
    have hdm : d * (A / d) + A % d = A := Nat.div_add_mod A d
    have hmod : A % d < d := Nat.mod_lt _ hd
    have hnat : A + 1 ≤ d * (A / d) + d := by omega
    have hR : ((A + 1 : ℕ) : ℝ) ≤ ((d * (A / d) + d : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hR
    linarith
  have hcast : ((A / d - 1 : ℕ) : ℝ) = ((A / d : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  have hLcast : ((H / d + 1 : ℕ) : ℝ) = ((H / d : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast, hLcast]
  -- `Φ·(⌊H/d⌋ + 1) ≤ Φ·(H/d + 1)`, and `d·(⌊A/d⌋ − 1) ≥ A − 2d + 1 ≥ Φ·H + Φ·d + 1`
  have hstep : (d : ℝ) * (Φ * (((H / d : ℕ) : ℝ) + 1)) ≤ (d : ℝ) * (((A / d : ℕ) : ℝ) - 1) := by
    have hup : (d : ℝ) * (Φ * (((H / d : ℕ) : ℝ) + 1)) ≤ Φ * (H : ℝ) + Φ * (d : ℝ) := by
      have := mul_le_mul_of_nonneg_left hHd hΦ0
      have hexp : (d : ℝ) * (Φ * (((H / d : ℕ) : ℝ) + 1))
          = (d : ℝ) * (Φ * ((H / d : ℕ) : ℝ)) + (d : ℝ) * Φ := by ring
      have hle : (d : ℝ) * (Φ * ((H / d : ℕ) : ℝ)) ≤ (d : ℝ) * (Φ * ((H : ℝ) / (d : ℝ))) :=
        mul_le_mul_of_nonneg_left this hd0.le
      have heq : (d : ℝ) * (Φ * ((H : ℝ) / (d : ℝ))) = Φ * (H : ℝ) := by
        field_simp
      rw [hexp]
      nlinarith
    nlinarith
  exact le_of_mul_le_mul_left (by linarith [hstep]) hd0

/-! ## §7 — THE REGISTER'S ROW DATA, AND ⟦THE COLLAPSE⟧

⟦W5⟧'s `∀d` register line, read twice: at `d = 1` it reproduces the landed ladder line (hence
`M4ChiDyadicRowMeanSq` and §5's `hrow1`), and at `2 ≤ d` it supplies §5's `hrowd`. -/

set_option maxHeartbeats 1600000 in
-- the same cause as `M4DoorClose` §4: the `∀d` register mentions `DoorRowCarriedT0` under
-- seven binders and is elaborated against `DoorRowCarried`'s ~85 conjuncts through the
-- bridge; no tactic search happens below
/-- **THE ROW DATA AT THE LADDER AND ITS DILATIONS** (`m4_rowDatum_dilated`), from ⟦W5⟧'s
`∀d` per-instance register.  The three outputs are exactly what
`m4_wave_closed_of_dyadicRow` and §5 consume. -/
theorem m4_rowDatum_dilated :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ)
        (Kbox X₀w : ℕ → ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧ (∀ Qm : ℕ, 0 ≤ Kbox Qm) ∧
      (∀ Qm : ℕ, 0 < X₀w Qm) ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloor M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
            doorRowFloor M ≤ j → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H →
              ∀ s ≤ H / d + 1,
                DoorRowCarriedT0 (Kbox Qm) (X₀w Qm) Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk
                    (Kcf Qm) Ctail χ M
                  (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H)) →
          (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
            ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
              M4RowDatumAt M MS H H χ (doorLadder R.x H (i + 1)))
            ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ d : ℕ, 2 ≤ d →
                (d : ℝ) ≤ arcDen 12 H →
                  M4RowDatumAt M MS H (H / d + 1) χ
                    (doorLadder R.x H (i + 1) / d - 1)) := by
  -- ⟦THE SKOLEM CUT⟧ the `T₀`-bridge's two constants, as functions of the modulus range
  choose Kbox X₀w hK0 hX₀0 hbridge using doorRowCarried_of_t0free
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hmeansq⟩ :=
    m4_door_meansq_carried
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hK0, hX₀0, ?_⟩
  intro R Qm M k MS hM hQm htriv harc hcarT0
  -- ⟦the carried form, at every dilated base⟧
  have hcar : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloor M ≤ j →
        ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H → ∀ s ≤ H / d + 1,
          DoorRowCarried Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
            (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) := by
    intro H hlo hhi q hq hqQ i hik χ j hjH hj0 d hd hdA s hsL
    haveI : NeZero q := ⟨by omega⟩
    have hqQm : q ≤ Qm := by
      have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hRq
    exact hbridge Qm Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail q χ M
      (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) hqQm
      (hcarT0 H hlo hhi q hq hqQ i hik χ j hjH hj0 d hd hdA s hsL)
  -- ⟦the mean square at every dilated base and every dyadic length⟧
  have hms : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
        ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H → ∀ s ≤ H / d + 1,
          1 / ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)
              * (∫ y in ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)..(2
                    * ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)),
                  ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                      * shortSum (doorChiCoeff χ M)
                          (seamS0 (2 * (doorLadder R.x H (i + 1) / d - 1 + s))
                            ((doorLadder R.x H (i + 1) / d - 1 + s : ℕ) : ℝ)) y
                          ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
            ≤ MS j H := by
    intro H hlo hhi q hq hqQ i hik χ j hjH d hd hdA s hsL
    -- ⟦the dilated base is positive: `2d ≤ H < X_{i+1}` forces `⌊X_{i+1}/d⌋ ≥ 2`⟧
    have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
    have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
    have h2d : 2 * d ≤ H := by
      have hR : ((2 * d : ℕ) : ℝ) ≤ (H : ℝ) := by
        push_cast
        have := harc H hlo hhi
        linarith
      exact_mod_cast hR
    have hA2 : 2 ≤ doorLadder R.x H (i + 1) / d :=
      (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hXpos : 0 < doorLadder R.x H (i + 1) / d - 1 + s := by omega
    by_cases hcase : doorRowFloor M ≤ j
    · have hqQm : q ≤ Qm := by
        have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
        exact_mod_cast hRq
      exact hmeansq Qm q χ hq hqQm M (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H) hM
        hcase
        (hcar H hlo hhi q hq hqQ i hik χ j hjH hcase d hd hdA s hsL)
    · exact le_trans (doorRow_trivial_grade χ M j hXpos) (htriv j H (not_le.mp hcase))
  constructor
  · -- ⟦the ladder bases: the `d = 1` instance at the shift `s + 1`⟧
    intro H hlo hhi q hq hqQ i hik χ j hjL s hsL
    have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
    have hAfl : H + 1 ≤ doorLadder R.x H (i + 1) := doorLadder_floor hxH (i + 1)
    have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
    have hd1 : ((1 : ℕ) : ℝ) ≤ arcDen 12 H := by push_cast; linarith
    have heq : doorLadder R.x H (i + 1) / 1 - 1 + (s + 1) = doorLadder R.x H (i + 1) + s := by
      rw [Nat.div_one]; omega
    have h := hms H hlo hhi q hq hqQ i hik χ j hjL 1 (by norm_num) hd1 (s + 1)
      (by rw [Nat.div_one]; omega)
    rwa [heq] at h
  · -- ⟦the dilated bases⟧
    intro H hlo hhi q hq hqQ i hik χ d hd2 hdA j hjL s hsL
    have hH2 : H / d + 1 ≤ H := by
      have h2d : 2 * d ≤ H := by
        have hR : ((2 * d : ℕ) : ℝ) ≤ (H : ℝ) := by
          push_cast
          have := harc H hlo hhi
          linarith
        exact_mod_cast hR
      have hstep : H / d ≤ H / 2 := Nat.div_le_div_left hd2 (by norm_num)
      omega
    exact hms H hlo hhi q hq hqQ i hik χ j (le_trans hjL (Nat.log_mono_right hH2)) d
      (by omega) hdA s hsL

/-- `arcDen 12` is monotone in the window length across the regime's range: `arcDen 12 H =
(log H)^{12}` and `log` is monotone past the regime's floor. -/
theorem arcDen_le_arcDen_Hhi (R : ChowlaRegime) {H : ℕ} (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi) :
    arcDen 12 H ≤ arcDen 12 R.Hhi := by
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hH0 : (0 : ℝ) < (H : ℝ) := by
    have : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
    linarith
  have hle : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast hhi
  have hL : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) := Real.log_le_log hH0 hle
  have hL0 : (0 : ℝ) ≤ Real.log (H : ℝ) := by
    have hLexp : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
    have := Real.exp_pos 1
    linarith
  have hnp : ∀ n : ℕ, arcDen 12 n = Real.log (n : ℝ) ^ (12 : ℕ) := by
    intro n
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hnp H, hnp R.Hhi]
  exact pow_le_pow_left₀ hL0 hL 12

/-- **⟦gate 9⟧ DISCHARGED** (`m4_modulusCap_discharged`) — the modulus cap `arcDen 12 H ≤ Qm`
at `Qm := ⌈arcDen 12 R.Hhi⌉₊`.

This is the point of the reorder: `Qm` is now chosen INSIDE, beside `M` and `k`, so it may be
read off the regime the exit produced (`M4Spine`'s ⟦WALL C⟧ named the `Qm` half "repairable by
a quantifier reorder — the constants can be selected at `Qm := ⌈arcDen 12 R.Hhi⌉₊` AFTER `R`,
through a choice function on `Qm`").  The choice functions are `m4_meansq_per_chi_gen`'s
`Kfl`, `m4_door_meansq_carried`'s `Kcf` and `m4_rowDatum_dilated`'s `Kbox`, `X₀w`.

⟦WHAT THIS DOES NOT DO⟧ ⟦WALL A⟧ (the budget collision, `M4Spine` §3) and ⟦WALL B⟧ (the
endpoint interval, §4) stand untouched.  The register is honest and `Hhi`-safe; it is still
unfulfillable. -/
theorem m4_modulusCap_discharged (R : ChowlaRegime) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ ((⌈arcDen 12 R.Hhi⌉₊ : ℕ) : ℝ) :=
  fun _ hlo hhi => le_trans (arcDen_le_arcDen_Hhi R hlo hhi) (Nat.le_ceil _)

set_option maxHeartbeats 1600000 in
-- the register mentions `DoorRowCarriedT0` under seven binders and is elaborated against
-- `m4_wave_closed_of_dyadicRow`'s own list; no tactic search happens below
/-- **THE M4 WAVE, COLLAPSED** (`m4_wave_collapsed`) — ⟦THE FINAL REGISTER⟧, regime and
witnessed data ONLY, with **no analytic arm at all**, closes the M4/S9 road:

  (the regime gates) + (the witnessed data) → `¬ logChowla2Fails R.eps R.x R.ω`.

Against `M4Collapse.m4_wave_closed_coprime_discharged` the diff is exactly TWO lines: the
per-instance register gains ⟦W5⟧'s ruled `∀d` quantifier over the DILATED bases, and the last
analytic line `M4CoprimeSupply.M4ChiFreeRowMeanSq R M MS` is GONE.  Every other byte — the
fifteen hoisted constants, the outer `(C, U1floor, g)` shape, the envelope gates, the drift
line, the two delivered lines, the modulus caps, ⟦G1⟧, ⟦G2⟧, ⟦the regime fact⟧, and the
conclusion — is identical.

## ⟦THE FINAL REGISTER⟧ — the S11 spine's consumption contract, complete

**(a) REGIME-ABSORBABLE GATES**, each an inequality in the regime's own parameters,
choosable by the spine before any datum is exhibited:

1. the OUTER shapes, chosen BEFORE `R`: `U1floor ≤ R.Hlo` and `g R.Hhi R.ω ≤ R.x` at the
   spine's own `U1floor : ℕ` and `g : ℕ → ℕ → ℕ`;
2. `M4DoorGates Cg R M k δ` — the EIGHT fields of `M4Close.M4DoorGates` (`hM`, `hδ`, `hMδ`,
   `hlogω`, `hpow`, `hcount`, `hreach`, `hblocks`);
3. `1 ≤ M`;
4. the three envelope positivities `0 ≤ MSan H`, `0 ≤ MStr H`, `0 ≤ Braw H`;
5. the two envelope gates `MS j H ≤ MSan H` at `j₀ ≤ j` and `MS j H ≤ MStr H` at `j < j₀`,
   `j₀ = doorRowFloor M = M·Adoor M`;
6. the `q`-graded drift price
   `(1 + 2π·arcDen 12 H/q)²·(q²·(3·m4BclGraded j₀ (2·MSan) (2·MStr) H)) ≤ Braw H`;
7. `√(Braw H) ≤ mrtDeliveredGrade (C/2) H`;
8. `δ/4 + 4·2^k/R.x ≤ mrtDeliveredGrade (C/2) H`;
9. the modulus cap `arcDen 12 H ≤ Qm` — with `Qm` in the WITNESSED group (beside `M`, `k`),
   so it is chosen AFTER `R`: `m4_modulusCap_discharged` closes it outright at
   `Qm := ⌈arcDen 12 R.Hhi⌉₊`;
10. the small lengths' trivial grade `4 ≤ MS j H` at `j < j₀`;
11. **the PER-INSTANCE `T₀`-free register, `∀d`** —
    `DoorRowCarriedT0 Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
    (⌊doorLadder R.x H (i+1)/d⌋ − 1 + s) j (MS j H)`, at every `H ∈ [R.Hlo, R.Hhi]`, every
    `q ≤ arcDen 12 H`, every `i < k`, every `χ mod q`, every `j ≤ log₂H` above the floor,
    every `d` with `0 < d` and `(d:ℝ) ≤ arcDen 12 H`, and every `s ≤ ⌊H/d⌋ + 1` — itself
    ~98 conjuncts (the scale page at the BLOCK scale, the band gates, the door gates, the
    socket's ~25, the tail threshold, the endpoint, the `DoorRowT0Gates` EIGHT and the
    instance envelope);
12. the dilation cap, `M`-RELATIVE: `arcDen 12 H < calP (Adoor M) (3072M) 1 = 2^{Adoor M}`
    (`M4Residue.door_dilation_gate'`) — a demand on the witnessed `M`, not a numeral cap on
    the window length (`M4Spine`'s ⟦WALL C⟧, the misplaced numeral);
13. `2·arcDen 12 H ≤ H`;
14. ⟦the regime fact⟧ `8·arcDen 12 H ≤ H`;
15. ⟦G1⟧ `arcDen 12 H ^ 2 ≤ MStr H`;
16. ⟦G2⟧ `12·MSan H + 24 ≤ 4^{j₀}`.

**(b) WITNESSED DATA** — what the spine must exhibit, and check non-vacuous: `C ≥ 0`,
`U1floor`, `g`, then `δ`, `Braw`, `MS`, `MSan`, `MStr`, `Qm`, `M`, `k`.  `Qm` sits here — not
outside — because the four opaque constants it feeds (`Kfl`, `Kcf`, `Kbox`, `X₀w`) are now
CHOICE FUNCTIONS of it (`ℕ → ℝ`), Skolemised out of their suppliers; that is what lets gates
9 and 12 be read against the regime and the door instead of against numerals.  `R` is NOT
witnessed: the exit produces it (only `R.eps = ε`, `U1floor ≤ R.Hlo`, `g R.Hhi R.ω ≤ R.x` are
visible).
The anti-vacuity duty sits at line 11, at the BOTTOM ladder rungs, the TOP dyadic length and
the LARGEST dilation `d ≍ arcDen 12 H`, where the scale page's coupling gate
`h ≤ X·(log X)^{−1/5}` bites; `hreach` and the `g`-arm are what buy the room, through
`M4Collapse.doorLadder_pow_lower` (`R.x/2^{i} ≤ X_i`) and `hcount` (`2^k ≤ 4R.ω`):
`⌊X_{i+1}/d⌋ − 1 ≥ R.x/(4·R.ω·arcDen 12 H) − 2`.

**(c) ANALYTIC ARMS** — none. -/
theorem m4_wave_collapsed :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ)
        (Kcf : ℕ → ℝ) (Ctail : ℝ) (Kbox X₀w : ℕ → ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧ (∀ Qm : ℕ, 0 ≤ Kbox Qm) ∧
      (∀ Qm : ℕ, 0 < X₀w Qm) ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (Qm M k : ℕ),
            M4DoorGates Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloor M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloor M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloor M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloor M → 4 ≤ MS j H) →
            -- ⟦THE PER-INSTANCE REGISTER, ∀d OVER THE DILATED BASES (⟦W5⟧)⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloor M ≤ j → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H →
                  ∀ s ≤ H / d + 1,
                    DoorRowCarriedT0 (Kbox Qm) (X₀w Qm) Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk
                        (Kcf Qm) Ctail χ M
                      (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦the regime fact⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦G1⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            -- ⟦G2⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloor M) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hK0, hX₀0, hdata⟩ :=
    m4_rowDatum_dilated
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr Qm M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcarT0 hgate harc harc8 hG1 hG2
  obtain ⟨hrow1, hrowd⟩ := hdata R Qm M k MS hM hQm htriv harc hcarT0
  -- ⟦the dyadic row datum: the `d = 1` family is exactly `M4ChiDyadicRowMeanSq`⟧
  have hdyad : M4ChiDyadicRowMeanSq R M k MS :=
    fun H hlo hhi q hq hqQ i hik χ j hjL s hsH =>
      hrow1 H hlo hhi q hq hqQ i hik χ j hjL s hsH
  -- ⟦R2 at every class of `q`, from the ladder's row data and their dilations⟧
  have hnc : M4ClassBlockMeanSq R M k
      (m4BclGraded (doorRowFloor M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_classBlockMeanSq_of_rowDatum hM hMSan0 hMStr0 han hG1 hG2 harc8 hgate harc
      hrow1 hrowd
  refine hR δ Braw MS MSan MStr (doorRowFloor M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest hdyad ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

set_option maxHeartbeats 1600000 in
-- the twin restates the whole register and elaborates it against the theorem above; the
-- proof itself is one destructuring
/-- **THE COLLISION FORM** (`m4_wave_collapsed_False`).  `m4_wave_collapsed`'s register with
`logChowla2Fails R.eps R.x R.ω` assumed: the chain closes to `False`.  Byte-for-byte the
theorem above with `¬ P` read as `P → False`. -/
theorem m4_wave_collapsed_False :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ)
        (Kcf : ℕ → ℝ) (Ctail : ℝ) (Kbox X₀w : ℕ → ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧ (∀ Qm : ℕ, 0 ≤ Kbox Qm) ∧
      (∀ Qm : ℕ, 0 < X₀w Qm) ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (Qm M k : ℕ),
            M4DoorGates Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloor M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloor M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloor M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloor M → 4 ≤ MS j H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloor M ≤ j → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ arcDen 12 H →
                  ∀ s ≤ H / d + 1,
                    DoorRowCarriedT0 (Kbox Qm) (X₀w Qm) Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk
                        (Kcf Qm) Ctail χ M
                      (doorLadder R.x H (i + 1) / d - 1 + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ doorRowFloor M) →
            logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩ := m4_wave_collapsed
  exact ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, hmain⟩

end Salt.MR

end
