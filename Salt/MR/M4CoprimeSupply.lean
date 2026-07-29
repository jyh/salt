/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4NonCoprime
import Salt.MR.M4DoorRow

/-!
# `M4CoprimeSupply` — THE COPRIME-SUPPLY ARM, SUPPLIED

`M4DoorClose`'s structural close carries TWO analytic arms.  This file discharges the
second — `M4NonCoprime.M4CoprimeBlockMeanSqN`, the NARROWED coprime family — from the free
row datum, by re-running `M4Maximal`'s dyadic maximal step at a FREE block `(A, B]` and a
FREE window length `L` instead of the door ladder's `(X_{i+1}, X_i]` and `H`.

## ⟦WHY A SECOND COPY OF THE MAXIMAL STEP⟧

`M4Maximal` proves the step at the ladder, where the fit is TIGHT (`doorLadder_fit`:
`B + H ≤ 2A`) and the shift pays for itself.  ⟦R2⟧'s re-indexed block is **not** a ladder
block: it misses the tight fit by `4` (`M4NonCoprime.dilBlock_reindex_fit`), and its window
length is the dilated `⌊H/d₀⌋ + 1`, not `H`.  Every χ-layer stone is already base- and
length-generic (`M4WaveClosed.classSup_le_inv_totient_sum_doorChiSup`,
`sq_inv_totient_sum_le_sum_sq`, `M4Close.inv_totient_sum_le`), so §1 is a verbatim mirror;
§2 and §3 are where the slack-`4` fit is paid, and the payment is the content of this file.

## ⟦THE LEDGER⟧ — where the free block's four units of slack go

Write `Λ = log₂L + 1`, `P = 4^{j₀}`, `α = arcDen 12 H`, and read ⟦THE NARROWING⟧
`H ≤ α·L` (the ONE hypothesis `M4CoprimeBlockMeanSqN` adds).  The assembly produces three
charges against the grade `m4BclGraded j₀ Fan Ftr H = 3Λ_H·Fan H + Λ_H·(2P/H)·Ftr H`:

1. **the analytic half** (`j₀ ≤ j`) — `Λ·Fan H·A·3L²`, which lands on the NOSE against the
   grade's first summand `3Λ_H·Fan H·L²·A`, because `L ≤ H` gives `Λ ≤ Λ_H`.  There is no
   slack in this summand and none is asked for;
2. **the trivial half** (`j < j₀`) — charged at the ABSOLUTE grade `1` (the capstone is
   never consulted below its own floor, so no row datum is read there at all): `Λ·A·2L·P`,
   which is at most HALF the grade's second summand, by ⟦G1⟧ and ⟦THE NARROWING⟧
   (`H ≤ α·L ≤ Ftr H·L/2`);
3. **the slack-`4` residue** — the free block's fit `B + L ≤ 2A + 4` costs the exchange a
   `+4` (`(2A+4)` in place of the ladder's `2A`) and the drop lemma
   `M4ClassPrice.sum_Ioc_absWindowSum_sq_div_le_slack4` costs `4·L²/A` per instance; both
   are `O((2^j)²)` with NO factor `A`, and together they total `Λ·(6·Fan H + 24)·L²`.
   This is paid by the OTHER half of the grade's second summand, and ⟦G2⟧ is exactly the
   comparison that closes it.

## ⟦THE TWO GATES⟧ (class (a) of ⟦THE FINAL REGISTER⟧ — `H`-only, consumer-choosable)

* **⟦G1⟧** `2·arcDen 12 H ≤ Ftr H` — the trivial envelope is at least the arc denominator.
  Read at `Ftr = 2·MStr` this is `arcDen 12 H ≤ MStr H`: the trivial grade is `≍ 1` (the
  block density) and `arcDen` is a fixed power of `log H`, so this is a threshold, not a
  saving.
* **⟦G2⟧** `6·Fan H + 24 ≤ 4^{j₀}` — the slack residue against the floor's own constant.
  At the door `j₀ = M·Adoor M ≥ 2^18`, so `4^{j₀}` is astronomically large and the gate is
  a formality; it is carried named because `j₀` is a PARAMETER here, never a numeral.

Both are stated on the envelopes `Fan`/`Ftr` (not on `MSan`/`MStr`) so the assembly reads
them at the grade it actually emits.

## ⟦THE REGIME FACT CARRIED⟧

`8·arcDen 12 H ≤ H` — a strengthening of `M4NonCoprime`'s own `harc` (which reads `2` in
place of `8`), and the same genre.  It is what turns ⟦THE NARROWING⟧ into `8 ≤ L`, hence
(on a non-empty block, where `A + L ≤ B + L ≤ 2A + 4`) into `L ≤ 2A` and `B ≤ 2A`: the free
block cannot be shorter than a fixed fraction of its own bottom.  Nothing below is true
without it — at `L = 4`, `A = 1`, `B = 2` the block is legal and carries no such comparison.

## ⟦THE TRAPS RESPECTED⟧

* **half-open** — every window is `Finset.Ioc n (n+K)` (through `doorSievedWindow`), every
  block and every shifted block is `Finset.Ioc A B`;
* **the log scales** — `Nat.log 2` for the dyadic count, `arcDen 12 H` (never evaluated)
  for the modulus range; no `log X`, no `loglog`;
* **`liouChi` only** — never `lamChi`; the datum is `doorChiCoeff χ M` BARE and the
  frequency is `0` throughout (`M4ClassPrice.doorCoeffPhase_zero`);
* **strict gates** — `0 < q`, `0 < A`, `R.Hlo ≤ H ≤ R.Hhi`, `0 < 2^j`, `2^j ≤ L` carried
  everywhere, never weakened;
* **the empty block** — `B < A` is legal at the interface and is discharged first: the sum
  is empty and the grade is nonnegative.  Every comparison below therefore runs under
  `A ≤ B`, which is where `L ≤ A + 4` comes from.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — TWO TRIVIAL BOUNDS ON THE SIEVED χ-TWISTED WINDOW

The datum is `1`-bounded and the sieve only deletes, so a window sum is bounded by the
window length.  Both statements below are used at the SMALL dyadic lengths, where the
capstone is silent and the absolute grade is what the split charges. -/

/-- A sieved χ-twisted window sum is bounded by its window length. -/
theorem norm_sum_doorSievedWindow_le {q : ℕ} (χ : DirichletCharacter ℂ q) (M K n : ℕ) :
    ‖∑ m ∈ doorSievedWindow M K n, liouChi χ m‖ ≤ (K : ℝ) := by
  have hsub : doorSievedWindow M K n ⊆ Finset.Ioc n (n + K) := by
    simp only [doorSievedWindow, sievedWindow]
    exact Finset.filter_subset _ _
  have hcard : (doorSievedWindow M K n).card ≤ K := by
    calc (doorSievedWindow M K n).card ≤ (Finset.Ioc n (n + K)).card :=
          Finset.card_le_card hsub
      _ = K := by simp [Nat.card_Ioc]
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ m ∈ doorSievedWindow M K n, ‖liouChi χ m‖
      ≤ ∑ _m ∈ doorSievedWindow M K n, (1 : ℝ) :=
        Finset.sum_le_sum fun m _ => norm_liouChi_le_one χ m
    _ = ((doorSievedWindow M K n).card : ℝ) := by simp
    _ ≤ (K : ℝ) := by exact_mod_cast hcard

/-- The χ-twisted sub-window sup is bounded by the window length — the length-`L` mirror of
`M4Maximal.m4_chiShiftBlock_trivial`'s inner estimate. -/
theorem doorChiSup_le_len {q : ℕ} (χ : DirichletCharacter ℂ q) (M L n : ℕ) :
    doorChiSup χ M L n ≤ (L : ℝ) := by
  unfold doorChiSup
  refine Finset.sup'_le _ _ fun K hK => ?_
  exact le_trans (norm_sum_doorSievedWindow_le χ M K n)
    (by exact_mod_cast (Finset.mem_Icc.mp hK).2)

/-! ## §1 — THE χ-REDUCTION, AT A FREE BLOCK AND A FREE LENGTH (⟦W2⟧)

`M4WaveClosed.m4_classMeanSq_of_chiMeanSq` with the two `doorLadder` literals freed to
`(A, B]` and `H` freed to `L` at the window length.  Every stone it uses is already
base- and length-generic, so this is a verbatim mirror and there is NO loss: the `1/φ(q)`
of the decomposition cancels against the character count exactly, and the only inequality
spent is the square-of-average step, which the χ-uniformity of the input makes free. -/

/-- **THE χ-UNIFORM FREE BLOCK MEAN SQUARE, NARROWED** — `M4CoprimeBlockMeanSqN`'s χ-layer:
the same free half-open block `(A, B]`, the same free window length `L` with ⟦THE
NARROWING⟧, the same slack-`4` fit, with the sub-window sup `doorChiSup` in place of the
class sup. -/
def M4CoprimeChiBlockMeanSqN (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → (H : ℝ) ≤ arcDen 12 H * (L : ℝ) →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q,
      ∀ A B : ℕ, 0 < A → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2 ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-- **THE ANTI-VACUITY WITNESS** (the house's duty, mirroring
`M4NonCoprime.m4_coprimeBlockMeanSq_trivial`).  At the trivial grade `5` the χ-layer holds
outright: each sup is `≤ L` and the fit plus `0 < A` bound the block's cardinality by `5A`.
So ALL of the interface's content is the grade. -/
theorem m4_coprimeChiBlockMeanSqN_trivial (R : ChowlaRegime) (M : ℕ) :
    M4CoprimeChiBlockMeanSqN R M (fun _ => 5) := by
  intro _ _ _ L _ _ q _ _ χ A B hA hfit
  have hterm : ∀ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2 ≤ (L : ℝ) ^ 2 := by
    intro n _
    have h := doorChiSup_le_len χ M L n
    have h0 := doorChiSup_nonneg χ M L n
    nlinarith
  have hsum : ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
      ≤ ((Finset.Ioc A B).card : ℝ) * (L : ℝ) ^ 2 := by
    calc ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
        ≤ ∑ _n ∈ Finset.Ioc A B, (L : ℝ) ^ 2 := Finset.sum_le_sum hterm
      _ = ((Finset.Ioc A B).card : ℝ) * (L : ℝ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc A B).card : ℝ) ≤ 5 * (A : ℝ) := by
    rw [Nat.card_Ioc]
    have hn : B - A ≤ 5 * A := by omega
    exact_mod_cast hn
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := sq_nonneg _
  nlinarith

/-- **⟦W2⟧ THE χ-REDUCTION AT THE FREE BLOCK** (`m4_coprimeMeanSqN_of_chiMeanSqN`) — the
narrowed coprime family from its χ-layer, at the SAME grade.  The verbatim mirror of
`M4WaveClosed.m4_classMeanSq_of_chiMeanSq`: the two `doorLadder` literals are free, the
window length is free, ⟦THE NARROWING⟧ is carried through untouched, and nothing else
changes — every χ-layer stone is base- and length-generic already. -/
theorem m4_coprimeMeanSqN_of_chiMeanSqN {R : ChowlaRegime} {M : ℕ} {Bcl : ℕ → ℝ}
    (hchi : M4CoprimeChiBlockMeanSqN R M Bcl) : M4CoprimeBlockMeanSqN R M Bcl := by
  intro H hlo hhi L hLH hnar q hq hqQ r _ hcop A B hA hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦pointwise: the χ-average, squared⟧
  have hpt : ∀ n : ℕ, (classSup (doorSievedCoeff M) L n q r) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup χ M L n) ^ 2 := by
    intro n
    have hle := classSup_le_inv_totient_sum_doorChiSup hcop M L n
    have h0 := classSup_nonneg (doorSievedCoeff M) L n q r
    have hsq : (classSup (doorSievedCoeff M) L n q r) ^ 2
        ≤ ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup χ M L n) ^ 2 := by
      nlinarith
    exact hsq.trans (sq_inv_totient_sum_le_sum_sq (fun χ => doorChiSup χ M L n))
  -- ⟦the block sum, then the χ-average and the `n`-sum commute⟧
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
  refine hstep1.trans ?_
  exact inv_totient_sum_le (fun χ => hchi H hlo hhi L hLH hnar q hq hqQ χ A B hA hfit)

/-! ## §2 — THE FREE-BASE ROW DATUM AND THE FREE SHIFTED BRIDGE (⟦W3⟧)

`M4Maximal.m4_chiShiftBlock_of_dyadicRow` with the ladder-specific steps re-derived from the
interface's slack-`4` fit.  Two things move:

* the fit `(B+s) + 2^j ≤ 2(A+s)` (the ladder's, tight) becomes `≤ 2(A+s) + 4`, so the
  supplier is `M4ClassPrice.sum_Ioc_absWindowSum_sq_div_le_slack4` — whose coverage
  hypothesis is asked for on the DROPPED block `(A+s, B+s−4]`, which is exactly the range
  the seam index set `seamS0 (2(A+s)) (A+s)` reaches;
* the exchange `B + s ≤ 2A` (the ladder's) becomes `B + s ≤ 2(A+s)`, which needs `L ≥ 4`
  (then `B ≤ 2A + 4 − L ≤ 2A`) — and `4 ≤ L` is ⟦THE NARROWING⟧ read against the regime's
  arc gate, carried as a hypothesis of the free shifted family so the bridge never guesses.

The residue is the two additive `O((2^j)²)` terms — the `+4` of the fit and the drop's
`4·(2^j)²/(A+s)` — which the family carries EXPLICITLY rather than hiding in the grade. -/

/-- **THE FREE-BASE ROW INPUT** (`M4ChiFreeRowMeanSq`) — `M4Maximal.M4ChiDyadicRowMeanSq`
with the block bottom freed: the mean square of the door's sieved, χ-twisted, UN-PHASED
datum in `ThmA2.thm_a2'_of_rows`' own currency, at the window length `h = 2^j`
(`j ≤ log₂L`) and the scale `X = A + s` (`0 < A`, `s ≤ L`), with the capstone's two pins
`X_d = X` and `N = 2X_d` intact at every instance.

**LENGTH-GRADED**: the grade is `MS j H` — one per dyadic length, ⟦WALL 2⟧'s lesson
(`M4Maximal`'s header) carried verbatim. -/
def M4ChiFreeRowMeanSq (R : ChowlaRegime) (M : ℕ) (MS : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 L,
      ∀ A : ℕ, 0 < A → ∀ s ≤ L,
        1 / ((A + s : ℕ) : ℝ)
            * (∫ y in ((A + s : ℕ) : ℝ)..(2 * ((A + s : ℕ) : ℝ)),
                ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                    * shortSum (doorChiCoeff χ M)
                        (seamS0 (2 * (A + s)) ((A + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
          ≤ MS j H

/-- **THE FREE SHIFTED FIXED-LENGTH DATUM** (`M4ChiFreeShiftBlockMeanSq`) — the block mean
square of the sieved, χ-twisted window sums at the dyadic lengths `2^j ≤ L` and at every
shift `s ≤ L` of the FREE block `(A, B]`, LENGTH-GRADED.

⟦THE RESIDUE IS EXPLICIT⟧ the right-hand side carries, beside the block term
`F j H·(2^j)²·A`, the additive `(2·F j H + 8)·(2^j)²` the slack-`4` fit and the drop cost.
Neither term has a factor `A`; §3 charges them to the graded price's SECOND summand, where
`4^{j₀}` pays for them (⟦G2⟧). -/
def M4ChiFreeShiftBlockMeanSq (R : ChowlaRegime) (M : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∀ A B : ℕ, 0 < A → 4 ≤ L → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc (A + s) (B + s),
            ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + (2 * F j H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2

/-- **ANTI-VACUITY** for the free shifted family, at the trivial grade `1` — the shape costs
nothing (`M4Maximal.m4_chiShiftBlock_trivial`'s lesson at a free block): the window sums are
bounded by their length and the block has `B − A ≤ A` cells, because `4 ≤ L` and the
interface's fit give `B ≤ 2A`. -/
theorem m4_chiFreeShiftBlock_trivial (R : ChowlaRegime) (M : ℕ) :
    M4ChiFreeShiftBlockMeanSq R M (fun _ _ => 1) := by
  intro _ _ _ L _ q _ _ χ j _ s _ A B hA hL4 hfit
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2 ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro n _
    have h := norm_sum_doorSievedWindow_le χ M (2 ^ j) n
    have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ := norm_nonneg _
    nlinarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  have hcast : ((B + s - (A + s) : ℕ) : ℝ) ≤ (A : ℝ) := by
    have hnat : B + s - (A + s) ≤ A := by omega
    exact_mod_cast hnat
  have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
  nlinarith

/-- **⟦W3⟧ THE FREE SHIFTED BRIDGE** (`m4_chiFreeShiftBlock_of_freeRow`) — the free-base,
per-length row mean square becomes the shifted block sum of squared sieved-twisted window
sums, at the grade `2·MS` plus the explicit slack residue.

The route is `M4Maximal.m4_chiShiftBlock_of_dyadicRow`'s with its two ladder facts replaced:

* `M4ClassPrice.sum_Ioc_absWindowSum_sq_div_le_slack4` at the block `(A+s, B+s]`, the scale
  `X := A + s` and the frequency `0` — its fit is `(B+s) + 2^j ≤ 2(A+s) + 4`, which is the
  interface's `B + L ≤ 2A + 4` plus `2^j ≤ L`, and its coverage runs on `(A+s, B+s−4]`,
  where `M4BridgeIntegral.hcov_of_seamS0` discharges it;
* the harmonic→flat exchange against `B + s ≤ 2(A+s)`, which is `4 ≤ L` and nothing else.
-/
theorem m4_chiFreeShiftBlock_of_freeRow {R : ChowlaRegime} {M : ℕ} {MS : ℕ → ℕ → ℝ}
    (hrow : M4ChiFreeRowMeanSq R M MS) :
    M4ChiFreeShiftBlockMeanSq R M (fun j H => 2 * MS j H) := by
  intro H hlo hhi L hLH q hq hqQ χ j hjL s hsL A B hA hL4 hfit
  have hL0 : 0 < L := by omega
  have h2j : 2 ^ j ≤ L :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjL) (Nat.pow_log_le_self 2 hL0.ne')
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAs : 0 < A + s := by omega
  have hAsR : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by exact_mod_cast hAs
  -- ⟦the fit, at the interface's slack⟧
  have hfitS : (B + s) + 2 ^ j ≤ 2 * (A + s) + 4 := by omega
  -- ⟦the coverage, on the DROPPED block⟧
  -- (the fit `(B+s−4) + 2^j ≤ 2(A+s)` is available only when the dropped block is
  -- INHABITED — at `A = 1`, `L = 4`, `B = 2`, `s = 0` it fails and the block is empty, so
  -- the membership is read first and the fit derived from it)
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
    exact hrow H hlo hhi L hLH q hq hqQ χ j hjL A hA s hsL
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

/-! ## §3 — THE MAXIMAL STEP AT A FREE BLOCK AND A FREE LENGTH (⟦W4⟧)

`M4Maximal.m4_chiBlockMeanSq_of_shiftBlock` re-run at `(A, B]` and `L`.  §4's two counts
(`dyadic_count_weight_le`, `dyadic_count_weight_small_le`) and §3's pointwise maximal bound
(`doorChiSup_sq_le_dyadic`) are all base- and length-generic, so what is new is the LEDGER:
the free block's slack-`4` residue, and the gates that pay it. -/

set_option maxHeartbeats 1600000 in
-- the dyadic assembly is `M4Maximal`'s at a free block: the triple-nested `Finset` sums
-- are re-elaborated against the free `(A, B]` and `L`, which is what costs the heartbeats
-- (no tactic search below is unbounded — every arithmetic step is `linarith` with hints)
/-- **⟦W4⟧ THE FREE MAXIMAL STEP** (`m4_coprimeChiN_of_freeShiftBlock`) — the χ-layer of the
narrowed coprime family, from the free shifted fixed-length datum, at the graded price
`m4BclGraded j₀ Fan Ftr`.

The three charges are the module header's ⟦THE LEDGER⟧: the analytic half lands on the nose
against the first summand; the trivial half is charged at the ABSOLUTE grade `1` (no row
datum is read below `j₀` at all) and takes half of the second; the slack-`4` residue takes
the other half, and ⟦G2⟧ is exactly that comparison. -/
theorem m4_coprimeChiN_of_freeShiftBlock {R : ChowlaRegime} {M : ℕ} {F : ℕ → ℕ → ℝ}
    {Fan Ftr : ℕ → ℝ} (j₀ : ℕ)
    (hFan0 : ∀ H : ℕ, 0 ≤ Fan H) (hFtr0 : ∀ H : ℕ, 0 ≤ Ftr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ Ftr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 6 * Fan H + 24 ≤ (4 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ))
    (hfix : M4ChiFreeShiftBlockMeanSq R M F) :
    M4CoprimeChiBlockMeanSqN R M (m4BclGraded j₀ Fan Ftr) := by
  classical
  intro H hlo hhi L hLH hnar q hq hqQ χ A B hA hfit
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hBcl0 : (0 : ℝ) ≤ m4BclGraded j₀ Fan Ftr H :=
    m4BclGraded_nonneg (hFan0 H) (hFtr0 H)
  -- ⟦THE NARROWING, read against the arc gate: the free length cannot be short⟧
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left
      (by have := harc8 H hlo hhi; linarith :
        arcDen 12 H * 8 ≤ arcDen 12 H * (L : ℝ)) harc0
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
  -- ⟦STEP 1⟧ the pointwise maximal bound, at the free length
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B, ((Lg : ℝ) + 1)
          * ∑ j ∈ Finset.range (Lg + 1), ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n :=
    Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic χ M L n
  -- ⟦STEP 2⟧ the sums commute
  have hswap : ∑ n ∈ Finset.Ioc A B, ((Lg : ℝ) + 1)
        * ∑ j ∈ Finset.range (Lg + 1), ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n
      = ((Lg : ℝ) + 1) * ∑ j ∈ Finset.range (Lg + 1),
          ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
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
    have hd := hfix H hlo hhi L hLH q hq hqQ χ j hjLg (2 ^ (j + 1) * t) (hsle j t ht) A B hA
      (by omega) hfit
    have hFle := han j H hj₀
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hP0 hA0R]
  -- ⟦the trivial half: the ABSOLUTE grade `1`, no row datum consulted⟧
  have hjtS : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, X j t n ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
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
  have hjL : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
      ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j := by
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
    refine hle.trans (le_of_eq ?_)
    simp only [hW]
    push_cast
    ring
  have hjS : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
      ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (A : ℝ) * W j := by
    intro j _
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1), (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun t _ => hjtS j t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    refine hle.trans (le_of_eq ?_)
    simp only [hW]
    push_cast
    ring
  -- ⟦STEP 5⟧ THE SPLIT: the full count against the analytic half, the `L`-linear head
  -- against the trivial one
  have hCan0 : (0 : ℝ) ≤ Fan H * (A : ℝ) + (2 * Fan H + 8) := by
    have := hFan0 H; nlinarith
  have hlarge : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
        ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (3 * (L : ℝ) ^ 2) := by
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
          ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j := Finset.sum_le_sum hjL
      _ ≤ ∑ j ∈ Finset.range (Lg + 1), (Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hCan0 (hW0 j))
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8)) * ∑ j ∈ Finset.range (Lg + 1), W j := by
          rw [Finset.mul_sum]
      _ ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (3 * (L : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (dyadic_count_weight_le hL0) hCan0
  have hsmall : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
        ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
      ≤ (A : ℝ) * (2 * (L : ℝ) * (4 : ℝ) ^ j₀) := by
    have hsub : (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
          ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j), (A : ℝ) * W j :=
          Finset.sum_le_sum hjS
      _ ≤ ∑ j ∈ Finset.range j₀, (A : ℝ) * W j :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg hA0R (hW0 j))
      _ = (A : ℝ) * ∑ j ∈ Finset.range j₀, W j := by rw [Finset.mul_sum]
      _ ≤ (A : ℝ) * (2 * (L : ℝ) * (4 : ℝ) ^ j₀) :=
          mul_le_mul_of_nonneg_left (dyadic_count_weight_small_le hL0 j₀) hA0R
  have hcount : ∑ j ∈ Finset.range (Lg + 1),
        ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (3 * (L : ℝ) ^ 2)
        + (A : ℝ) * (2 * (L : ℝ) * (4 : ℝ) ^ j₀) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Lg + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧
  have hLgle : (Lg : ℝ) ≤ ((Nat.log 2 H : ℕ) : ℝ) := by
    have : Nat.log 2 L ≤ Nat.log 2 H := Nat.log_mono_right hLH
    rw [hLg]
    exact_mod_cast this
  have hFtrL : 2 * (H : ℝ) ≤ Ftr H * (L : ℝ) := by
    have h1 := hG1 H hlo hhi
    have h2 : 2 * arcDen 12 H * (L : ℝ) ≤ Ftr H * (L : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hL0R.le
    linarith [hnar]
  -- ⟦the slack residue and the trivial head, together, under the second summand⟧
  have hEkey : 4 * (4 : ℝ) ^ j₀ * (L : ℝ)
      ≤ 2 * (4 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hH0R]
    linarith [mul_le_mul_of_nonneg_left hFtrL
      (by positivity : (0 : ℝ) ≤ 2 * (4 : ℝ) ^ j₀ * (L : ℝ))]
  have hres : (6 * Fan H + 24) * (L : ℝ) ^ 2 + (A : ℝ) * (2 * (L : ℝ) * (4 : ℝ) ^ j₀)
      ≤ 2 * (4 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hg2 := hG2 H hlo hhi
    have hstep : (6 * Fan H + 24) * (L : ℝ) ^ 2 ≤ (4 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ)) := by
      have h1 : (6 * Fan H + 24) * (L : ℝ) ^ 2 ≤ (4 : ℝ) ^ j₀ * (L : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hg2 (sq_nonneg _)
      linarith [mul_le_mul_of_nonneg_left hL2A
        (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ j₀ * (L : ℝ))]
    linarith [mul_le_mul_of_nonneg_right hEkey hA0R, hstep]
  -- ⟦the final comparison, summand by summand⟧
  have hb1 : (0 : ℝ) ≤ 3 * Fan H * (A : ℝ) * (L : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (by have := hFan0 H; linarith) hA0R) (sq_nonneg _)
  have hb2 : (0 : ℝ) ≤ 2 * (4 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 * (A : ℝ) :=
    mul_nonneg (mul_nonneg
      (mul_nonneg (by positivity) (hFtr0 H)) (sq_nonneg _)) hA0R
  have hgrade : ((Lg : ℝ) + 1) * ((Fan H * (A : ℝ) + (2 * Fan H + 8)) * (3 * (L : ℝ) ^ 2)
        + (A : ℝ) * (2 * (L : ℝ) * (4 : ℝ) ^ j₀))
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hin : (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (3 * (L : ℝ) ^ 2)
          + (A : ℝ) * (2 * (L : ℝ) * (4 : ℝ) ^ j₀)
        ≤ 3 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
          + 2 * (4 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
      linarith [hres]
    have h1 : ((Lg : ℝ) + 1) * ((Fan H * (A : ℝ) + (2 * Fan H + 8)) * (3 * (L : ℝ) ^ 2)
          + (A : ℝ) * (2 * (L : ℝ) * (4 : ℝ) ^ j₀))
        ≤ ((Lg : ℝ) + 1) * (3 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
            + 2 * (4 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 * (A : ℝ)) :=
      mul_le_mul_of_nonneg_left hin (by positivity)
    have h2 : ((Lg : ℝ) + 1) * (3 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
            + 2 * (4 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 * (A : ℝ))
        ≤ (((Nat.log 2 H : ℕ) : ℝ) + 1) * (3 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
            + 2 * (4 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 * (A : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h3 : (((Nat.log 2 H : ℕ) : ℝ) + 1) * (3 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
            + 2 * (4 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 * (A : ℝ))
        = m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
      unfold m4BclGraded m4Cmax
      ring
    linarith
  calc ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M L n) ^ 2
      ≤ ((Lg : ℝ) + 1) * ∑ j ∈ Finset.range (Lg + 1),
          ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n := by
        rw [← hswap]; exact hstep1
    _ ≤ ((Lg : ℝ) + 1) * ((Fan H * (A : ℝ) + (2 * Fan H + 8)) * (3 * (L : ℝ) ^ 2)
          + (A : ℝ) * (2 * (L : ℝ) * (4 : ℝ) ^ j₀)) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
    _ ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := hgrade

/-! ## §4 — THE ASSEMBLED SUPPLY

The three waves composed: the free row datum → the free shifted family (§2) → the χ-layer
of the narrowed coprime family (§3) → the narrowed coprime family itself (§1).  The grade
emitted is `M4Maximal.m4BclGraded j₀ (2·MSan) (2·MStr)` — **verbatim** the grade
`M4DoorClose`'s coprime-supply arm carries, so no register line moves. -/

/-- **THE COPRIME-SUPPLY ARM, SUPPLIED** (`m4_coprimeN_supplied`) — `M4CoprimeBlockMeanSqN`
at the grade `m4BclGraded j₀ (2·MSan) (2·MStr)`, from the free-base row datum and the
register's own envelopes.

⟦THE CONSUMPTION LIST⟧, beyond the row datum: the two envelope nonnegativities, the
analytic envelope gate `MS j H ≤ MSan H` at `j₀ ≤ j` (the trivial envelope gate is NOT
needed — the small lengths are charged at the absolute grade `1`), and the three
`H`-only class-(a) gates ⟦G1⟧, ⟦G2⟧, ⟦the regime fact⟧ of the module header. -/
theorem m4_coprimeN_supplied {R : ChowlaRegime} {M : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ} (j₀ : ℕ)
    (hMSan0 : ∀ H : ℕ, 0 ≤ MSan H) (hMStr0 : ∀ H : ℕ, 0 ≤ MStr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ MStr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 12 * MSan H + 24 ≤ (4 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ))
    (hrow : M4ChiFreeRowMeanSq R M MS) :
    M4CoprimeBlockMeanSqN R M
      (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) := by
  refine m4_coprimeMeanSqN_of_chiMeanSqN
    (m4_coprimeChiN_of_freeShiftBlock (F := fun j H => 2 * MS j H) j₀ ?_ ?_ ?_ ?_ ?_ harc8
      (m4_chiFreeShiftBlock_of_freeRow hrow))
  · intro H; have := hMSan0 H; linarith
  · intro H; have := hMStr0 H; linarith
  · intro j H hj; have := han j H hj; linarith
  · intro H hlo hhi; have := hG1 H hlo hhi; linarith
  · intro H hlo hhi; have := hG2 H hlo hhi; linarith

end Salt.MR

end
