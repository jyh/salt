/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ParsevalSingle
import Salt.MR.SeamLemma14

/-!
# S8 ladder, node A2-2 — THE COMPOSITION SPINE (`ThmA2Spine`)

Freeze: `docs/exploration/s8-freeze-0727.md` row A2-2, **as re-priced by Amendment A**
(`[C, 350–600]`, with the coefficient-contract obligation folded in).

This is the file that joins the seam-supplied calibrated rows (`SeamLemma14`,
`SeamNumber.seam_row_number`) to A2-1's single-`h` Parseval
(`ParsevalSingle.parseval_single_h`) and lands a `shortSum` statement.

## The three design questions the node was dispatched with, and their verdicts

### 1. Is `parseval_single_h`'s `hMsup` a single instance or a genuine `∀T` family?

**A GENUINE FAMILY — the single-row collapse does NOT transfer.**
`SeamLemma14.lemma14_contour_of_Msup_at` (J4′) exists because the DIFFERENCE-form
`lemma14_contour` truncates at `Tcut = 2·(X/h₁)`, exactly ONE dyadic block above
`W = X/h₁`, so its proof fires `hMsup` once, at `T = W`, where the weight `(X/h₁)/T`
is `1`.  The single-`h` assembly `contour_single_h_kernel` truncates at `2^K·W` and
feeds `Lemma14Bridge.dyadic_tail_proper`, which reads the binder at
`T = 2^k·W` for **every** `k < K` (and the binder is *stated* for every `T ≥ W`, so
the family must be produced whatever `K` is).  There is no collapse to steal.

### 2. What is the honest supply?

**THE TALL-ROW DEVICE + THE CRUDE MOMENT TAIL, split exactly where the row's own
frame runs out.**  Two facts do it:

* *(rows, `X/h ≤ T` and `2T ≤ X`)*  `SeamLemma14.seam_Msup` reads the row at height
  `2T` and returns the dyadic block `∫_T^{2T} + ∫_{−2T}^{−T}`; the seam frame's own
  ceiling `Tann ≤ X` is exactly `2T ≤ X`, so the rows reach `T = X/2` and no further.
  The weight `(X/h)/T ≤ 1` is applied to the row bound as given, so the hypothesis is
  taken in its already-weighted form (`seam_Msup_family`'s `hrows`) — that is what
  makes the family, not a single row, the honest object: the row's own right-hand side
  is `Tann`-LINEAR (`seamRowRHS`'s `(Tann·Q₁/X_d + 1)`, `(2Tann/X_d + 240)`,
  `(Tann/X + 1)` factors), so the weighted family is grade-flat while ONE row read at
  the top height `Tann = X` would inflate the §8.1 level-1 term by `h/2` (it turns
  `Tann·Q₁/X_d ≈ 2Q₁/h ≤ 2` — the interface's `[P₁,Q₁] ⊆ [1,h]` gate — into `Q₁`).
  A single tall row is therefore NOT a legal shortcut here; the dyadic family is.
* *(beyond the rows, `T > X/2`)*  the LANDED moment row `MomentsA2.moment_core_bound`
  (`∫_{−T}^{T}‖spoly‖² ≤ (2T + 20N)·Σ‖aₙ‖²/n²`) with `Σ ≤ 2/X` gives
  `(X/h)/T·(∫_T^{2T} + ∫_{−2T}^{−T}) ≤ 8/h + 80·X/(hT)`, and past `T = X/2` the
  weight has already done its work: the bound is `≤ 168/h`.  **This is why the far
  socket does NOT open here**: the freeze's named second `D`-risk (FarArm's general-`T`
  socket at `T ≍ X`) is unnecessary for the `Msup` family — the crude MVT tail is
  small *because* it is weighted, and it costs one explicit `1/h` summand.

So `Msup := Mrow + 168/h` (`seam_Msup_family`), and the `1/h` term is the ONE honest
deviation this node introduces into the `thm_A2′` interface — flagged, never absorbed.
It is harmless downstream (the S9 consumer's `h` is astronomically large) but it is a
**fifth summand** and A2-7 must carry it.  The alternative that removes it is an
A2-1 *additive variant* of `contour_single_h_kernel`/`parseval_single_h` taking the
FINITE family (`∀ k < K`) in place of `∀ T ≥ X/h` — the J4′ idiom again, ~400 ln of
re-derivation (`ParsevalSingle`'s `vsingR` scaffolding is `private`).  Not taken here.

### 3. The coefficient contract (Amendment A's obligation)

`SeamNumber.seam_row_number` demands, beside the row frame, the Lemma-12 factorization
`hcoef : a(pm) = b m · c p` (all `p` in the level band, all `m` with `p ∤ m`), the
support gate `hwin : c p · b m ≠ 0 → X_d ≤ pm ≤ 2X_d`, and (R6) `a n ≠ 0 → X_d ≤ n ≤ 2X_d`.
Amendment A recorded that the naive instantiation breaks off-window.  **The finding here
is sharper, and it is a theorem** (`seam_coef_contract_forces_vanishing`,
`seam_coef_contract_absurd`):

> `hcoef` (∀ `p` in the band) together with (R6) is not merely awkward — it FORCES `a`
> to vanish on every `p₁`-multiple with `p₁ ∤ m`, for every band prime `p₁` that is
> large enough to push some live cofactor off the window.  For the S8 datum
> (`a = 1_{(X_d,2X_d]}·g_𝒥·f`, supported on integers that HAVE a band prime — that is
> what `𝒮_K` means) that is a contradiction as soon as the band is wider than a factor
> `2`, which every calibrated band is.

The window and the factorization cannot both be global.  `RamareErr`'s own header
already names the piece `hwin` is buying for free (it kills MR p.20's SECOND seam
window, the overcount range `[2X, 2Xe^{1/H}]`, "identically zero in this
formalisation").  **The repair is a `SeamNumber`/`RamareErr` statement change —
maestro-tier, flagged, NOT taken here** (iron rule 1): relativize `hcoef`/`hwin` to the
window (`X_d ≤ pm ≤ 2X_d →` as an antecedent) and price MR's second seam window as the
fourth Lemma-12 row.  Consequently `thm_a2_spine` takes the seam row's bound as a
hypothesis (the `SeamLemma14.lemma14_contour_seam_supplied` idiom — the row as a free
real) rather than instantiating `seam_row_number`: instantiating today would produce a
statement whose contract binders are unsatisfiable at the datum.

## Glyph notes (freeze traps, all three live in this file)

* `T₀` here is `seamT0 X = (log X)^{1/15}` — never MRT's SET `𝒯₀`, never the contour
  height `(log X)²`.
* `N` is the seam row's coefficient cutoff (`X ≤ N ≤ 2X`), `K` is the Perron dyadic
  DEPTH (`2^K`).  `ParsevalSingle` calls the latter `N`; renamed here on purpose.
* the row's `Tann` is always read at `2T`, never at `T`.

## The ladder in this file

* `seam_coef_contract_forces_vanishing` / `seam_coef_contract_absurd` — the coefficient
  contract's obstruction, as a theorem (the Amendment-A obligation, resolved as a flag).
* `far_tail_crude` — the weighted moment tail past the rows' reach.
* `seam_Msup_family` — THE SUPPLY: the `∀T` family from the weighted row family.
* `thm_a2_spine` — THE EXIT, in the shape A2-7 consumes.
-/

noncomputable section

namespace Salt.MR

open MeasureTheory Complex
open scoped BigOperators

/-! ## §1 — the coefficient contract (Amendment A's obligation)

Two short stones.  They do not enter the spine's proof; they are the *design verdict*,
kernel-checked, so that the flag in `docs/blueprints/flags.md` cites a theorem instead
of an argument. -/

/-- **THE CONTRACT'S OBSTRUCTION.**  `SeamNumber.seam_row_number`'s Lemma-12
factorization `hcoef` (stated for EVERY prime `p` of the level band and every cofactor
`m` with `p ∤ m`) plus its (R6) window `a n ≠ 0 → X_d ≤ n ≤ 2X_d` force `c` to vanish
at every band prime `p₁` that carries a live cofactor off the window — and hence force
`a` to vanish on ALL `p₁`-multiples with coprime cofactor.

Read at the S8 datum this is fatal: `a` is supported on `𝒮_K`, whose members are
*required* to have a prime factor in each band, and the band is wider than a factor `2`,
so such a `p₁` always exists. -/
theorem seam_coef_contract_forces_vanishing {a b c : ℕ → ℂ} {P Q Xd : ℕ}
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hcoef : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    {p₀ p₁ m₀ : ℕ} (hp₀ : p₀.Prime) (hP₀ : P ≤ p₀) (hQ₀ : p₀ ≤ Q) (hd₀ : ¬ p₀ ∣ m₀)
    (hlive : a (p₀ * m₀) ≠ 0)
    (hp₁ : p₁.Prime) (hP₁ : P ≤ p₁) (hQ₁ : p₁ ≤ Q) (hd₁ : ¬ p₁ ∣ m₀)
    (hoff : 2 * Xd < p₁ * m₀) :
    ∀ m : ℕ, ¬ p₁ ∣ m → a (p₁ * m) = 0 := by
  have hb : b m₀ ≠ 0 := by
    intro hb0
    exact hlive (by rw [hcoef p₀ m₀ hp₀ hP₀ hQ₀ hd₀, hb0, zero_mul])
  have hz : a (p₁ * m₀) = 0 := by
    by_contra hne
    exact absurd (hasupp _ hne).2 (Nat.not_le.mpr hoff)
  have hc0 : c p₁ = 0 := by
    have hEq := hcoef p₁ m₀ hp₁ hP₁ hQ₁ hd₁
    rw [hz] at hEq
    rcases mul_eq_zero.mp hEq.symm with hh | hh
    · exact absurd hh hb
    · exact hh
  intro m hm
  rw [hcoef p₁ m hp₁ hP₁ hQ₁ hm, hc0, mul_zero]

/-- **THE CONTRACT IS UNSATISFIABLE AT A LIVE DATUM.**  The same hypotheses, plus one
further live coefficient `a (p₁ * m₁) ≠ 0` with `p₁ ∤ m₁` — i.e. exactly what
"`a` is supported on integers having a band prime" provides — are contradictory.

This is the precise form of Amendment A's "the support gate fails off-window": it is
not a bad *choice* of `(b,c)`, there is no choice.  Repair = the window-relativized
`hcoef`/`hwin` twin + MR's second seam window priced (`RamareErr` header). -/
theorem seam_coef_contract_absurd {a b c : ℕ → ℂ} {P Q Xd : ℕ}
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hcoef : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    {p₀ p₁ m₀ m₁ : ℕ} (hp₀ : p₀.Prime) (hP₀ : P ≤ p₀) (hQ₀ : p₀ ≤ Q) (hd₀ : ¬ p₀ ∣ m₀)
    (hlive : a (p₀ * m₀) ≠ 0)
    (hp₁ : p₁.Prime) (hP₁ : P ≤ p₁) (hQ₁ : p₁ ≤ Q) (hd₁ : ¬ p₁ ∣ m₀)
    (hoff : 2 * Xd < p₁ * m₀)
    (hd : ¬ p₁ ∣ m₁) (hwit : a (p₁ * m₁) ≠ 0) : False :=
  hwit (seam_coef_contract_forces_vanishing hasupp hcoef hp₀ hP₀ hQ₀ hd₀ hlive
    hp₁ hP₁ hQ₁ hd₁ hoff m₁ hd)

/-! ## §2 — the crude moment tail (past the rows' reach) -/

/-- The `ℓ²` coefficient mass of a `1`-bounded coefficient supported above `X`, at the
seam's dyadic length: `Σ_{n ≤ N} ‖aₙ‖²/n² ≤ 2/X`.  (Each live term is `≤ 1/X²`, and
`N ≤ 2X`.) -/
private lemma seam_coeff_massSq_le {N : ℕ} {a : ℕ → ℂ} {X : ℝ} (hX0 : 0 < X)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X) :
    ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 2 / X := by
  have hXne : X ≠ 0 := hX0.ne'
  have hterm : ∀ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / X ^ 2 := by
    intro n _
    rcases le_or_gt (n : ℝ) X with hn | hn
    · rw [hsupp n hn, norm_zero]
      have hz : (0 : ℝ) ≤ 1 / X ^ 2 := by positivity
      simpa using hz
    · have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans hX0 hn
      have h1 : ‖a n‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (a n), ha n]
      have h2 : X ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
      calc ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) ^ 2 := by gcongr
        _ ≤ 1 / X ^ 2 := by
            exact one_div_le_one_div_of_le (by positivity) h2
  calc ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ ∑ _n ∈ Finset.Icc 1 N, 1 / X ^ 2 := Finset.sum_le_sum hterm
    _ = (N : ℝ) * (1 / X ^ 2) := by
        simp [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    _ ≤ (2 * X) * (1 / X ^ 2) := mul_le_mul_of_nonneg_right hN2 (by positivity)
    _ = 2 / X := by field_simp

/-- **THE CRUDE WEIGHTED TAIL.**  For any `T > 0`, the weighted dyadic block of the
concrete Dirichlet polynomial obeys

  `(X/h)/T·(∫_T^{2T}‖A‖² + ∫_{−2T}^{−T}‖A‖²) ≤ 8/h + 80·X/(hT)`,

by the landed moment row `MomentsA2.moment_core_bound` on `[−2T, 2T]` and the mass
bound `Σ‖aₙ‖²/n² ≤ 2/X`.  Past `T = X/2` — exactly where the seam row's own frame
ceiling `Tann ≤ X` stops it — this reads `≤ 168/h`.

This is the stone that keeps FarArm's general-`T` socket (the freeze's named second
`D`-risk) OUT of the spine: the far family is paid crudely because it is paid
*weighted*. -/
theorem far_tail_crude {N : ℕ} {a : ℕ → ℂ} {X h T : ℝ} (hX0 : 0 < X) (hh0 : 0 < h)
    (hT0 : 0 < T) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X) :
    X / h / T * ((∫ t in T..(2 * T), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
        + ∫ t in (-(2 * T))..(-T), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      ≤ 8 / h + 80 * (X / (h * T)) := by
  have hc : Continuous (fun t : ℝ => ‖dpolyA a (seamS0 N X) t‖ ^ 2) :=
    dpolyA_seamS0_normSq_continuous hX0.le
  have hAeq : ∀ t : ℝ, ‖dpolyA a (seamS0 N X) t‖ ^ 2 = ‖spoly N a t‖ ^ 2 := by
    intro t; rw [spoly_eq_dpolyA_filter hsupp t]
  -- the three-way split of `[−2T, 2T]`
  have e1 : (∫ t in (-(2 * T))..(-T), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
        + (∫ t in (-T)..(2 * T), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      = ∫ t in (-(2 * T))..(2 * T), ‖dpolyA a (seamS0 N X) t‖ ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
  have e2 : (∫ t in (-T)..T, ‖dpolyA a (seamS0 N X) t‖ ^ 2)
        + (∫ t in T..(2 * T), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      = ∫ t in (-T)..(2 * T), ‖dpolyA a (seamS0 N X) t‖ ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
  have emid : (0 : ℝ) ≤ ∫ t in (-T)..T, ‖dpolyA a (seamS0 N X) t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
  -- the landed moment row on `[−2T, 2T]`
  have hmom : (∫ t in (-(2 * T))..(2 * T), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      ≤ 8 * T / X + 80 := by
    have hcongr : (∫ t in (-(2 * T))..(2 * T), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
        = ∫ t in (-(2 * T))..(2 * T), ‖spoly N a t‖ ^ 2 :=
      intervalIntegral.integral_congr (fun t _ => hAeq t)
    rw [hcongr]
    refine (moment_core_bound N a (2 * T)).trans ?_
    have hmass := seam_coeff_massSq_le hX0 ha hsupp hN2
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hpre : (0 : ℝ) ≤ 2 * (2 * T) + 20 * (N : ℝ) := by linarith
    have hXnn : (0 : ℝ) ≤ 2 / X := by positivity
    calc (2 * (2 * T) + 20 * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ (2 * (2 * T) + 20 * (N : ℝ)) * (2 / X) :=
          mul_le_mul_of_nonneg_left hmass hpre
      _ ≤ (4 * T + 40 * X) * (2 / X) := by
          have h20 : 20 * (N : ℝ) ≤ 40 * X := by linarith
          nlinarith [hXnn, h20]
      _ = 8 * T / X + 80 := by field_simp; ring
  -- assemble
  have hw : (0 : ℝ) ≤ X / h / T := by positivity
  have hchain : (∫ t in T..(2 * T), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      + (∫ t in (-(2 * T))..(-T), ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ 8 * T / X + 80 := by
    linarith
  refine (mul_le_mul_of_nonneg_left hchain hw).trans (le_of_eq ?_)
  field_simp

/-! ## §3 — THE SUPPLY: the `∀T` family from the weighted row family -/

/-- `5 ≤ loglog` is monotone upward — the seam frame's `h`-ceiling gate, transferred
from the designed height `2X/h` to every larger annulus height.

The two positivity hypotheses are NOT decoration: `Real.log` is even-ish junk below `0`
(`log x = log |x|`, `log 0 = 0`), so `5 ≤ loglog u` alone is satisfied by
`u = e^{−e⁵}` and monotonicity would be false there.  Both are supplied at the call
site by `TannGate` (which forces `Tann > 1`). -/
private lemma five_le_loglog_mono {u v : ℝ} (hu0 : 0 < u) (hlu : 0 < Real.log u)
    (huv : u ≤ v) (h5 : 5 ≤ Real.log (Real.log u)) : 5 ≤ Real.log (Real.log v) :=
  h5.trans (Real.log_le_log hlu (Real.log_le_log hu0 huv))

/-- **THE `Msup` SUPPLY** (`seam_Msup_family`).  `parseval_single_h`'s far-family binder,
produced from the seam rows where they reach and from the crude weighted moment tail
past that, at

  `Msup := Mrow + 168/h`.

The row hypothesis is taken in its ALREADY-WEIGHTED form, at every height `2T` the seam
frame admits (`2T ≤ X` is the frame's own `Tann ≤ X`), with the frame's two `Tann`-side
gates — `TannGate` and the `h`-ceiling `5 ≤ loglog Tann` — as antecedents; the caller
meets them once, at the designed height `Tann = 2X/h`, and this proof transfers them
upward (both are monotone in the height).

Grade note: the weighted form is what keeps the supply honest.  `seamRowRHS` is
`Tann`-linear, so `(X/h)/T·Row(2T)` is flat in `T` while `Row(X)` — one tall row at the
frame ceiling — would inflate the §8.1 level-1 term by `h/2`. -/
theorem seam_Msup_family {N : ℕ} {a : ℕ → ℂ} {X h Mrow : ℝ}
    (hX : Real.exp 1 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2) ≤ Mrow) :
    ∀ T : ℝ, X / h ≤ T →
      X / h / T * ((∫ t in T..(2 * T), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
          + ∫ t in (-(2 * T))..(-T), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
        ≤ Mrow + 168 / h := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hX1 : (1 : ℝ) < X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hWpos : (0 : ℝ) < X / h := div_pos hX0 hh0
  have hT0W : seamT0 X ≤ X / h := seamT0_le_div hX hh1 le_rfl hhX
  have h2W : 2 * (X / h) ≤ X := by
    have hkey : 2 * (X / h) = 2 * X / h := by ring
    rw [hkey, div_le_iff₀ hh0]
    nlinarith
  -- the annulus height at the designed place exceeds `1` (`TannGate`), so `loglog` is
  -- past its junk region and the frame's `h`-ceiling transfers upward
  have hTann' : Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) ≤ 2 * (X / h) := hTann
  have hLXpos : (0 : ℝ) < Real.log X := Real.log_pos hX1
  have hrp0 : (0 : ℝ) < (Real.log X) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hLXpos _
  have hT1 : (1 : ℝ) < 2 * (X / h) := by
    have hexp := Real.add_one_le_exp (30 * (Real.log X) ^ ((1 : ℝ) / 2))
    linarith
  have hWlog : (0 : ℝ) < Real.log (2 * (X / h)) := Real.log_pos hT1
  -- `Mrow ≥ 0`, read off the row at the designed height
  have hMrow0 : (0 : ℝ) ≤ Mrow := by
    have hW := hrows (X / h) le_rfl h2W hTann hceil
    rw [div_self hWpos.ne', one_mul] at hW
    have hnn : (0 : ℝ) ≤ ∫ t in seamAnn X (2 * (X / h)), ‖spoly N a t‖ ^ 2 :=
      integral_nonneg (fun t => by positivity)
    linarith
  intro T hT
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le hWpos hT
  have hw : (0 : ℝ) ≤ X / h / T := by positivity
  rcases le_or_gt (2 * T) X with hcase | hcase
  · -- inside the rows' reach
    have hTT0 : seamT0 X ≤ T := le_trans hT0W hT
    have hgate : TannGate X (2 * T) := le_trans hTann (by linarith)
    have hceilT : 5 ≤ Real.log (Real.log (2 * T)) :=
      five_le_loglog_mono (by linarith) hWlog (by linarith) hceil
    have hrow := hrows T hT hcase hgate hceilT
    have hblock := seam_Msup (N := N) (a := a) (X := X) (W := T) hX1 hsupp hTT0 le_rfl
    have hstep := mul_le_mul_of_nonneg_left hblock hw
    have htail : (0 : ℝ) ≤ 168 / h := by positivity
    linarith
  · -- past the rows' reach: the crude weighted tail
    have hcr := far_tail_crude (N := N) (a := a) hX0 hh0 hTpos ha hsupp hN2
    have hXT : X / (h * T) ≤ 2 / h := by
      rw [div_le_div_iff₀ (by positivity) hh0]
      nlinarith
    have hb1 : 80 * (X / (h * T)) ≤ 160 / h := by
      calc 80 * (X / (h * T)) ≤ 80 * (2 / h) :=
            mul_le_mul_of_nonneg_left hXT (by norm_num)
        _ = 160 / h := by ring
    have hb2 : (8 : ℝ) / h + 160 / h = 168 / h := by ring
    linarith

/-! ## §4 — THE EXIT -/

/-- **A2-2 — THE COMPOSITION SPINE** (`thm_a2_spine`).  The single-`h` mean square of the
half-open short sum, priced by the seam rows:

`(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
`  ≤ (1/2π²)·[ 236365π·Mrow + 205π·B₀ + 39674880π/h + Egap(K,δ) ]`

where

* `Mrow` bounds the WEIGHTED seam-row family `(X/h)/T·∫_{Ann(T₀,2T)}‖A(1+it)‖² dt` over
  every height the seam frame admits (`X/h ≤ T`, `2T ≤ X`, `TannGate`, the `h`-ceiling);
  it pays BOTH of Lemma 14's analytic terms — the mid band `T₀ ≤ |t| ≤ X/h` (through
  `SeamLemma14.seam_midrange_of_tall_row`, the `T = X/h` instance, where the weight is
  `1`) and the whole far family (`seam_Msup_family`);
* `B₀` bounds the `T₀`-BAND `∫_{−T₀}^{T₀}‖A(1+it)‖² dt`, `T₀ = seamT0 X = (log X)^{1/15}`
  — **carried, by design**: this is the summand A2-1 left open and A2-3/A2-3b's cap-free
  arm discharges.  Nothing here touches it;
* `39674880π/h` is the crude weighted moment tail past the rows' reach
  (`far_tail_crude`) — the ONE honest deviation of this node, a fifth interface
  summand, never absorbed;
* `Egap(K,δ) = 34560·δ·(π + 2log(1 + 2^K·X/h))² + 1152·(12h/(2^K δ) + (8h/2^K)(1+log 3X))²`
  is A2-1's Perron defect, unchanged, `→ 0` along `δ = 2^{−K/2}`.

Side conditions, all in-statement: `exp 1 ≤ X`; `4 ≤ h` (the AS-2 MVT guard at the far
height — NOT `3`, and NOT `2`); `h ≤ X(log X)^{−1/5}` (Lemma 14's window frame);
`0 < δ ≤ 1`; `‖aₙ‖ ≤ 1` (the row's R5) and `a` supported above `X` (the row's `hsupp`,
which is what makes `seamS0 N X` the right index set); `N ≤ 2X` (the row's dyadic pin,
from which `hrange` is DERIVED, `seamS0_range`); `TannGate X (2X/h)` and
`5 ≤ loglog(2X/h)` (the seam frame at the designed height — equivalently the freeze's
`h`-ceiling `h ≤ 2X·e^{−e⁵}`).

The row frame's remaining sixty binders (`CalFrameK`, R1–R6, the `𝒰`-side gates, the
`hSup` binder) live inside `Mrow`'s supplier, `SeamNumber.seam_row_number`, and are
cited rather than restated — see this file's header for why that indirection is
currently *load-bearing* (the coefficient contract R5/R6-vs-`hcoef` obstruction). -/
theorem thm_a2_spine {N : ℕ} {a : ℕ → ℂ} {X h Mrow B₀ δ : ℝ} (K : ℕ)
    (hX : Real.exp 1 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2) ≤ Mrow)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ B₀) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 1 / (2 * Real.pi ^ 2)
          * (236365 * Real.pi * Mrow + 205 * Real.pi * B₀ + 39674880 * Real.pi / h
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ K * δ)
                  + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2)) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hX2 : (2 : ℝ) ≤ X := le_trans he2 hX
  have hX1 : (1 : ℝ) < X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hWpos : (0 : ℝ) < X / h := div_pos hX0 hh0
  have hT0W : seamT0 X ≤ X / h := seamT0_le_div hX hh1 le_rfl hhX
  have h2W : 2 * (X / h) ≤ X := by
    have hkey : 2 * (X / h) = 2 * X / h := by ring
    rw [hkey, div_le_iff₀ hh0]
    nlinarith
  -- the MID BAND: the row at the designed height, where the weight is `1`
  have hrowW := hrows (X / h) le_rfl h2W hTann hceil
  rw [div_self hWpos.ne', one_mul] at hrowW
  have hmid := seam_midrange_of_tall_row hX1 hsupp hT0W hrowW
  simp only [seamT0] at hmid
  -- the `T₀` BAND, in `ParsevalSingle`'s glyph
  have hband : (∫ t in (-((Real.log X) ^ (1 / 15 : ℝ)))..((Real.log X) ^ (1 / 15 : ℝ)),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ B₀ := by
    simpa only [seamT0] using hT0band
  -- the FAR FAMILY
  have hfam := seam_Msup_family hX hh4 hhX ha hsupp hN2 hTann hceil hrows
  -- A2-1
  have hmain := parseval_single_h a (seamS0 N X) K hX hh4 hhX hδ0 hδ1
    (fun m _ => ha m) (seamS0_range hN2) hfam
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hpi0 : (0 : ℝ) ≤ 205 * Real.pi := by positivity
  have h1 := mul_le_mul_of_nonneg_left hmid hpi0
  have h2 := mul_le_mul_of_nonneg_left hband hpi0
  have h3 : 236160 * Real.pi * (Mrow + 168 / h)
      = 236160 * Real.pi * Mrow + 39674880 * Real.pi / h := by
    field_simp
    ring
  linarith

end Salt.MR
