/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Sec9Glue
import Salt.MR.TypicalPrice

/-!
# SieveGlue — the `hsieve` ownership wire (HS-1 … HS-5)

Design block: `docs/exploration/s9-design-0726.md` ⟦AMENDMENT A⟧, **THE HSIEVE
VERDICT**.  `Sec9Glue`'s honest-scope block lists `hsieve` (the fundamental lemma
of the sieve, MR p. 31 (e)) as one of three named externals.  That flag is stale:
`TypicalDensity.typical_density_le` **is** MR's Lemma 2.2, unconditional, with an
absolute constant `C ≈ 1.6·10¹²`, and the `blockOmega` bridge
(`TypicalPrice.coprime_bandProd_of_blockOmega_zero`) is landed too.  This file is
the wire.

## The ladder

* **HS-1** — `sec9_eq28_const`, `eq28_clears_of_M_const`, `sec9_eq28_exit_const`:
  the `Sec9Glue`/`SeamCalibrationK` statements with the literal `(1 + 1/100)`
  promoted to a parameter `C` (`1 ≤ C`).  The conclusion coefficient becomes `2C`
  and the clears-gate becomes `8C/δ ≤ M`.  **Additive** — the landed
  `sec9_eq28`, `sec9_eq28_exit`, `eq28_clears_of_M` are untouched.  The
  literal-`(1+1/100)` road remains exactly the `C = 1 + 1/100` instance.
* **HS-2** — `card_blockfree_le`: `typical_density_le ∘
  coprime_bandProd_of_blockOmega_zero`, extracted as a named count bound on the
  `blockOmega = 0` shell of `Ioc X (2X)`.  (`TypicalPrice.blockfree_sum_le` runs
  the same composition inline, priced into a coefficient sum; the §9 consumer
  needs the count, not the price.)
* **HS-3** — `hreg_of_small_h`, `hbig_of_floor`, `herr_of_mertens`/`herr_of_floor`:
  the three analytic gates of `typical_density_le`, discharged from door-side
  data.  Each gate rides its own statement (law #253).
* **HS-4** — `hsieve_of_engine`: the `j`-sum composition,
  `card_not_memS_le_sum ∘ card_blockfree_le`, producing **verbatim** the shape of
  `Sec9Glue.sec9_eq28_exit`'s `hsieve` binder with `(1 + 1/100)` replaced by the
  HS-2 constant.
* **HS-5** — `memS_calFamily`, `memS_congr`, `card_notMemS_pin`, and the capstone
  `sec9_eq28_exit_calFamily`: the **cross-wire pin**.  Nothing inside
  `sec9_eq28_exit`'s binder ties `MemS`'s free `Pseq`/`Qseq` to the `K`-family
  `calP`/`calQK` that the `hsieve` right-hand side names — the two could be
  unrelated and the statement would still typecheck.  These lemmas are that tie,
  and the capstone takes it at the instantiation `Pseq := calP A G`,
  `Qseq := calQK A G M`, discharging `hsieve` outright.

## The one shared constant

`card_blockfree_le` is an `∃ C`.  Both consumers — the `hsieve` bound (HS-4) and
the `M`-rescale gate `8C/δ ≤ M` (HS-1) — must see the **same** `C`, so the
`∃`-wrapper is opened once, at the capstone, and threaded.  That is why
`hsieve_of_engine` and `sec9_eq28_exit_calFamily` are themselves `∃ C`-shaped
rather than `C`-parametric: the alternative silently admits two constants.

`card_blockfree_le` delivers `1 ≤ C` (not merely `0 < C`) by a `max … 1`, because
HS-1's `sec9_eq28_const` needs `1 ≤ C` and `typical_density_le` only advertises
positivity.

## ⟦V9c LAW⟧

Nothing here is ever allowed to present a closed `calP`/`calQK` to `norm_num` or
`simp`: those are `2^{65536}`-scale numerals.  Every lemma below keeps `A`, `G`,
`M`, `j` as variables and moves only through `log_calP` / `log_calQK` /
`log_calP_div_log_calQK`.

## Honest scope

This file retires `hsieve` on the §9 path.  `Sec9Glue`'s other two named
externals — `Lemma4Comparison` (Granville–Soundararajan) and the two Theorem-3
applications `hthm3f` / `hthm3one` (MR eq (27)'s exceptional-set accounting) —
are untouched and still ride the capstone's binder.

⟦ZENO residuals⟧
1. **HS-6** — the window generality.  `typical_density_le` counts on the dyadic
   window `Ioc X (2X)`; the §9 long sum is over `[X, 2X]` in MR's own indexing.
   `hsieve_of_engine` therefore takes `Nlg ⊆ Ioc X (2X)` and the half-open
   endpoint `n = X` is simply not covered; the dyadic split that removes this
   restriction is the M4-8 wave's.
2. **The door-normalisation `log ω` absorption into `M`** — verified at
   instantiation, not here (M4-8).
3. `hreg_of_small_h`'s `Real.log c ≤ 50` is a convenience floor, not a sharp
   constant: any `c ≤ e^{s/2}` works, and the small-`h` branch has `s ≥ 100`.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — HS-1: the `C`-parametric eq (28) family

`Sec9Glue.sec9_eq28` and `SeamCalibrationK.eq28_clears_of_M` hard-code MR p. 31's
`(1 + 1/100)` (from `[8, Thm 6.17]`).  The engine this file wires in has a much
larger constant — `typical_density_le`'s `C ≈ 1.6·10¹²` — and the K-ladder is
built to absorb exactly that: the whole cost is a **linear `M`-rescale**.  These
are the same three statements with `C` a parameter.
-/

/-- **HS-1(a)** — MR p. 31 (f), eq (28), at a general sieve constant.  With
`Bc ≤ C·Ssum` in place of `Bc ≤ (1 + 1/100)·Ssum`, the assembled bound is
`δ/50 + 2C·Ssum` in place of `δ/50 + (2 + 1/50)·Ssum`.  The `2` is p. 30 (c)'s
own coefficient; `C = 1 + 1/100` recovers `Sec9Glue.sec9_eq28` exactly. -/
theorem sec9_eq28_const {D E Bc Ssum δ R C : ℝ} (_hC : 1 ≤ C)
    (hD : D ≤ δ / 100) (hE : E ≤ δ / 100) (hsieve : Bc ≤ C * Ssum) :
    D + E + 2 * Bc + R ≤ δ / 50 + (2 * C) * Ssum + R := by
  linarith

/-- **HS-1(b)** — the demand side at a general sieve constant
(`SeamCalibrationK.eq28_clears_of_M`, re-derived).  `Σ_{j≤Jb} log P_j/log Q_j ≤ 2/M`
is uniform in `Jb`, so `δ/50 + 2C·Σ_j ≤ δ/50 + 4C/M`, and the gate `M ≥ 8C/δ`
makes `4C/M ≤ δ/2`; `1/50 + 1/2 = 0.52 ≤ 1`.

This is the whole price of the engine's constant: MR's `M ≥ 4/δ` becomes
`M ≥ 8C/δ`, a **linear** rescale of the K-ladder's re-pin parameter.  At
`C = 1 + 1/100` it is `eq28_clears_of_M`'s own `8/δ` up to the slack already
present there. -/
theorem eq28_clears_of_M_const {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M)
    (Jb : ℕ) {δ C : ℝ} (hδ : 0 < δ) (hC : 1 ≤ C) (hMδ : 8 * C / δ ≤ (M : ℝ)) :
    δ / 50 + (2 * C) * ∑ j ∈ Finset.Icc 1 Jb,
        Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ)
      ≤ δ := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hC0 : (0 : ℝ) < C := by linarith
  have hsum := sum_ratioK_le hA hG hM Jb
  have hstep : (2 * C) * ∑ j ∈ Finset.Icc 1 Jb,
      Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ)
        ≤ (2 * C) * (2 / (M : ℝ)) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hMδ' : 8 * C ≤ (M : ℝ) * δ := by
    rw [div_le_iff₀ hδ] at hMδ; linarith
  have hMinv : (2 : ℝ) / (M : ℝ) ≤ δ / (4 * C) := by
    rw [div_le_div_iff₀ hM0 (by positivity)]
    linarith
  have hprod : (2 * C) * (2 / (M : ℝ)) ≤ (2 * C) * (δ / (4 * C)) :=
    mul_le_mul_of_nonneg_left hMinv (by positivity)
  have heq : (2 * C) * (δ / (4 * C)) = δ / 2 := by field_simp; ring
  linarith

/-- **HS-1(c)** — **THE §9 EXIT AT A GENERAL SIEVE CONSTANT**.  Byte-for-byte
`Sec9Glue.sec9_eq28_exit` with the `hsieve` binder's `(1 + 1/100)` replaced by
`C` and the clears-gate `8/δ ≤ M` replaced by `8C/δ ≤ M`.  Everything else — the
four-term bound of p. 30 (c), the two Theorem-3 applications, the `O(1/h)`
normalisation residual — is unchanged and is cited, not re-proved.

This is the statement HS-4's output feeds. -/
theorem sec9_eq28_exit_const (Nsh Nlg : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (J : ℕ)
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) {h X δ C : ℝ} (hh : 0 < h) (hX : 0 < X)
    (hδ : 0 < δ) (hC : 1 ≤ C) {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M)
    (hMδ : 8 * C / δ ≤ (M : ℝ))
    (hthm3f : |(1 / h) * ∑ n ∈ Nsh.filter (fun n => MemS Pseq Qseq J n), f n
        - (1 / X) * ∑ n ∈ Nlg.filter (fun n => MemS Pseq Qseq J n), f n|
      ≤ δ / 100)
    (hthm3one : |(1 / h) * ((Nsh.filter (fun n => MemS Pseq Qseq J n)).card : ℝ)
        - (1 / X) * ((Nlg.filter (fun n => MemS Pseq Qseq J n)).card : ℝ)|
      ≤ δ / 100)
    (hsieve : (1 / X) * ((Nlg.filter (fun n => ¬ MemS Pseq Qseq J n)).card : ℝ)
      ≤ C * ∑ j ∈ Finset.Icc 1 J,
          Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ)) :
    |(1 / h) * ∑ n ∈ Nsh, f n - (1 / X) * ∑ n ∈ Nlg, f n|
      ≤ δ + (((1 / h) * (Nsh.card : ℝ) - 1) + (1 - (1 / X) * (Nlg.card : ℝ))) := by
  have hfour :=
    sec9_four_term Nsh Nlg (fun n => MemS Pseq Qseq J n) f hf hh hX
  have hclear := eq28_clears_of_M_const hA hG hM J hδ hC hMδ
  linarith

/-! ## §2 — HS-2: the named count extraction

`typical_density_le` counts `n ∈ (X, 2X]` coprime to `bandProd P Q`; §9 counts
`n` with `blockOmega P Q n = 0`.  The bridge is
`coprime_bandProd_of_blockOmega_zero`, which needs `n ≠ 0` — supplied by the
window itself (`n ∈ Ioc X (2X)` forces `X < n`).
-/

/-- **HS-2 — `card_blockfree_le`.**  `#{n ∈ (X, 2X] : ω(n; P, Q) = 0} ≤
C·(log P/log Q)·X`, with an absolute `C ≥ 1`, under `typical_density_le`'s own
three analytic gates (MR's regularity `log Q ≤ √log X`, the large-`X` guard
`√log X ≥ 100`, and the explicit error-domination inequality — HS-3 discharges
all three).  This is MR Lemma 2.2 in the shape §9 consumes.

The constant is `typical_density_le`'s, raised to `max C 1` so that HS-1's
`1 ≤ C` binder is met; the raise is free because `(log P/log Q)·X ≥ 0`. -/
theorem card_blockfree_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P Q X : ℕ), 2 ≤ P → P ≤ Q →
        Real.log Q ≤ Real.sqrt (Real.log X) →
        (100 : ℝ) ≤ Real.sqrt (Real.log X) →
        ((Nat.sqrt X : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (X : ℝ) * (Real.log P / Real.log Q) →
        (((Finset.Ioc X (2 * X)).filter (fun n => blockOmega P Q n = 0)).card : ℝ)
          ≤ C * (Real.log P / Real.log Q) * X := by
  obtain ⟨C₀, hC₀, hden⟩ := typical_density_le
  refine ⟨max C₀ 1, le_max_right _ _, ?_⟩
  intro P Q X hP hPQ hreg hbig herr
  have hQ2 : 2 ≤ Q := le_trans hP hPQ
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast hQ2)
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hratio : (0 : ℝ) ≤ Real.log P / Real.log Q := div_nonneg hlogP.le hlogQ.le
  -- ⟦the bridge: `ω(n;P,Q) = 0` ⟹ coprime to the band radical, for `n ≠ 0`⟧
  have hsub : ((Finset.Ioc X (2 * X)).filter (fun n => blockOmega P Q n = 0)).card
      ≤ ((Finset.Ioc X (2 * X)).filter (fun n => (bandProd P Q).Coprime n)).card := by
    refine Finset.card_le_card ?_
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, coprime_bandProd_of_blockOmega_zero (by omega) hn.2⟩
  have hcast :
      (((Finset.Ioc X (2 * X)).filter (fun n => blockOmega P Q n = 0)).card : ℝ)
        ≤ (((Finset.Ioc X (2 * X)).filter
              (fun n => (bandProd P Q).Coprime n)).card : ℝ) := by
    exact_mod_cast hsub
  refine hcast.trans ((hden P Q X hP hPQ hreg hbig herr).trans ?_)
  have hmax : C₀ ≤ max C₀ 1 := le_max_left _ _
  nlinarith [mul_nonneg hratio hXnn]

/-! ## §3 — HS-3: the three analytic gates

`typical_density_le` has three hypotheses beyond `2 ≤ P ≤ Q`.  Each is discharged
here from door-side data, with the door-side data *in the statement* (law #253):
no gate is assumed away, each is traded for a floor on `X`.
-/

/-- `log s ≤ s/4` for `s ≥ 100` (via `log t ≤ t − 1` at `t = √s`).  The slack is
enormous — at `s = 100`, `log s = 4.6` against `25`. -/
private lemma log_le_quarter {s : ℝ} (hs : (100 : ℝ) ≤ s) : Real.log s ≤ s / 4 := by
  have hs0 : (0 : ℝ) < s := by linarith
  have ht : (10 : ℝ) ≤ Real.sqrt s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hts : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have hlog : Real.log s = 2 * Real.log (Real.sqrt s) := by
    have h : Real.log (Real.sqrt s ^ 2) = 2 * Real.log (Real.sqrt s) := by
      rw [Real.log_pow]; push_cast; ring
    rwa [hts] at h
  have hle : Real.log (Real.sqrt s) ≤ Real.sqrt s - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  nlinarith [sq_nonneg (Real.sqrt s - 10)]

/-- **HS-3(a) — `hreg_of_small_h`: MR's regularity gate, FREE on the small-`h`
branch.**

⟦THE BRANCH⟧  `Sec9Glue.door_h_le_hTwo` puts the door road in MR p. 30's
`h ≤ h₂` branch, where the door width satisfies `h ≪ log X` — that is the
**small-`h` branch**, and it is the only branch this lemma covers.  There the
block top `Q_j ≤ h` is at most `c·log X`, so
`log Q_j ≤ log c + 2·log √log X ≤ log c + (√log X)/2 ≤ √log X`
once `√log X ≥ 100` and `log c ≤ 50`.  Nothing analytic is spent: the gate is
free, which is exactly ⟦AMENDMENT A⟧'s claim.

On the long branch (`h ≫ log X`) the gate is NOT free and this lemma says
nothing about it. -/
theorem hreg_of_small_h {Q : ℕ} {hw c X : ℝ} (hQ : 1 ≤ Q) (hc : 1 ≤ c)
    (hclog : Real.log c ≤ 50) (hQh : (Q : ℝ) ≤ hw) (hhX : hw ≤ c * Real.log X)
    (hbig : (100 : ℝ) ≤ Real.sqrt (Real.log X)) :
    Real.log Q ≤ Real.sqrt (Real.log X) := by
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log X) := by linarith
  have hL0 : 0 < Real.log X := Real.sqrt_pos.mp hs0
  have hLs : Real.log X = Real.sqrt (Real.log X) ^ 2 := (Real.sq_sqrt hL0.le).symm
  have hc0 : (0 : ℝ) < c := by linarith
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have h1 : Real.log Q ≤ Real.log (c * Real.log X) :=
    Real.log_le_log hQ0 (le_trans hQh hhX)
  have h2 : Real.log (c * Real.log X) = Real.log c + Real.log (Real.log X) :=
    Real.log_mul hc0.ne' hL0.ne'
  have h3 : Real.log (Real.log X) = 2 * Real.log (Real.sqrt (Real.log X)) := by
    have h := Real.log_pow (Real.sqrt (Real.log X)) 2
    rw [← hLs] at h
    rw [h]; push_cast; ring
  have h4 := log_le_quarter hbig
  linarith

/-- **HS-3(b) — `hbig_of_floor`: the large-`X` guard from an explicit floor.**
`√log X ≥ 100` is exactly `X ≥ e^{10000}`.  Recorded as a lemma so the floor is
visible in the consumer's binder rather than hidden in a `≥ 100` assumption. -/
theorem hbig_of_floor {X : ℕ} (hX : Real.exp 10000 ≤ (X : ℝ)) :
    (100 : ℝ) ≤ Real.sqrt (Real.log X) := by
  have h1 : (10000 : ℝ) ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 10000) hX
    rwa [Real.log_exp] at h
  have h2 : Real.sqrt 10000 ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt h1
  rwa [show (10000 : ℝ) = 100 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)] at h2

/-- **HS-3(c₀) — `herr_of_mertens`: the error-domination gate, with the Euler
product eliminated.**  `TypicalDensity.prod_one_add_three_div_le` is the landed
windowed-Mertens bound
`∏_{P≤p≤Q}(1 + 3/p) ≤ exp(3(log(log(Q+1)/log P) + 19/log P))
   = (log(Q+1)/log P)³·e^{57/log P}`,
so the gate reduces to an inequality with no product in it.  The `57 = 3·19`. -/
theorem herr_of_mertens {P Q X : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hgate : ((Nat.sqrt X : ℝ) + 1)
        * ((Real.log ((Q : ℝ) + 1) / Real.log P) ^ 3 * Real.exp (57 / Real.log P))
      ≤ (X : ℝ) * (Real.log P / Real.log Q)) :
    ((Nat.sqrt X : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (X : ℝ) * (Real.log P / Real.log Q) := by
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hQ2 : 2 ≤ Q := le_trans hP hPQ
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
  have ha0 : 0 < Real.log ((Q : ℝ) + 1) / Real.log P :=
    div_pos (Real.log_pos (by linarith)) hlogP
  refine le_trans ?_ hgate
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (prod_one_add_three_div_le hP hPQ).trans (le_of_eq ?_)
  rw [show (3 : ℝ) * (Real.log (Real.log ((Q : ℝ) + 1) / Real.log P)
        + 19 / Real.log P)
      = 3 * Real.log (Real.log ((Q : ℝ) + 1) / Real.log P) + 57 / Real.log P by
    ring, Real.exp_add]
  congr 1
  rw [show (3 : ℝ) * Real.log (Real.log ((Q : ℝ) + 1) / Real.log P)
      = Real.log (Real.log ((Q : ℝ) + 1) / Real.log P)
        + Real.log (Real.log ((Q : ℝ) + 1) / Real.log P)
        + Real.log (Real.log ((Q : ℝ) + 1) / Real.log P) by ring,
    Real.exp_add, Real.exp_add, Real.exp_log ha0]
  ring

/-- `2 ≤ calP A G j`: the `P`-ladder never degenerates.  (⟦V9c⟧: proved through
`Nat.pow_le_pow_right`, never by evaluating `2 ^ calE`.) -/
lemma two_le_calP {A G : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (j : ℕ) : 2 ≤ calP A G j := by
  have hE : 0 < calE A G j := by
    rw [calE]
    exact Nat.mul_pos (Nat.mul_pos hA (pow_pos hG (j - 1)))
      (pow_pos (Nat.factorial_pos j) 2)
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ calE A G j := Nat.pow_le_pow_right (by norm_num) hE
    _ = calP A G j := rfl

/-- **HS-3(c) — `herr_of_floor`: the error-domination gate at the K-family, from
a floor on `√X`.**

At `P_j = calP A G j`, `Q_j = calQK A G M j` the ratio is exactly `1/K` with
`K = j²M` (`log_calP_div_log_calQK`), and `log(Q_j+1)/log P_j ≤ 2K` (because
`Q_j + 1 ≤ Q_j²`).  So the Mertens factor is `≤ 8K³·e^{57/log P_j}` and the gate
collapses to

`16·(j²M)⁴·e^{57/log calP A G j} ≤ √X`,

which is the scoper's `√X ≥ 2(j²M)⁴e^{57/log P}` shape (our constant is `16`, not
`2`: `8` from `(2K)³`, and `2` from `Nat.sqrt X + 1 ≤ 2√X`).  Note the level is
`Nat.sqrt X + 1`, the Selberg level of `densSieve`, and it is bounded by the real
`√X` — not silently identified with it. -/
theorem herr_of_floor {A G M j X : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M)
    (hj : 1 ≤ j) (hX : 1 ≤ X)
    (hfloor : 16 * ((j : ℝ) ^ 2 * (M : ℝ)) ^ 4
        * Real.exp (57 / Real.log ((calP A G j : ℕ) : ℝ)) ≤ Real.sqrt X) :
    ((Nat.sqrt X : ℝ) + 1)
        * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
      ≤ (X : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
          / Real.log ((calQK A G M j : ℕ) : ℝ)) := by
  have hP2 : 2 ≤ calP A G j := two_le_calP hA hG j
  have hPQ : calP A G j ≤ calQK A G M j := calP_le_calQK hM hj
  refine herr_of_mertens hP2 hPQ ?_
  -- ⟦the numeric gate⟧
  have hQ2 : 2 ≤ calQK A G M j := le_trans hP2 hPQ
  have hlogP : 0 < Real.log ((calP A G j : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast hP2)
  have hQR : (2 : ℝ) ≤ ((calQK A G M j : ℕ) : ℝ) := by exact_mod_cast hQ2
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hK1 : (1 : ℝ) ≤ (j : ℝ) ^ 2 * (M : ℝ) := by nlinarith
  have hK0 : (0 : ℝ) < (j : ℝ) ^ 2 * (M : ℝ) := by linarith
  -- `log Q = K · log P`, straight from the two log identities
  have hQP : Real.log ((calQK A G M j : ℕ) : ℝ)
      = ((j : ℝ) ^ 2 * (M : ℝ)) * Real.log ((calP A G j : ℕ) : ℝ) := by
    rw [log_calQK, log_calP]; ring
  have hratio : Real.log ((calP A G j : ℕ) : ℝ)
      / Real.log ((calQK A G M j : ℕ) : ℝ) = 1 / ((j : ℝ) ^ 2 * (M : ℝ)) :=
    log_calP_div_log_calQK hA hG hM hj
  -- `a := log(Q+1)/log P ≤ 2K`
  have hanonneg : 0 ≤ Real.log (((calQK A G M j : ℕ) : ℝ) + 1)
      / Real.log ((calP A G j : ℕ) : ℝ) :=
    div_nonneg (Real.log_nonneg (by linarith)) hlogP.le
  have hlogQ1 : Real.log (((calQK A G M j : ℕ) : ℝ) + 1)
      ≤ 2 * Real.log ((calQK A G M j : ℕ) : ℝ) := by
    have hsq : ((calQK A G M j : ℕ) : ℝ) + 1 ≤ ((calQK A G M j : ℕ) : ℝ) ^ 2 := by
      nlinarith
    calc Real.log (((calQK A G M j : ℕ) : ℝ) + 1)
        ≤ Real.log (((calQK A G M j : ℕ) : ℝ) ^ 2) :=
          Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log ((calQK A G M j : ℕ) : ℝ) := by
          rw [Real.log_pow]; push_cast; ring
  have ha : Real.log (((calQK A G M j : ℕ) : ℝ) + 1)
      / Real.log ((calP A G j : ℕ) : ℝ) ≤ 2 * ((j : ℝ) ^ 2 * (M : ℝ)) := by
    rw [div_le_iff₀ hlogP]
    rw [hQP] at hlogQ1
    linarith
  -- `Nat.sqrt X + 1 ≤ 2·√X`
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hs1 : (1 : ℝ) ≤ Real.sqrt X := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : (0 : ℝ) < Real.sqrt X := by linarith
  have hsX : Real.sqrt X ^ 2 = (X : ℝ) := Real.sq_sqrt (by linarith)
  have hNs : ((Nat.sqrt X : ℕ) : ℝ) ≤ Real.sqrt X := Real.nat_sqrt_le_real_sqrt
  have hE0 : (0 : ℝ) < Real.exp (57 / Real.log ((calP A G j : ℕ) : ℝ)) :=
    Real.exp_pos _
  rw [hratio, mul_one_div, le_div_iff₀ hK0]
  have hstep : ((Nat.sqrt X : ℝ) + 1)
      * ((Real.log (((calQK A G M j : ℕ) : ℝ) + 1)
            / Real.log ((calP A G j : ℕ) : ℝ)) ^ 3
        * Real.exp (57 / Real.log ((calP A G j : ℕ) : ℝ)))
      ≤ (2 * Real.sqrt X)
        * ((2 * ((j : ℝ) ^ 2 * (M : ℝ))) ^ 3
          * Real.exp (57 / Real.log ((calP A G j : ℕ) : ℝ))) := by
    refine mul_le_mul (by linarith) ?_
      (mul_nonneg (pow_nonneg hanonneg 3) hE0.le) (by positivity)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hanonneg ha 3) hE0.le
  calc ((Nat.sqrt X : ℝ) + 1)
        * ((Real.log (((calQK A G M j : ℕ) : ℝ) + 1)
              / Real.log ((calP A G j : ℕ) : ℝ)) ^ 3
          * Real.exp (57 / Real.log ((calP A G j : ℕ) : ℝ)))
        * ((j : ℝ) ^ 2 * (M : ℝ))
      ≤ (2 * Real.sqrt X)
          * ((2 * ((j : ℝ) ^ 2 * (M : ℝ))) ^ 3
            * Real.exp (57 / Real.log ((calP A G j : ℕ) : ℝ)))
          * ((j : ℝ) ^ 2 * (M : ℝ)) :=
        mul_le_mul_of_nonneg_right hstep hK0.le
    _ = (16 * ((j : ℝ) ^ 2 * (M : ℝ)) ^ 4
          * Real.exp (57 / Real.log ((calP A G j : ℕ) : ℝ))) * Real.sqrt X := by
        ring
    _ ≤ Real.sqrt X * Real.sqrt X := mul_le_mul_of_nonneg_right hfloor hs0.le
    _ = (X : ℝ) := Real.mul_self_sqrt (by linarith)

/-! ## §4 — HS-4: the `j`-sum composition

`card_not_memS_le_sum` is the union bound `#{n ∉ S} ≤ Σ_j #{n : ω(n; P_j, Q_j) = 0}`;
HS-2 prices each summand.  The result is **verbatim** the `hsieve` binder of
`Sec9Glue.sec9_eq28_exit` with `(1 + 1/100)` replaced by the engine's constant.
-/

/-- **HS-4 — `hsieve_of_engine`: `hsieve` DISCHARGED.**

Under the K-family pins (`1 ≤ A, G, M`), the window restriction
`Nlg ⊆ Ioc X (2X)`, and HS-3's three gates read at each block `j ∈ [1, J]`,

`(1/X)·#{n ∈ Nlg : n ∉ S} ≤ C·Σ_{j≤J} log calP_j / log calQK_j`

with `C` the (single, shared) constant of `card_blockfree_le`.  This is
`Sec9Glue.sec9_eq28_exit`'s third named external, retired.

⟦THE PIN⟧  `MemS`'s sequences are instantiated here — `Pseq := calP A G`,
`Qseq := calQK A G M` — so the left-hand `S` and the right-hand ratio speak about
the same blocks.  See §5 for why that is not automatic. -/
theorem hsieve_of_engine :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A G M J X : ℕ) (Nlg : Finset ℕ),
      1 ≤ A → 1 ≤ G → 1 ≤ M →
      Nlg ⊆ Finset.Ioc X (2 * X) → 0 < (X : ℝ) →
      (100 : ℝ) ≤ Real.sqrt (Real.log X) →
      (∀ j ∈ Finset.Icc 1 J,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log X)) →
      (∀ j ∈ Finset.Icc 1 J,
        ((Nat.sqrt X : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (X : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
              / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      (1 / (X : ℝ))
          * ((Nlg.filter (fun n => ¬ MemS (calP A G) (calQK A G M) J n)).card : ℝ)
        ≤ C * ∑ j ∈ Finset.Icc 1 J,
            Real.log ((calP A G j : ℕ) : ℝ)
              / Real.log ((calQK A G M j : ℕ) : ℝ) := by
  obtain ⟨C, hC, hcard⟩ := card_blockfree_le
  refine ⟨C, hC, ?_⟩
  intro A G M J X Nlg hA hG hM hNlg hX hbig hreg herr
  have hXne : (X : ℝ) ≠ 0 := ne_of_gt hX
  -- ⟦STEP 1: the union bound (p. 31 (e), the pure-counting part)⟧
  have h1 := card_not_memS_le_sum Nlg (calP A G) (calQK A G M) J
  -- ⟦STEP 2: each block, by the engine⟧
  have h2 : ∀ j ∈ Finset.Icc 1 J,
      ((Nlg.filter
          (fun n => blockOmega (calP A G j) (calQK A G M j) n = 0)).card : ℝ)
        ≤ C * (Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ)) * X := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hP2 : 2 ≤ calP A G j := two_le_calP hA hG j
    have hPQ : calP A G j ≤ calQK A G M j := calP_le_calQK hM hj1
    have hmono : ((Nlg.filter
        (fun n => blockOmega (calP A G j) (calQK A G M j) n = 0)).card : ℝ)
        ≤ (((Finset.Ioc X (2 * X)).filter
            (fun n => blockOmega (calP A G j) (calQK A G M j) n = 0)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hNlg)
    exact hmono.trans (hcard _ _ _ hP2 hPQ (hreg j hj) hbig (herr j hj))
  -- ⟦STEP 3: sum and normalise⟧
  have h3 : ((Nlg.filter
      (fun n => ¬ MemS (calP A G) (calQK A G M) J n)).card : ℝ)
      ≤ ∑ j ∈ Finset.Icc 1 J,
          C * (Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ)) * X := by
    refine le_trans ?_ (Finset.sum_le_sum h2)
    exact_mod_cast h1
  have h4 : ∑ j ∈ Finset.Icc 1 J,
      C * (Real.log ((calP A G j : ℕ) : ℝ)
        / Real.log ((calQK A G M j : ℕ) : ℝ)) * X
      = C * X * ∑ j ∈ Finset.Icc 1 J,
          Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [h4] at h3
  calc (1 / (X : ℝ))
        * ((Nlg.filter (fun n => ¬ MemS (calP A G) (calQK A G M) J n)).card : ℝ)
      ≤ (1 / (X : ℝ)) * (C * X * ∑ j ∈ Finset.Icc 1 J,
          Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = C * ∑ j ∈ Finset.Icc 1 J,
          Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ) := by
        field_simp

/-! ## §5 — HS-5: the `Pseq`/`Qseq` cross-wire pin

⟦THE TRAP⟧  In `Sec9Glue.sec9_eq28_exit` the set `S` is `MemS Pseq Qseq J` for
**free** `Pseq`, `Qseq`, while the `hsieve` binder's right-hand side names
`calP A G j` and `calQK A G M j`.  Nothing in the statement connects them: one
could supply `Pseq = fun _ => 2` and the theorem would still typecheck, saying
nothing about the K-family.  These lemmas are the tie, and the capstone takes it.
-/

/-- **HS-5(a)** — the pin, unfolded: `S` at the K-family. -/
lemma memS_calFamily (A G M J n : ℕ) :
    MemS (calP A G) (calQK A G M) J n
      ↔ ∀ j ∈ Finset.Icc 1 J, 1 ≤ blockOmega (calP A G j) (calQK A G M j) n :=
  Iff.rfl

/-- **HS-5(b)** — `MemS` reads its sequences only on `[1, J]`, so a pointwise
agreement there is enough to identify two `S`'s.  This is what makes the pin
*checkable*: a consumer holding `Pseq`/`Qseq` from elsewhere discharges the
cross-wire by exhibiting the agreement, not by fiat. -/
lemma memS_congr {Pseq Qseq Pseq' Qseq' : ℕ → ℕ} {J n : ℕ}
    (hP : ∀ j ∈ Finset.Icc 1 J, Pseq j = Pseq' j)
    (hQ : ∀ j ∈ Finset.Icc 1 J, Qseq j = Qseq' j) :
    MemS Pseq Qseq J n ↔ MemS Pseq' Qseq' J n := by
  constructor <;> intro h j hj
  · rw [← hP j hj, ← hQ j hj]; exact h j hj
  · rw [hP j hj, hQ j hj]; exact h j hj

/-- **HS-5(c)** — the pin at the level §9 actually uses it: the `n ∉ S` count. -/
lemma card_notMemS_pin {Pseq Qseq : ℕ → ℕ} {A G M J : ℕ} (Nlg : Finset ℕ)
    (hP : ∀ j ∈ Finset.Icc 1 J, Pseq j = calP A G j)
    (hQ : ∀ j ∈ Finset.Icc 1 J, Qseq j = calQK A G M j) :
    (Nlg.filter (fun n => ¬ MemS Pseq Qseq J n)).card
      = (Nlg.filter (fun n => ¬ MemS (calP A G) (calQK A G M) J n)).card := by
  congr 1
  refine Finset.filter_congr (fun n _ => ?_)
  simp only [not_iff_not]
  exact memS_congr hP hQ

/-- **THE CAPSTONE — the §9 exit at the K-family, with `hsieve` GONE.**

`Sec9Glue.sec9_eq28_exit` carries three named externals; this is the same exit
with the third one discharged by the corpus's own MR Lemma 2.2.  What remains in
the binder is exactly the Theorem-3 pair (`hthm3f`, `hthm3one`) plus HS-3's three
gates, which are floors on `X`, not theorems.

⟦ONE CONSTANT⟧  The `∃ C` is opened once.  The same `C` appears in the
`M`-rescale gate `8C/δ ≤ M` and inside the discharged sieve bound; splitting the
wrapper would let the two drift apart and the accounting would be vacuous.

⟦THE PIN, TAKEN⟧  `Pseq := calP A G`, `Qseq := calQK A G M` throughout, so the
`S` on the left and the ratio sum on the right are the same K-family. -/
theorem sec9_eq28_exit_calFamily :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A G M J X : ℕ) (Nsh Nlg : Finset ℕ) (f : ℕ → ℝ)
      (hw δ : ℝ),
      (∀ n, |f n| ≤ 1) → Nlg ⊆ Finset.Ioc X (2 * X) →
      0 < hw → 0 < (X : ℝ) → 0 < δ →
      1 ≤ A → 1 ≤ G → 1 ≤ M → 8 * C / δ ≤ (M : ℝ) →
      (100 : ℝ) ≤ Real.sqrt (Real.log X) →
      (∀ j ∈ Finset.Icc 1 J,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log X)) →
      (∀ j ∈ Finset.Icc 1 J,
        ((Nat.sqrt X : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (X : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
              / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      |(1 / hw) * ∑ n ∈ Nsh.filter
            (fun n => MemS (calP A G) (calQK A G M) J n), f n
          - (1 / (X : ℝ)) * ∑ n ∈ Nlg.filter
            (fun n => MemS (calP A G) (calQK A G M) J n), f n| ≤ δ / 100 →
      |(1 / hw) * ((Nsh.filter
            (fun n => MemS (calP A G) (calQK A G M) J n)).card : ℝ)
          - (1 / (X : ℝ)) * ((Nlg.filter
            (fun n => MemS (calP A G) (calQK A G M) J n)).card : ℝ)| ≤ δ / 100 →
      |(1 / hw) * ∑ n ∈ Nsh, f n - (1 / (X : ℝ)) * ∑ n ∈ Nlg, f n|
        ≤ δ + (((1 / hw) * (Nsh.card : ℝ) - 1)
            + (1 - (1 / (X : ℝ)) * (Nlg.card : ℝ))) := by
  obtain ⟨C, hC, heng⟩ := hsieve_of_engine
  refine ⟨C, hC, ?_⟩
  intro A G M J X Nsh Nlg f hw δ hf hNlg hh hX hδ hA hG hM hMδ hbig hreg herr
    hthm3f hthm3one
  exact sec9_eq28_exit_const Nsh Nlg (calP A G) (calQK A G M) J f hf hh hX hδ hC
    hA hG hM hMδ hthm3f hthm3one
    (heng A G M J X Nlg hA hG hM hNlg hX hbig hreg herr)

end Salt.MR
