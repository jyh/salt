/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Sec9Glue
import Salt.MR.Lemma14

/-!
# Eq26Bridge — MR eq (26): the `h₂`-average → `X`-average bridge (§9, p. 30)

Source: Matomäki–Radziwiłł, arXiv `1501.04585v4`, **p. 30** (the display (26)),
read against **p. 13** (Lemma 4) and **p. 15** (Lemma 5).  Design freeze:
`docs/exploration/eq26-freeze-0726.md` (ladder `E26-0 … E26-8`, with
⟦AMENDMENT A⟧ folded).  This file is **wave 1** — the elementary core
`E26-0 … E26-5b`, all `A`/`B`.

## The statement MR make (p. 30)

At `Q₁ ≤ h ≤ h₂ = X/(log X)^{1/5}`, "using Lemma 4 together with Lemma 5", for
every `X ≤ x ≤ 2X`,

`(1/h₂)∑_{x ≤ n ≤ x+h₂, n ∈ S} f(n) = (1/X)∑_{X ≤ n ≤ 2X, n ∈ S} f(n)
    + O((log X)^{−1/20+o(1)})`.

MR give no proof.  The reconstruction, and what this file kernel-checks:
Lemma 5 (`Sec9Glue.lemma5`, here in its `ℝ` mirror `lemma5R`) expands the
`n ∈ S` restriction into `2^J` alternating rows indexed by `𝒥 ⊆ {1,…,J}`;
each row is a comparison of the **same** shape at the coefficient sequence
`g_𝒥·f`, so Lemma 4 (`Sec9Glue.Lemma4Comparison`, an external hypothesis —
Halász + Granville–Soundararajan) applies **at `y := h₂`, the exact lower
endpoint of its own `y`-range**; the triangle inequality over the `2^J` rows
pays the factor `2^J`, which is MR's `(log X)^{o(1)}` (p. 28, §8.3).  The
conclusion here is stated with that factor **explicit** — `2^J·C/(log X)^{1/20}`
— which is a strengthening of the printed `O((log X)^{−1/20+o(1)})`, and
`eq26_pinned` reads it off at the K-ladder's pin `Jb = 2` (`2^J = 4`, and the
`o(1)` evaporates).

## The `ℂ`/`ℝ` seam (E26-0)

Lemma 5 is landed over `ℂ` (`gJ : … → ℂ`, the Dirichlet-polynomial lane);
Lemma 4 and eq (26) are statements about **real**, `[−1,1]`-valued
multiplicative `f`.  `gJR` is the `ℝ` mirror of `gJ` and `gJR_ofReal` the one
`split_ifs` that bridges them; every `ℝ`-side fact below is *transported*
through `Complex.ofReal_inj` rather than re-proved (the freeze's "cast route",
⟦AMENDMENT A⟧).

## The stones

* **E26-0** `gJR`, `gJR_ofReal`, `lemma5R` — the `ℝ` mirror and the transported
  Lemma 5.
* **E26-1** `lemma5_budget_diff` — the *difference-shaped* `2^J` budget.
  (⚠ `Sec9Glue.lemma5_budget` is a naming trap: it budgets ONE sum over ONE
  `Finset`, which is not the shape (26) needs.)
* **E26-2** `hTwo_pos`, `hTwo_le_self`, `hTwo_eq_mul_rpow_neg` — the `h₂`
  arithmetic.  The last is the **adapter** to the landed `KernelCarry` binder
  `h₂ ≤ X·(log X)^{−1/5}` (`KernelCarry.lemma14_contour_kernel` :940): the same
  number as `Sec9Glue.hTwo`'s reciprocal-rpow form, but *not* syntactically
  equal to it.
* **E26-3 / E26-3′** `eq26` / `eq26_pinned` — the bridge, uniform in `J`, and
  its `J = 2` specialisation.
* **E26-4** `gJR_one`, `gJR_mul`, `gJR_prime_pow`, `gJR_abs_le_one`,
  `Lemma4Datum`, `Lemma4Datum.gJR_mul` — *the honesty stone*: `g_𝒥·f` really is
  completely multiplicative and `1`-bounded, so the `2^J` instantiations of
  `Lemma4Comparison` in `eq26`'s hypothesis are legitimate instances of Lemma 4
  and not a vacuous over-assumption.
* **E26-5a** `window_defect_bound`, `shortSum_eq26_window` — the window bridge
  between `Lemma14.shortSum`'s **half-open** `(x, x+h]` convention (on the
  clipped carrier `s0`) and eq (26)'s **closed** `[⌈x⌉₊, ⌊x+h⌋₊]` convention.
  **The true defect is ONE lattice point** — the single `n` with `(n : ℝ) = x`,
  which the closed window carries and the half-open one drops; both `s0`-clip
  directions are automatic under `X ≤ x ≤ 2X`, `1 ≤ h ≤ h₂`.  Hence the honest
  bound is `1/h` per average, not `2/h`.
* **E26-5b** `sec9_R_eq_zero_of_card` + the note below — the explicit record
  that `Sec9Glue.sec9_four_term`'s residual `R` is a **different object**.

## ⚠ E26-5b — `sec9_four_term`'s `R` is NOT the window defect

The freeze's first draft equated the E26-5 conversion defect with the residual
`R = ((1/h)#N_sh − 1) + (1 − (1/X)#N_lg)` carried by
`Sec9Glue.sec9_four_term`/`sec9_eq28_exit`.  That is **false**, and the two
must not be netted against each other:

* `R` is the **cardinality-normalisation** defect.  It mentions neither `f` nor
  any window convention: it measures only that `#[x,x+h] ≠ h` and
  `#[X,2X] ≠ X`.  `sec9_R_eq_zero_of_card` below pins this — `R = 0` as soon as
  the two windows carry exactly `h` and `X` lattice points, whatever `f` is.
  It sits **outside** any mean square, in the p. 30 (c) four-term bound.
* The E26-5a defect is a **coefficient-sum** defect: `∑_{B\A} a`, a sum of the
  actual coefficients over the boundary point.  It survives at exact
  cardinalities, and it lives **inside** the Theorem-3 mean square that E26-6
  integrates.

Two different lines of the argument, two different prices.

⟦ZENO residuals of this file⟧ Lemma 4 itself (carried by `Lemma4Comparison`,
Sec9Glue's own ⟦ZENO⟧ #1); E26-6 (the Theorem-3 composition), E26-7 (eq (27)'s
exceptional set) and E26-8 (the `A(h)` instantiation) — wave 2.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §0  E26-0 — the `ℝ` mirror of `g_𝒥` and of Lemma 5 -/

/-- **`g_𝒥`, real-valued** — the `ℝ` mirror of `Sec9Glue.gJ`, defined by the same
`if`-`then`-`else`.  Lemma 5 is landed over `ℂ` because its consumers there are
Dirichlet polynomials; eq (26) and Lemma 4 live over `ℝ`.  `gJR_ofReal` is the
one-line bridge, and every `ℝ`-side fact below is transported across it. -/
def gJR (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) : ℝ :=
  if ∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) n = 0 then 1 else 0

/-- **The `ℂ`/`ℝ` seam** — `↑(g_𝒥^ℝ) = g_𝒥`. -/
@[simp] theorem gJR_ofReal (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) :
    ((gJR 𝒥 Pseq Qseq n : ℝ) : ℂ) = gJ 𝒥 Pseq Qseq n := by
  unfold gJR gJ
  split_ifs <;> simp

/-- **Lemma 5 over `ℝ`** (MR p. 15) — transported from the landed `ℂ` form
`Sec9Glue.lemma5` through `Complex.ofReal_inj`:
`∑_{n∈N, n∈S} a_n = ∑_{𝒥⊆{1,…,J}} (−1)^{#𝒥} ∑_{n∈N} g_𝒥(n) a_n`. -/
theorem lemma5R (N : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (a : ℕ → ℝ) :
    ∑ n ∈ N.filter (fun n => MemS Pseq Qseq J n), a n
      = ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
          (-1 : ℝ) ^ 𝒥.card * ∑ n ∈ N, gJR 𝒥 Pseq Qseq n * a n := by
  apply Complex.ofReal_inj.mp
  push_cast [gJR_ofReal]
  exact lemma5 N Pseq Qseq J (fun n => ((a n : ℝ) : ℂ))

/-! ## §1  E26-1 — the difference-shaped `2^J` budget -/

/-- **E26-1 — the `2^J` budget in the shape eq (26) needs.**  A bound `B`
uniform over the `2^J` inclusion–exclusion rows of the *difference*
`c₁∑_{N₁} g_𝒥·a − c₂∑_{N₂} g_𝒥·a` costs exactly the factor `2^J` on the
corresponding difference of `S`-restricted sums.

⚠ This is **not** `Sec9Glue.lemma5_budget`, which budgets a single sum over a
single `Finset` (the freeze's naming trap): (26) compares two windows with two
different normalisations, and the triangle inequality has to be taken *after*
the difference is formed, row by row. -/
theorem lemma5_budget_diff {N₁ N₂ : Finset ℕ} {Pseq Qseq : ℕ → ℕ} {J : ℕ}
    {a : ℕ → ℝ} {c₁ c₂ B : ℝ}
    (hB : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset,
      |c₁ * ∑ n ∈ N₁, gJR 𝒥 Pseq Qseq n * a n
        - c₂ * ∑ n ∈ N₂, gJR 𝒥 Pseq Qseq n * a n| ≤ B) :
    |c₁ * ∑ n ∈ N₁.filter (fun n => MemS Pseq Qseq J n), a n
      - c₂ * ∑ n ∈ N₂.filter (fun n => MemS Pseq Qseq J n), a n| ≤ 2 ^ J * B := by
  rw [lemma5R N₁ Pseq Qseq J a, lemma5R N₂ Pseq Qseq J a]
  have hrw : c₁ * ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
        (-1 : ℝ) ^ 𝒥.card * ∑ n ∈ N₁, gJR 𝒥 Pseq Qseq n * a n
      - c₂ * ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset,
        (-1 : ℝ) ^ 𝒥.card * ∑ n ∈ N₂, gJR 𝒥 Pseq Qseq n * a n
      = ∑ 𝒥 ∈ (Finset.Icc 1 J).powerset, (-1 : ℝ) ^ 𝒥.card *
          (c₁ * ∑ n ∈ N₁, gJR 𝒥 Pseq Qseq n * a n
            - c₂ * ∑ n ∈ N₂, gJR 𝒥 Pseq Qseq n * a n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun 𝒥 _ => by ring)
  rw [hrw]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset,
      |(-1 : ℝ) ^ 𝒥.card * (c₁ * ∑ n ∈ N₁, gJR 𝒥 Pseq Qseq n * a n
        - c₂ * ∑ n ∈ N₂, gJR 𝒥 Pseq Qseq n * a n)| ≤ B := by
    intro 𝒥 h𝒥
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hB 𝒥 h𝒥
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [Finset.card_powerset, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
    Nat.cast_pow]
  norm_num

/-! ## §2  E26-2 — the `h₂` arithmetic -/

/-- `exp 1 ≤ X` gives `1 ≤ log X` (the standing `X`-hypothesis of the arc). -/
theorem one_le_log_of_exp_le {X : ℝ} (hX : Real.exp 1 ≤ X) : 1 ≤ Real.log X := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  rw [Real.le_log_iff_exp_le hX0]
  exact hX

/-- **E26-2** — `h₂ > 0` on the arc's range `exp 1 ≤ X`. -/
theorem hTwo_pos {X : ℝ} (hX : Real.exp 1 ≤ X) : 0 < hTwo X := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL : (0 : ℝ) < Real.log X := lt_of_lt_of_le zero_lt_one (one_le_log_of_exp_le hX)
  rw [hTwo]
  exact div_pos hX0 (Real.rpow_pos_of_pos hL _)

/-- **E26-2** — `h₂ ≤ X`: this is what makes `y := h₂` a legal instantiation of
Lemma 4's `y`-range `h₂ ≤ y ≤ X` (it saturates the range at *both* ends). -/
theorem hTwo_le_self {X : ℝ} (hX : Real.exp 1 ≤ X) : hTwo X ≤ X := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL1 : (1 : ℝ) ≤ Real.log X := one_le_log_of_exp_le hX
  have hone : (1 : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 5) :=
    Real.one_le_rpow hL1 (by norm_num)
  rw [hTwo]
  exact div_le_self hX0.le hone

/-- **E26-2, the adapter.**  `Sec9Glue.hTwo` is written as a quotient by a
positive rpow; the landed `KernelCarry` binder
(`lemma14_contour_kernel` :940, `lemma14_shortInterval_meansq_kernel` :1156)
is written with a *negative* exponent, `h₂ ≤ X·(log X)^{−1/5}`.  Same number,
different syntax — this is the bridge. -/
theorem hTwo_eq_mul_rpow_neg {X : ℝ} (hL : 0 ≤ Real.log X) :
    hTwo X = X * Real.log X ^ (-(1 / 5 : ℝ)) := by
  rw [hTwo, Real.rpow_neg hL, div_eq_mul_inv]

/-! ## §3  E26-3 / E26-3′ — eq (26) -/

/-- **MR eq (26)** (p. 30) — *the bridge*.  For real `f`, every `X ≤ x ≤ 2X`,
and every `J`, given Lemma 4 at each of the `2^J` coefficient sequences
`g_𝒥·f` (`𝒥 ⊆ {1,…,J}`) with a common constant `C`:

`|(1/h₂)∑_{x ≤ n ≤ x+h₂, n∈S} f − (1/X)∑_{X ≤ n ≤ 2X, n∈S} f| ≤ 2^J·C/(log X)^{1/20}`.

The `2^J` is MR's `(log X)^{o(1)}` (p. 28, §8.3: *"since `2^J ≪ (log X)^{o(1)}`"*),
here left **explicit** — a strengthening of the printed
`O((log X)^{−1/20+o(1)})`, uniform in `J` and in `f`.

Both windows are Lemma 4's own closed windows `[⌈·⌉₊, ⌊·⌋₊]`, so no window
convention is crossed here; all conversion work is isolated in
`shortSum_eq26_window` (E26-5a).  `y := h₂` saturates Lemma 4's `y`-range at
its lower endpoint — the extract's §6.1 finding that MR's `h₂` and Lemma 4's
lower endpoint are one constant, not two. -/
theorem eq26 (Pseq Qseq : ℕ → ℕ) (J : ℕ) (f : ℕ → ℝ) {X C x : ℝ}
    (hX : Real.exp 1 ≤ X) (hx1 : X ≤ x) (hx2 : x ≤ 2 * X)
    (hL4 : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset,
      Lemma4Comparison (fun n => gJR 𝒥 Pseq Qseq n * f n) X C) :
    |(1 / hTwo X) * ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + hTwo X⌋₊).filter
          (fun n => MemS Pseq Qseq J n), f n
        - (1 / X) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
          (fun n => MemS Pseq Qseq J n), f n|
      ≤ 2 ^ J * (C / Real.log X ^ ((1 : ℝ) / 20)) := by
  refine lemma5_budget_diff (fun 𝒥 h𝒥 => ?_)
  exact hL4 𝒥 h𝒥 x (hTwo X) hx1 hx2 le_rfl (hTwo_le_self hX)

/-- **E26-3′ — eq (26) at the K-ladder's pin `Jb = 2`**
(`SeamCalibrationK.calFrameK_satisfiable`).  The `2^J` of MR p. 28 is the
number `4` there, and the `o(1)` in `(log X)^{−1/20+o(1)}` **evaporates**: the
error is the honest `4C/(log X)^{1/20}`.

(The general statement `eq26` is uniform in `J` and hard-codes nothing; this
one carries no `o(1)`.  Both directions of the freeze's `J`-trap respected.) -/
theorem eq26_pinned (Pseq Qseq : ℕ → ℕ) (f : ℕ → ℝ) {X C x : ℝ}
    (hX : Real.exp 1 ≤ X) (hx1 : X ≤ x) (hx2 : x ≤ 2 * X)
    (hL4 : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      Lemma4Comparison (fun n => gJR 𝒥 Pseq Qseq n * f n) X C) :
    |(1 / hTwo X) * ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + hTwo X⌋₊).filter
          (fun n => MemS Pseq Qseq 2 n), f n
        - (1 / X) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
          (fun n => MemS Pseq Qseq 2 n), f n|
      ≤ 4 * (C / Real.log X ^ ((1 : ℝ) / 20)) := by
  refine (eq26 Pseq Qseq 2 f hX hx1 hx2 hL4).trans (le_of_eq ?_)
  norm_num

/-! ## §4  E26-4 — the honesty stone: `g_𝒥·f` really is a Lemma-4 datum -/

/-- `g_𝒥^ℝ(1) = 1`. -/
theorem gJR_one (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) : gJR 𝒥 Pseq Qseq 1 = 1 := by
  have h : ∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) 1 = 0 := by
    intro j _
    simp [blockOmega, BlockPrimeDivs]
  rw [gJR, if_pos h]

/-- **`g_𝒥^ℝ` is completely multiplicative** (MR p. 15) — transported from
`Sec9Glue.gJ_mul`.  No coprimality hypothesis: that is what "completely"
buys, and it is what Lemma 4 needs. -/
theorem gJR_mul (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) :
    gJR 𝒥 Pseq Qseq (m * n) = gJR 𝒥 Pseq Qseq m * gJR 𝒥 Pseq Qseq n := by
  apply Complex.ofReal_inj.mp
  push_cast [gJR_ofReal]
  exact gJ_mul 𝒥 Pseq Qseq hm hn

/-- The block-avoidance condition at a prime power, as an `Iff` — the shared
core of `Sec9Glue.gJ_prime_pow` and of `gJR_prime_pow` below. -/
theorem blockOmega_pow_eq_zero_iff (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    (∀ j ∈ 𝒥, blockOmega (Pseq j) (Qseq j) (p ^ k) = 0)
      ↔ p ∉ 𝒥.biUnion (fun j => jBlock (Pseq j) (Qseq j)) := by
  constructor
  · intro hall hmem
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hmem
    have hzero := hall j hj
    rw [blockOmega_prime_pow hp hk] at hzero
    rw [mem_jBlock] at hpj
    rw [if_pos hpj.1] at hzero
    exact one_ne_zero hzero
  · intro hnot j hj
    rw [blockOmega_prime_pow hp hk]
    have hout : ¬ (Pseq j ≤ p ∧ p ≤ Qseq j) := fun hc =>
      hnot (Finset.mem_biUnion.mpr ⟨j, hj, mem_jBlock.mpr ⟨hc, hp⟩⟩)
    rw [if_neg hout]

/-- **The MR defining spec of `g_𝒥`, real-valued** (p. 15): `g_𝒥(p^k) = 1` if
`p ∉ ⋃_{j∈𝒥}[P_j,Q_j]` and `0` otherwise, for *every* exponent `k ≥ 1`. -/
theorem gJR_prime_pow (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) :
    gJR 𝒥 Pseq Qseq (p ^ k)
      = if p ∉ 𝒥.biUnion (fun j => jBlock (Pseq j) (Qseq j)) then 1 else 0 := by
  unfold gJR
  exact if_congr (blockOmega_pow_eq_zero_iff 𝒥 Pseq Qseq hp hk) rfl rfl

/-- `g_𝒥^ℝ` takes only the values `0` and `1`, hence is `1`-bounded. -/
theorem gJR_abs_le_one (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) :
    |gJR 𝒥 Pseq Qseq n| ≤ 1 := by
  unfold gJR
  split_ifs <;> norm_num

/-- **MR Lemma 4's standing hypothesis on its coefficient sequence** (p. 13):
`f : ℕ → [−1,1]` completely multiplicative.  Named so that E26-4 can say
exactly what it demonstrates. -/
structure Lemma4Datum (f : ℕ → ℝ) : Prop where
  /-- `f(1) = 1`. -/
  map_one : f 1 = 1
  /-- Complete multiplicativity: no coprimality hypothesis. -/
  map_mul : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → f (m * n) = f m * f n
  /-- `f` is `[−1,1]`-valued. -/
  abs_le_one : ∀ n : ℕ, |f n| ≤ 1

/-- **E26-4 — the honesty stone.**  If `f` is a Lemma-4 datum then so is
`g_𝒥·f`, for every `𝒥`.  This is what makes `eq26`'s hypothesis
`∀ 𝒥 ∈ powerset, Lemma4Comparison (g_𝒥·f) X C` a family of *genuine* Lemma-4
instances rather than an over-assumption: the `2^J` rows of the
inclusion–exclusion are exactly `2^J` legitimate applications of MR's Lemma 4,
which is the "side-check" the freeze demands be demonstrable. -/
theorem Lemma4Datum.gJR_mul {f : ℕ → ℝ} (hf : Lemma4Datum f) (𝒥 : Finset ℕ)
    (Pseq Qseq : ℕ → ℕ) : Lemma4Datum (fun n => gJR 𝒥 Pseq Qseq n * f n) where
  map_one := by rw [gJR_one, hf.map_one, mul_one]
  map_mul := by
    intro m n hm hn
    rw [_root_.Salt.MR.gJR_mul 𝒥 Pseq Qseq hm hn, hf.map_mul m n hm hn]
    ring
  abs_le_one := by
    intro n
    rw [abs_mul]
    calc |gJR 𝒥 Pseq Qseq n| * |f n| ≤ 1 * 1 :=
          mul_le_mul (gJR_abs_le_one 𝒥 Pseq Qseq n) (hf.abs_le_one n) (abs_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1

/-! ## §5  E26-5a/5b — the window bridge, and what `sec9_four_term`'s `R` is not -/

/-- **The generic window-defect bound.**  If `A ⊆ B` differ by at most one
element and the coefficients are `1`-bounded on the difference, then the two
`c`-normalised sums differ by at most `c`.  (E26-5a's engine; stated separately
because the same shape recurs at every window-convention crossing.) -/
theorem window_defect_bound {A B : Finset ℕ} {a : ℕ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hAB : A ⊆ B) (hcard : (B \ A).card ≤ 1) (hb : ∀ n ∈ B \ A, ‖a n‖ ≤ 1) :
    ‖(c : ℂ) * ∑ m ∈ A, a m - (c : ℂ) * ∑ n ∈ B, a n‖ ≤ c := by
  have hdiff : ∑ m ∈ A, a m - ∑ n ∈ B, a n = -(∑ n ∈ B \ A, a n) := by
    rw [Finset.sum_sdiff_eq_sub hAB]; ring
  have hb1 : ‖∑ n ∈ B \ A, a n‖ ≤ 1 := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
    rw [nsmul_eq_mul, mul_one]
    exact_mod_cast hcard
  rw [← mul_sub, hdiff, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg hc]
  calc c * ‖∑ n ∈ B \ A, a n‖ ≤ c * 1 := mul_le_mul_of_nonneg_left hb1 hc
    _ = c := mul_one c

/-- **E26-5a — the window bridge.**  `Lemma14.shortSum` sums the **half-open**
window `(x, x+h]` over the clipped carrier
`s0 = [⌈X⌉₊, ⌊4X⌋₊] ∩ S`; eq (26)'s sums run over the **closed** window
`[⌈x⌉₊, ⌊x+h⌋₊] ∩ S`.  Under `X ≤ x ≤ 2X` and `1 ≤ h ≤ h₂`:

* both `s0`-clip directions are **automatic** (`x ≤ n` forces `⌈X⌉₊ ≤ n`, and
  `n ≤ x+h ≤ 3X` forces `n ≤ ⌊4X⌋₊`) — the containment obligation the freeze
  flags is discharged, not assumed;
* the **only** defect is the single lattice point `n` with `(n : ℝ) = x`, which
  the closed window carries and the half-open one drops.

Hence the honest bound is `1/h` per average — one point, not two.  (`x` is a
real; the defect is present exactly when `x` happens to be a natural number in
`S`, and the bound is uniform over that dichotomy.)

The coefficient hypothesis is stated in the landed `KernelCarry` shape
`∀ m ∈ s0, ‖a m‖ ≤ 1` (`lemma14_contour_kernel` :941) rather than as a range
condition: the boundary point is *provably* in `s0`, so no stronger hypothesis
is needed and the wave-2 consumer can pass its own `ha` through unchanged. -/
theorem shortSum_eq26_window (a : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) {X x h : ℝ}
    (hX : Real.exp 1 ≤ X) (hx1 : X ≤ x) (hx2 : x ≤ 2 * X) (hh1 : 1 ≤ h)
    (hh2 : h ≤ hTwo X)
    (ha : ∀ m ∈ (Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n),
      ‖a m‖ ≤ 1) :
    ‖((1 / h : ℝ) : ℂ) * shortSum a
          ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x h
        - ((1 / h : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊).filter
            (fun n => MemS Pseq Qseq J n), a n‖
      ≤ 1 / h := by
  -- the arithmetic environment
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hh0 : (0 : ℝ) < h := lt_of_lt_of_le zero_lt_one hh1
  have hhX : h ≤ X := hh2.trans (hTwo_le_self hX)
  have hx0 : (0 : ℝ) ≤ x := le_trans hX0.le hx1
  have hxh0 : (0 : ℝ) ≤ x + h := by linarith
  have hxh4 : x + h ≤ 4 * X := by linarith
  -- **the boundary analysis** — every point of `B ∖ A` lies in `s0` AND equals `x`
  have hkey : ∀ r : ℕ, r ∈ ((Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊).filter
      (fun n => MemS Pseq Qseq J n)) \
      (((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)).filter
        (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + h)) →
      r ∈ (Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)
        ∧ (r : ℝ) = x := by
    intro r hr
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨⟨hlo, hhi⟩, hrS⟩, hnot⟩ := hr
    have hxr : x ≤ (r : ℝ) := Nat.ceil_le.mp hlo
    have hrx : (r : ℝ) ≤ x + h := (Nat.le_floor_iff hxh0).mp hhi
    -- both `s0`-clip directions are automatic
    have hin : r ∈ (Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter
        (fun n => MemS Pseq Qseq J n) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hrS⟩
      · exact Nat.ceil_le.mpr (le_trans hx1 hxr)
      · exact Nat.le_floor (le_trans hrx hxh4)
    refine ⟨hin, ?_⟩
    have hnlt : ¬ x < (r : ℝ) := by
      intro hlt
      exact hnot (Finset.mem_filter.mpr ⟨hin, hlt, hrx⟩)
    linarith [not_lt.mp hnlt]
  simp only [shortSum]
  refine window_defect_bound (by positivity) ?_ ?_ ?_
  -- (i) the half-open window is contained in the closed one
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨_, hmS⟩, hlt, hle⟩ := hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hmS⟩
    · exact Nat.ceil_le.mpr hlt.le
    · exact Nat.le_floor hle
  -- (ii) the difference is at most ONE lattice point: the `n` with `(n : ℝ) = x`
  · refine Finset.card_le_one.mpr (fun p hp q hq => ?_)
    have hpq := ((hkey p hp).2).trans ((hkey q hq).2).symm
    exact_mod_cast hpq
  -- (iii) the coefficients are `1`-bounded there — the boundary point is in `s0`
  · exact fun n hn => ha n (hkey n hn).1

/-- **E26-5b** — `Sec9Glue.sec9_four_term`'s residual
`R = ((1/h)#N_sh − 1) + (1 − (1/X)#N_lg)` is the pure **cardinality-
normalisation** defect: it mentions neither the coefficient sequence nor any
window convention, and it vanishes identically as soon as the two windows
carry exactly `h` and `X` lattice points.

The E26-5a defect `∑_{B∖A} a` does **not** vanish under that hypothesis — it is
a sum of coefficients over the boundary lattice point.  The two are different
objects at different places in the argument (`R` outside the Theorem-3 mean
square, the E26-5a defect inside it), and must not be netted against each
other.  This lemma is the record of that. -/
theorem sec9_R_eq_zero_of_card {Nsh Nlg : Finset ℕ} {h X : ℝ} (hh : h ≠ 0)
    (hX : X ≠ 0) (hs : (Nsh.card : ℝ) = h) (hl : (Nlg.card : ℝ) = X) :
    ((1 / h) * (Nsh.card : ℝ) - 1) + (1 - (1 / X) * (Nlg.card : ℝ)) = 0 := by
  rw [hs, hl, one_div_mul_cancel hh, one_div_mul_cancel hX]
  ring

end Salt.MR
