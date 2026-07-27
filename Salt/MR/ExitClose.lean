/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MinorArcExit

/-!
# S7 — the exponent close: `ExitClose 12`, and the tight arc unconditionally

`Salt/MR/MinorArcExit.lean` reduces the whole minor-arc obligation to ONE closed-form
numeric statement, `ExitClose B₅`: the assembled bound `exitBd ε H q` eventually undercuts
the `Ξ_H` threshold `ε²/log H`, uniformly over the admissible Dirichlet denominators
`q ∈ ((log H)^{B₅}, H/(log H)^{B₅} + 1]`.  This file proves it at `B₅ = 12` and fires the
two conditional exports, so `MinorArcBoundTight 12` and `BigXiArcTight 12` become
unconditional theorems.

## The shape of the estimate

`exitBd` is a finite sum of terms of the form `C·(log-powers of H)·(powers of ε⁻¹)` over
`H`-powers.  Writing `L = log H`, `N = ⌊ε²H⌋`, `M = ⌊ε²H/2⌋`, `W = ⌊⌊√M⌋^{1/2}⌋`, the two
governing shapes are

* the **power saving** `L³·N/√W`, from the Type II head `√(7·hi·N)` and the
  `√(12N²(1+log q)/W)` block — `W ≍ (ε²H)^{1/4}`, so this is `≍ L³·N^{7/8}`;
* the **log saving** `E·N/L³` (with `E = 1 + ε⁻²`), from every term carrying a factor
  `1/q` or `q`, since the admissible range pins `L^{12} < q ≤ H/L^{12} + 1`.

Collected (`exit_collect`) and divided by `M·log M ≥ N·L/12` this reads

```
exitBd ε H q ≤ 12000·L²/√W + 60000·E/L⁴,
```

and the close is the two-arm threshold `√W ≥ 50000·L³·E` (a power-versus-log gate, via
`W⁴ ≥ M/16 ≥ ε²H/64` and `H = e^L ≥ (L/25)^{25}`) together with `L³ ≥ 240000·E²`.

## Margin hygiene

Every constant here is an explicit numeral and every `H₀` arm is an explicit shape:
`H₀(ε) = max` of four ceilings, the last of which is `⌈exp(25^25·10^40·(1+ε⁻²)^9)⌉₊`.
Nothing downstream reads `H₀` — the target's own `∃ H₀` absorbs it — so the arms are taken
generously: the crude collection above throws away several powers of `log`, while the true
crossover of `exitBd` against `ε²/log H` sits near `H ≈ 10^{100}` with a margin that widens.
(The minor arc is in any case empty below `H ≈ e^{115}`; see `MinorArcExit`'s header.)
-/

namespace Salt.MR

/-! ## §0 — three elementary tools -/

/-- `√x ≤ y` from a square domination — the workhorse of the four block estimates. -/
theorem sqrt_le_of_sq_le {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : Real.sqrt x ≤ y := by
  calc Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = y := Real.sqrt_sq hy

/-- Monotonicity of a triple product of nonnegatives (`mul_le_mul` twice). -/
theorem mul_three_le {a b c A B C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C) : a * b * c ≤ A * B * C := by
  have hA0 : 0 ≤ A := le_trans ha hA
  have hB0 : 0 ≤ B := le_trans hb hB
  exact mul_le_mul (mul_le_mul hA hB hb hA0) hC hc (mul_nonneg hA0 hB0)

/-- **The polynomial-versus-exponential threshold.**  `C·L^24 ≤ e^L` as soon as
`L ≥ 25^25·C`.  Proof: `e^L = (e^{L/25})^{25} ≥ (L/25)^{25} = L^{25}/25^{25}`. -/
theorem pow24_le_exp {C L : ℝ} (hC : 0 < C) (hL : 25 ^ 25 * C ≤ L) :
    C * L ^ 24 ≤ Real.exp L := by
  have h25 : (0 : ℝ) < 25 ^ 25 := by norm_num
  have hL0 : (0 : ℝ) ≤ L := le_trans (mul_nonneg h25.le hC.le) hL
  have hstep : L / 25 ≤ Real.exp (L / 25) := by linarith only [Real.add_one_le_exp (L / 25)]
  have hexp : (L / 25) ^ (25 : ℕ) ≤ Real.exp L := by
    have h1 : (L / 25) ^ (25 : ℕ) ≤ Real.exp (L / 25) ^ (25 : ℕ) :=
      pow_le_pow_left₀ (by linarith only [hL0]) hstep 25
    have h2 : Real.exp L = Real.exp (L / 25) ^ (25 : ℕ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h2]; exact h1
  have hkey : C * L ^ 24 ≤ (L / 25) ^ (25 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_right hL (pow_nonneg hL0 24)
    rw [div_pow, le_div_iff₀ h25]
    calc C * L ^ 24 * 25 ^ 25 = 25 ^ 25 * C * L ^ 24 := by ring
      _ ≤ L * L ^ 24 := hmul
      _ = L ^ 25 := by ring
  linarith only [hkey, hexp]

/-! ## §1 — the collection lemma

The whole of `exitBd`, over plain reals with every logarithm, root and parameter
*generalised to an atom*.  (Stating it this way is what makes the arithmetic
`linarith`-shaped: the concrete form is cast-heavy and defeats the linear pass.)

The atoms are, at the call site,
`n = N`, `m = M`, `w = W`, `hi = W·2^K`, `Q = q`, `L = log H`, `ln = log N`,
`lm = log M`, `lw = log W`, `l2w = log 2W`, `lww = log W²`, `l2ww = log 2W²`,
`lq = log q`, `kk = K`, `E = 1 + ε⁻²`. -/

theorem exit_collect {n m w hi Q L ln lm lw l2w lww l2ww lq kk E : ℝ}
    (hE : 1 ≤ E) (hL : 8 ≤ L)
    (hm : 2 ≤ m) (hw : 1 ≤ w) (hnm : n ≤ 3 * m) (hmn : m ≤ n)
    (hw4 : w ^ 4 ≤ n) (hw2n : w * w ≤ n)
    (hln0 : 0 ≤ ln) (hln : ln ≤ 2 * L) (hlm : L / 4 ≤ lm)
    (hlw0 : 0 ≤ lw) (hlw : lw ≤ 4 * L)
    (hl2w0 : 0 ≤ l2w) (hl2w : l2w ≤ 4 * L)
    (hlww0 : 0 ≤ lww) (hlww : lww ≤ 4 * L)
    (hl2ww0 : 0 ≤ l2ww) (hl2ww : l2ww ≤ 4 * L)
    (hlq0 : 0 ≤ lq) (hlq : lq ≤ L)
    (hQ0 : 0 < Q) (hQ1 : L ^ 12 ≤ Q) (hQ3 : Q * L ^ 12 ≤ 4 * E * n)
    (hkk0 : 0 ≤ kk) (hkk : kk ≤ 6 * L)
    (hhi : hi * w ≤ 2 * n + 2 * (w * w)) :
    (2 * (w * lw
        + (2 * ln * (30 * (n / Q) * (1 + l2w) + 12 * (w + Q) * (1 + lq))
          + lww * (30 * (n / Q) * (1 + l2ww) + 12 * (w * w + Q) * (1 + lq)))
        + kk * (Real.sqrt 2 * ln * (Real.sqrt (7 * hi * n) + Real.sqrt (6 * n ^ 2 / Q)
            + Real.sqrt (12 * n ^ 2 * (1 + lq) / w) + Real.sqrt (12 * n * Q * (1 + lq)))))
      + 4 * Real.sqrt n * ln) / (m * lm)
      ≤ 12000 * L ^ 2 / Real.sqrt w + 60000 * E / L ^ 4 := by
  -- ### scale facts
  have hL1 : (1 : ℝ) ≤ L := by linarith only [hL]
  have hL0 : (0 : ℝ) < L := by linarith only [hL]
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hn2 : (2 : ℝ) ≤ n := le_trans hm hmn
  have hn0 : (0 : ℝ) < n := by linarith only [hn2]
  have hnne : n ≠ 0 := ne_of_gt hn0
  have hw0 : (0 : ℝ) < w := by linarith only [hw]
  have hwne : w ≠ 0 := ne_of_gt hw0
  have hE0 : (0 : ℝ) ≤ E := by linarith only [hE]
  have hwsq : w ≤ w * w := by nlinarith only [hw, hw0]
  have hwn : w ≤ n := le_trans hwsq hw2n
  -- the `L`-power ladder
  have hL23 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL13 : L ≤ L ^ 3 := by
    have h := pow_le_pow_right₀ hL1 (show 1 ≤ 3 by norm_num); simpa using h
  have hL34 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL310 : L ^ 3 ≤ L ^ 10 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL3pos : (0 : ℝ) < L ^ 3 := pow_pos hL0 3
  have hL10pos : (0 : ℝ) < L ^ 10 := pow_pos hL0 10
  have hL12pos : (0 : ℝ) < L ^ 12 := pow_pos hL0 12
  -- ### the root of `w`
  have hs0 : (0 : ℝ) < Real.sqrt w := Real.sqrt_pos.mpr hw0
  have hsne : Real.sqrt w ≠ 0 := ne_of_gt hs0
  have hs2 : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw0.le
  have hs1 : (1 : ℝ) ≤ Real.sqrt w := by nlinarith only [hs2, hs0, hw]
  have hsw : Real.sqrt w ≤ w := by nlinarith only [hs2, hs1]
  have hX0 : (0 : ℝ) ≤ n / Real.sqrt w := div_nonneg hn0.le hs0.le
  have hY0 : (0 : ℝ) ≤ n / L ^ 3 := div_nonneg hn0.le hL3pos.le
  have hPX0 : (0 : ℝ) ≤ L ^ 3 * (n / Real.sqrt w) := mul_nonneg hL3pos.le hX0
  have hEY0 : (0 : ℝ) ≤ E * (n / L ^ 3) := mul_nonneg hE0 hY0
  -- ### the `X`-domination facts
  have hwX : w ≤ n / Real.sqrt w := by
    rw [le_div_iff₀ hs0]
    calc w * Real.sqrt w ≤ w * w := mul_le_mul_of_nonneg_left hsw hw0.le
      _ ≤ n := hw2n
  have hw2X : w * w ≤ n / Real.sqrt w := by
    rw [le_div_iff₀ hs0]
    calc w * w * Real.sqrt w ≤ w * w * w :=
          mul_le_mul_of_nonneg_left hsw (mul_nonneg hw0.le hw0.le)
      _ = w ^ 3 := by ring
      _ ≤ w ^ 4 := pow_le_pow_right₀ hw (by norm_num)
      _ ≤ n := hw4
  have hsqrtnX : Real.sqrt n ≤ n / Real.sqrt w := by
    rw [le_div_iff₀ hs0]
    calc Real.sqrt n * Real.sqrt w ≤ Real.sqrt n * Real.sqrt n :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hwn) (Real.sqrt_nonneg n)
      _ = n := Real.mul_self_sqrt hn0.le
  -- ### the `q`-range facts
  have hnQ : n / Q ≤ n / L ^ 12 := div_le_div_of_nonneg_left hn0.le hL12pos hQ1
  have hnQ0 : (0 : ℝ) ≤ n / Q := div_nonneg hn0.le hQ0.le
  have hQub : Q ≤ 4 * E * n / L ^ 12 := by rw [le_div_iff₀ hL12pos]; exact hQ3
  have hQ0' : (0 : ℝ) ≤ Q := hQ0.le
  -- ### the field identities used to move `L`-powers across a division
  have hidA : L ^ 2 * (n / L ^ 12) = n / L ^ 10 := by field_simp
  have hidB : L ^ 2 * (n / L ^ 6) = n / L ^ 4 := by field_simp
  have hidC : L ^ 2 * (n / L ^ 5) = n / L ^ 3 := by field_simp
  have hnL10 : n / L ^ 10 ≤ n / L ^ 3 := div_le_div_of_nonneg_left hn0.le hL3pos hL310
  have hnL4 : n / L ^ 4 ≤ n / L ^ 3 := div_le_div_of_nonneg_left hn0.le hL3pos hL34
  -- ### the four block roots
  have hA : Real.sqrt (7 * hi * n) ≤ 8 * (n / Real.sqrt w) := by
    refine sqrt_le_of_sq_le (by linarith only [hX0]) ?_
    have hsq : (8 * (n / Real.sqrt w)) ^ 2 = 64 * n ^ 2 / w := by
      rw [mul_pow, div_pow, hs2]; ring
    rw [hsq, le_div_iff₀ hw0]
    linarith only [mul_le_mul_of_nonneg_left hhi (by linarith only [hn0] : (0 : ℝ) ≤ 7 * n),
      mul_le_mul_of_nonneg_left hw2n (by linarith only [hn0] : (0 : ℝ) ≤ 14 * n), sq_nonneg n]
  have hB : Real.sqrt (6 * n ^ 2 / Q) ≤ 3 * (n / L ^ 6) := by
    refine sqrt_le_of_sq_le
      (mul_nonneg (by norm_num) (div_nonneg hn0.le (pow_nonneg hL0.le 6))) ?_
    have hsq : (3 * (n / L ^ 6)) ^ 2 = 9 * n ^ 2 / L ^ 12 := by
      rw [mul_pow, div_pow]; ring
    rw [hsq, div_le_div_iff₀ hQ0 hL12pos]
    linarith only [mul_le_mul_of_nonneg_left hQ1 (by positivity : (0 : ℝ) ≤ 9 * n ^ 2),
      mul_nonneg (sq_nonneg n) hL12pos.le]
  have hC : Real.sqrt (12 * n ^ 2 * (1 + lq) / w) ≤ 5 * L * (n / Real.sqrt w) := by
    refine sqrt_le_of_sq_le (mul_nonneg (mul_nonneg (by norm_num) hL0.le) hX0) ?_
    have hsq : (5 * L * (n / Real.sqrt w)) ^ 2 = 25 * L ^ 2 * n ^ 2 / w := by
      rw [mul_pow, div_pow, hs2]; ring
    rw [hsq, div_le_div_iff₀ hw0 hw0]
    have h1 : 12 * (1 + lq) ≤ 25 * L ^ 2 := by nlinarith only [hlq, hL1]
    nlinarith only [mul_nonneg (sq_nonneg n) hw0.le, h1]
  have hD : Real.sqrt (12 * n * Q * (1 + lq)) ≤ 10 * (E * (n / L ^ 5)) := by
    refine sqrt_le_of_sq_le
      (mul_nonneg (by norm_num)
        (mul_nonneg hE0 (div_nonneg hn0.le (pow_nonneg hL0.le 5)))) ?_
    have hsq : (10 * (E * (n / L ^ 5))) ^ 2 = 100 * E ^ 2 * n ^ 2 / L ^ 10 := by
      rw [mul_pow, mul_pow, div_pow]; ring
    rw [hsq, le_div_iff₀ hL10pos]
    refine le_of_mul_le_mul_right ?_ (pow_pos hL0 2)
    have hEL1 : (1 : ℝ) ≤ E * L := by nlinarith only [hE, hL1]
    have hEL : 96 * E * L ≤ 100 * E ^ 2 * L ^ 2 := by nlinarith only [hEL1]
    calc 12 * n * Q * (1 + lq) * L ^ 10 * L ^ 2 = (12 * n * (1 + lq)) * (Q * L ^ 12) := by ring
      _ ≤ (12 * n * (1 + lq)) * (4 * E * n) :=
          mul_le_mul_of_nonneg_left hQ3 (by nlinarith only [hn0, hlq0])
      _ = (48 * E * n ^ 2) * (1 + lq) := by ring
      _ ≤ (48 * E * n ^ 2) * (2 * L) :=
          mul_le_mul_of_nonneg_left (by linarith only [hlq, hL1])
            (by nlinarith only [hE0, sq_nonneg n])
      _ = (96 * E * L) * n ^ 2 := by ring
      _ ≤ (100 * E ^ 2 * L ^ 2) * n ^ 2 := mul_le_mul_of_nonneg_right hEL (sq_nonneg n)
      _ = 100 * E ^ 2 * n ^ 2 * L ^ 2 := by ring
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  -- ### the seven pieces
  have hq1 : 2 * (w * lw) ≤ 8 * (L ^ 3 * (n / Real.sqrt w)) := by
    have h1 : w * lw ≤ (n / Real.sqrt w) * (4 * L) := mul_le_mul hwX hlw hlw0 hX0
    nlinarith only [h1, hX0, hL13]
  have hq2 : 4 * ln * (30 * (n / Q) * (1 + l2w)) ≤ 1200 * (E * (n / L ^ 3)) := by
    have hmain : 4 * ln * (30 * (n / Q) * (1 + l2w))
        ≤ (120 * (2 * L)) * (n / L ^ 12) * (5 * L) := by
      calc 4 * ln * (30 * (n / Q) * (1 + l2w)) = (120 * ln) * (n / Q) * (1 + l2w) := by ring
        _ ≤ (120 * (2 * L)) * (n / L ^ 12) * (5 * L) :=
            mul_three_le (by linarith only [hln0]) hnQ0 (by linarith only [hl2w0])
              (by linarith only [hln]) hnQ (by linarith only [hl2w, hL1])
    have hrw : (120 * (2 * L)) * (n / L ^ 12) * (5 * L) = 1200 * (L ^ 2 * (n / L ^ 12)) := by
      ring
    rw [hrw, hidA] at hmain
    have h2 : n / L ^ 10 ≤ E * (n / L ^ 3) := by
      nlinarith only [hnL10, hY0, hE]
    linarith only [hmain, h2]
  have halg : (8 * L) * (12 * (n / Real.sqrt w + 4 * E * n / L ^ 12)) * (1 + L)
      ≤ 192 * (L ^ 3 * (n / Real.sqrt w)) + 768 * (E * (n / L ^ 3)) := by
    have hEn12 : (0 : ℝ) ≤ E * (n / L ^ 12) := mul_nonneg hE0 (div_nonneg hn0.le hL12pos.le)
    have hsplit : (8 * L) * (12 * (n / Real.sqrt w + 4 * E * n / L ^ 12)) * (1 + L)
        = (96 * L * (1 + L)) * (n / Real.sqrt w)
          + (384 * (L * (1 + L))) * (E * (n / L ^ 12)) := by
      field_simp
      ring
    rw [hsplit]
    have h1 : (96 * L * (1 + L)) * (n / Real.sqrt w) ≤ 192 * (L ^ 3 * (n / Real.sqrt w)) := by
      have hz : 96 * L * (1 + L) ≤ 192 * L ^ 3 := by nlinarith only [hL13, hL23]
      nlinarith only [hz, hX0]
    have h2 : (384 * (L * (1 + L))) * (E * (n / L ^ 12)) ≤ 768 * (E * (n / L ^ 3)) := by
      have hz : L * (1 + L) ≤ 2 * L ^ 2 := by nlinarith only [hL1]
      have hstep1 : (384 * (L * (1 + L))) * (E * (n / L ^ 12))
          ≤ (384 * (2 * L ^ 2)) * (E * (n / L ^ 12)) := by
        nlinarith only [hz, hEn12]
      have hstep2 : (384 * (2 * L ^ 2)) * (E * (n / L ^ 12))
          = 768 * (E * (L ^ 2 * (n / L ^ 12))) := by ring
      have hstep3 : 768 * (E * (n / L ^ 10)) ≤ 768 * (E * (n / L ^ 3)) := by
        nlinarith only [hnL10, hE0]
      rw [hstep2, hidA] at hstep1
      linarith only [hstep1, hstep3]
    linarith only [h1, h2]
  have hq3 : 4 * ln * (12 * (w + Q) * (1 + lq))
      ≤ 192 * (L ^ 3 * (n / Real.sqrt w)) + 768 * (E * (n / L ^ 3)) := by
    have hmain : 4 * ln * (12 * (w + Q) * (1 + lq))
        ≤ (8 * L) * (12 * (n / Real.sqrt w + 4 * E * n / L ^ 12)) * (1 + L) := by
      calc 4 * ln * (12 * (w + Q) * (1 + lq))
          = (4 * ln) * (12 * (w + Q)) * (1 + lq) := by ring
        _ ≤ (8 * L) * (12 * (n / Real.sqrt w + 4 * E * n / L ^ 12)) * (1 + L) :=
            mul_three_le (by linarith only [hln0])
              (by nlinarith only [hX0, hQ0', hw0])
              (by linarith only [hlq0])
              (by linarith only [hln])
              (by linarith only [hwX, hQub])
              (by linarith only [hlq])
    linarith only [hmain, halg]
  have hq4 : 2 * lww * (30 * (n / Q) * (1 + l2ww)) ≤ 1200 * (E * (n / L ^ 3)) := by
    have hmain : 2 * lww * (30 * (n / Q) * (1 + l2ww))
        ≤ (60 * (4 * L)) * (n / L ^ 12) * (5 * L) := by
      calc 2 * lww * (30 * (n / Q) * (1 + l2ww)) = (60 * lww) * (n / Q) * (1 + l2ww) := by ring
        _ ≤ (60 * (4 * L)) * (n / L ^ 12) * (5 * L) :=
            mul_three_le (by linarith only [hlww0]) hnQ0 (by linarith only [hl2ww0])
              (by linarith only [hlww]) hnQ (by linarith only [hl2ww, hL1])
    have hrw : (60 * (4 * L)) * (n / L ^ 12) * (5 * L) = 1200 * (L ^ 2 * (n / L ^ 12)) := by
      ring
    rw [hrw, hidA] at hmain
    have h2 : n / L ^ 10 ≤ E * (n / L ^ 3) := by
      nlinarith only [hnL10, hY0, hE]
    linarith only [hmain, h2]
  have hq5 : 2 * lww * (12 * (w * w + Q) * (1 + lq))
      ≤ 192 * (L ^ 3 * (n / Real.sqrt w)) + 768 * (E * (n / L ^ 3)) := by
    have hmain : 2 * lww * (12 * (w * w + Q) * (1 + lq))
        ≤ (8 * L) * (12 * (n / Real.sqrt w + 4 * E * n / L ^ 12)) * (1 + L) := by
      calc 2 * lww * (12 * (w * w + Q) * (1 + lq))
          = (2 * lww) * (12 * (w * w + Q)) * (1 + lq) := by ring
        _ ≤ (8 * L) * (12 * (n / Real.sqrt w + 4 * E * n / L ^ 12)) * (1 + L) :=
            mul_three_le (by linarith only [hlww0])
              (by nlinarith only [hX0, hQ0', hw0])
              (by linarith only [hlq0])
              (by linarith only [hlww])
              (by linarith only [hw2X, hQub])
              (by linarith only [hlq])
    linarith only [hmain, halg]
  have hq6 : 2 * (kk * (Real.sqrt 2 * ln * (Real.sqrt (7 * hi * n) + Real.sqrt (6 * n ^ 2 / Q)
        + Real.sqrt (12 * n ^ 2 * (1 + lq) / w) + Real.sqrt (12 * n * Q * (1 + lq)))))
      ≤ 468 * (L ^ 3 * (n / Real.sqrt w)) + 468 * (E * (n / L ^ 3)) := by
    have hS0 : (0 : ℝ) ≤ Real.sqrt (7 * hi * n) + Real.sqrt (6 * n ^ 2 / Q)
        + Real.sqrt (12 * n ^ 2 * (1 + lq) / w) + Real.sqrt (12 * n * Q * (1 + lq)) := by
      positivity
    have hSub : Real.sqrt (7 * hi * n) + Real.sqrt (6 * n ^ 2 / Q)
        + Real.sqrt (12 * n ^ 2 * (1 + lq) / w) + Real.sqrt (12 * n * Q * (1 + lq))
        ≤ 8 * (n / Real.sqrt w) + 3 * (n / L ^ 6) + 5 * L * (n / Real.sqrt w)
          + 10 * (E * (n / L ^ 5)) := by linarith only [hA, hB, hC, hD]
    have hln2 : Real.sqrt 2 * ln ≤ 3 * L := by
      have h := mul_le_mul hsqrt2 hln hln0 (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith only [h]
    have hmain : 2 * (kk * (Real.sqrt 2 * ln * (Real.sqrt (7 * hi * n) + Real.sqrt (6 * n ^ 2 / Q)
          + Real.sqrt (12 * n ^ 2 * (1 + lq) / w) + Real.sqrt (12 * n * Q * (1 + lq)))))
        ≤ (12 * L) * (3 * L) * (8 * (n / Real.sqrt w) + 3 * (n / L ^ 6) + 5 * L * (n / Real.sqrt w)
          + 10 * (E * (n / L ^ 5))) := by
      calc 2 * (kk * (Real.sqrt 2 * ln * (Real.sqrt (7 * hi * n) + Real.sqrt (6 * n ^ 2 / Q)
            + Real.sqrt (12 * n ^ 2 * (1 + lq) / w) + Real.sqrt (12 * n * Q * (1 + lq)))))
          = (2 * kk) * (Real.sqrt 2 * ln) * (Real.sqrt (7 * hi * n) + Real.sqrt (6 * n ^ 2 / Q)
            + Real.sqrt (12 * n ^ 2 * (1 + lq) / w) + Real.sqrt (12 * n * Q * (1 + lq))) := by
            ring
        _ ≤ (12 * L) * (3 * L) * (8 * (n / Real.sqrt w) + 3 * (n / L ^ 6)
            + 5 * L * (n / Real.sqrt w) + 10 * (E * (n / L ^ 5))) :=
            mul_three_le (by linarith only [hkk0]) (mul_nonneg (Real.sqrt_nonneg 2) hln0) hS0
              (by linarith only [hkk]) hln2 hSub
    have hrw : (12 * L) * (3 * L) * (8 * (n / Real.sqrt w) + 3 * (n / L ^ 6)
        + 5 * L * (n / Real.sqrt w) + 10 * (E * (n / L ^ 5)))
        = 288 * (L ^ 2 * (n / Real.sqrt w)) + 108 * (L ^ 2 * (n / L ^ 6))
          + 180 * (L ^ 3 * (n / Real.sqrt w)) + 360 * E * (L ^ 2 * (n / L ^ 5)) := by
      ring
    rw [hrw, hidB, hidC] at hmain
    have h1 : 288 * (L ^ 2 * (n / Real.sqrt w)) ≤ 288 * (L ^ 3 * (n / Real.sqrt w)) := by
      nlinarith only [hX0, hL23]
    have h2 : 108 * (n / L ^ 4) ≤ 108 * (E * (n / L ^ 3)) := by
      nlinarith only [hnL4, hY0, hE]
    have h3 : 360 * E * (n / L ^ 3) ≤ 360 * (E * (n / L ^ 3)) := le_of_eq (by ring)
    linarith only [hmain, h1, h2, h3]
  have hq7 : 4 * Real.sqrt n * ln ≤ 8 * (L ^ 3 * (n / Real.sqrt w)) := by
    have h1 : Real.sqrt n * ln ≤ (n / Real.sqrt w) * (2 * L) :=
      mul_le_mul hsqrtnX hln hln0 hX0
    nlinarith only [h1, hX0, hL13]
  -- ### the numerator
  have hnum : 2 * (w * lw
        + (2 * ln * (30 * (n / Q) * (1 + l2w) + 12 * (w + Q) * (1 + lq))
          + lww * (30 * (n / Q) * (1 + l2ww) + 12 * (w * w + Q) * (1 + lq)))
        + kk * (Real.sqrt 2 * ln * (Real.sqrt (7 * hi * n) + Real.sqrt (6 * n ^ 2 / Q)
            + Real.sqrt (12 * n ^ 2 * (1 + lq) / w) + Real.sqrt (12 * n * Q * (1 + lq)))))
      + 4 * Real.sqrt n * ln
      ≤ 1000 * (L ^ 3 * (n / Real.sqrt w)) + 5000 * (E * (n / L ^ 3)) := by
    linarith only [hq1, hq2, hq3, hq4, hq5, hq6, hq7, hPX0, hEY0]
  -- ### the denominator
  have hlm0 : (0 : ℝ) ≤ lm := by linarith only [hlm, hL0]
  have hden : n * L / 12 ≤ m * lm := by
    have h1 : n / 3 ≤ m := by linarith only [hnm]
    calc n * L / 12 = (n / 3) * (L / 4) := by ring
      _ ≤ m * (L / 4) := mul_le_mul_of_nonneg_right h1 (by linarith only [hL0])
      _ ≤ m * lm := mul_le_mul_of_nonneg_left hlm (by linarith only [hm])
  have hdpos : (0 : ℝ) < n * L / 12 := by
    have := mul_pos hn0 hL0; linarith only [this]
  -- ### divide
  refine le_trans (div_le_div₀ (by linarith only [hPX0, hEY0]) hnum hdpos hden) (le_of_eq ?_)
  field_simp
  ring

/-! ## §2 — the concrete gates -/

/-- **The exponent close at the explicit arms.**  Every hypothesis is an explicit
inequality on `H`; `exitClose_twelve` supplies them from one `max` of ceilings. -/
theorem exitBd_lt_of_arms {eps : ℚ} (heps : 0 < eps) {H q : ℕ}
    (hH4 : (4 : ℝ) / (eps : ℝ) ^ 2 ≤ (H : ℝ))
    (hHe : (eps : ℝ) ^ 2 ≤ (H : ℝ))
    (hH4e : (4 : ℝ) / (eps : ℝ) ^ 4 ≤ (H : ℝ))
    (hLbig : (25 : ℝ) ^ 25 * (10 ^ 40 * (1 + 1 / (eps : ℝ) ^ 2) ^ 9) ≤ Real.log (H : ℝ))
    (hq1 : arcDen 12 H < (q : ℝ)) (hq2 : (q : ℝ) ≤ (H : ℝ) / arcDen 12 H + 1) :
    exitBd eps H q < (eps : ℝ) ^ 2 / Real.log (H : ℝ) := by
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have he2 : (0 : ℝ) < (eps : ℝ) ^ 2 := pow_pos hepsR 2
  set E : ℝ := 1 + 1 / (eps : ℝ) ^ 2 with hEdef
  have hE1 : (1 : ℝ) ≤ E := by
    have h : (0 : ℝ) < 1 / (eps : ℝ) ^ 2 := one_div_pos.mpr he2
    rw [hEdef]; linarith only [h]
  have hE0 : (0 : ℝ) ≤ E := by linarith only [hE1]
  have hEe : (1 : ℝ) ≤ E * (eps : ℝ) ^ 2 := by
    have h : E * (eps : ℝ) ^ 2 = (eps : ℝ) ^ 2 + 1 := by
      rw [hEdef]; field_simp
    rw [h]; linarith only [he2]
  have hE9 : (1 : ℝ) ≤ E ^ 9 := one_le_pow₀ hE1
  -- ### the scale
  have hH0 : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le (div_pos (by norm_num) he2) hH4
  have hL8 : (8 : ℝ) ≤ Real.log (H : ℝ) := by
    refine le_trans ?_ hLbig
    calc (8 : ℝ) ≤ 25 ^ 25 * 10 ^ 40 := by norm_num
      _ = 25 ^ 25 * 10 ^ 40 * 1 := by ring
      _ ≤ 25 ^ 25 * 10 ^ 40 * E ^ 9 := mul_le_mul_of_nonneg_left hE9 (by norm_num)
      _ = 25 ^ 25 * (10 ^ 40 * E ^ 9) := by ring
  have hL1 : (1 : ℝ) ≤ Real.log (H : ℝ) := by linarith only [hL8]
  have hL0 : (0 : ℝ) < Real.log (H : ℝ) := by linarith only [hL8]
  have hmaster : 10 ^ 40 * E ^ 9 * Real.log (H : ℝ) ^ 24 ≤ (H : ℝ) := by
    have hC : (0 : ℝ) < 10 ^ 40 * E ^ 9 :=
      mul_pos (by norm_num) (by linarith only [hE9])
    have h := pow24_le_exp (C := 10 ^ 40 * E ^ 9) hC hLbig
    rwa [Real.exp_log hH0] at h
  have hL24pos : (0 : ℝ) ≤ Real.log (H : ℝ) ^ 24 := pow_nonneg hL0.le 24
  have hL24 : Real.log (H : ℝ) ^ 24 ≤ (H : ℝ) := by
    nlinarith only [hmaster, hL24pos, hE9]
  have hL12H : Real.log (H : ℝ) ^ 12 ≤ (H : ℝ) :=
    le_trans (pow_le_pow_right₀ hL1 (by norm_num)) hL24
  have hL12big : (2 : ℝ) ≤ Real.log (H : ℝ) ^ 12 := by
    calc (2 : ℝ) ≤ 8 ^ 12 := by norm_num
      _ ≤ Real.log (H : ℝ) ^ 12 := pow_le_pow_left₀ (by norm_num) hL8 12
  have hH2 : (2 : ℝ) ≤ (H : ℝ) := le_trans hL12big hL12H
  -- ### the window
  have hN_ub : ((winTop eps H : ℕ) : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    have h : ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
      Nat.floor_le (by positivity)
    have h2 : (((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℚ) : ℝ) ≤ ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast h
    rw [winTop]; push_cast at h2 ⊢; exact h2
  have hN_lb : (eps : ℝ) ^ 2 * (H : ℝ) - 1 ≤ ((winTop eps H : ℕ) : ℝ) := by
    have h : eps ^ 2 * (H : ℚ) < ((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℚ) + 1 := Nat.lt_floor_add_one _
    have h2 : ((eps ^ 2 * (H : ℚ) : ℚ) : ℝ) < ((((⌊eps ^ 2 * (H : ℚ)⌋₊ : ℕ) : ℚ) + 1 : ℚ) : ℝ) := by
      exact_mod_cast h
    rw [winTop]; push_cast at h2 ⊢; linarith only [h2]
  have hM_lb : (eps : ℝ) ^ 2 * (H : ℝ) / 2 - 1 ≤ ((winBot eps H : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one ((eps : ℝ) ^ 2 * (H : ℝ) / 2)
    rw [winBot]; linarith only [h]
  have hM2 : (2 : ℝ) ≤ ((winBot eps H : ℕ) : ℝ) := by
    have h : 2 ≤ winBot eps H := two_le_winBot heps hH4
    exact_mod_cast h
  have hMN : ((winBot eps H : ℕ) : ℝ) ≤ ((winTop eps H : ℕ) : ℝ) := by
    have h : winBot eps H ≤ winTop eps H := winBot_le_winTop heps H
    exact_mod_cast h
  have hN2 : (2 : ℝ) ≤ ((winTop eps H : ℕ) : ℝ) := le_trans hM2 hMN
  have hN0 : (0 : ℝ) < ((winTop eps H : ℕ) : ℝ) := by linarith only [hN2]
  have hnm3 : ((winTop eps H : ℕ) : ℝ) ≤ 3 * ((winBot eps H : ℕ) : ℝ) := by
    linarith only [hN_ub, hM_lb, hM2]
  -- ### the Vaughan parameter
  have hW1 : 1 ≤ vaughanW eps H := by
    refine one_le_vaughanW ?_
    have h : 2 ≤ winBot eps H := two_le_winBot heps hH4
    omega
  have hw1R : (1 : ℝ) ≤ ((vaughanW eps H : ℕ) : ℝ) := by exact_mod_cast hW1
  have hw0R : (0 : ℝ) < ((vaughanW eps H : ℕ) : ℝ) := by linarith only [hw1R]
  have hW4M : vaughanW eps H ^ 4 ≤ winBot eps H := by
    have h1 : vaughanW eps H * vaughanW eps H ≤ Nat.sqrt (winBot eps H) := by
      rw [vaughanW]; exact Nat.sqrt_le _
    calc vaughanW eps H ^ 4
        = vaughanW eps H * vaughanW eps H * (vaughanW eps H * vaughanW eps H) := by ring
      _ ≤ Nat.sqrt (winBot eps H) * Nat.sqrt (winBot eps H) := Nat.mul_le_mul h1 h1
      _ ≤ winBot eps H := Nat.sqrt_le _
  have hw4R : ((vaughanW eps H : ℕ) : ℝ) ^ 4 ≤ ((winTop eps H : ℕ) : ℝ) := by
    have h : vaughanW eps H ^ 4 ≤ winTop eps H := le_trans hW4M (winBot_le_winTop heps H)
    exact_mod_cast h
  have hw2R : ((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ)
      ≤ ((winTop eps H : ℕ) : ℝ) := by
    have h : vaughanW eps H * vaughanW eps H ≤ winTop eps H :=
      le_trans (vaughanW_sq_le eps H) (winBot_le_winTop heps H)
    exact_mod_cast h
  have hM16 : ((winBot eps H : ℕ) : ℝ) ≤ 16 * ((vaughanW eps H : ℕ) : ℝ) ^ 4 := by
    have h1 : Nat.sqrt (winBot eps H) < (vaughanW eps H + 1) * (vaughanW eps H + 1) := by
      rw [vaughanW]; exact Nat.lt_succ_sqrt _
    have h2 : winBot eps H
        < (Nat.sqrt (winBot eps H) + 1) * (Nat.sqrt (winBot eps H) + 1) := Nat.lt_succ_sqrt _
    have h3 : Nat.sqrt (winBot eps H) + 1 ≤ (vaughanW eps H + 1) * (vaughanW eps H + 1) := h1
    have h5 := Nat.mul_le_mul h3 h3
    have h6 : (Nat.sqrt (winBot eps H) + 1) * (Nat.sqrt (winBot eps H) + 1)
        ≤ (vaughanW eps H + 1) ^ 4 := by
      calc (Nat.sqrt (winBot eps H) + 1) * (Nat.sqrt (winBot eps H) + 1)
          ≤ (vaughanW eps H + 1) * (vaughanW eps H + 1)
            * ((vaughanW eps H + 1) * (vaughanW eps H + 1)) := h5
        _ = (vaughanW eps H + 1) ^ 4 := by ring
    have h7 : (vaughanW eps H + 1) ^ 4 ≤ 16 * vaughanW eps H ^ 4 := by
      calc (vaughanW eps H + 1) ^ 4 ≤ (2 * vaughanW eps H) ^ 4 :=
            Nat.pow_le_pow_left (by omega) 4
        _ = 16 * vaughanW eps H ^ 4 := by ring
    have h8 : winBot eps H ≤ 16 * vaughanW eps H ^ 4 := by omega
    exact_mod_cast h8
  -- ### the logarithms
  have hnH2 : ((winTop eps H : ℕ) : ℝ) ≤ (H : ℝ) ^ 2 := by
    nlinarith only [hN_ub, hHe, hH0]
  have hln2L : Real.log ((winTop eps H : ℕ) : ℝ) ≤ 2 * Real.log (H : ℝ) := by
    have h1 := Real.log_le_log hN0 hnH2
    rw [Real.log_pow] at h1; push_cast at h1; linarith only [h1]
  have hln0 : (0 : ℝ) ≤ Real.log ((winTop eps H : ℕ) : ℝ) :=
    Real.log_nonneg (by linarith only [hN2])
  have hsqrtH : Real.sqrt (H : ℝ) ≤ ((winTop eps H : ℕ) : ℝ) := by
    have ht : Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) = (H : ℝ) := Real.mul_self_sqrt hH0.le
    have ht2 : (2 : ℝ) / (eps : ℝ) ^ 2 ≤ Real.sqrt (H : ℝ) := by
      have hsq : ((2 : ℝ) / (eps : ℝ) ^ 2) ^ 2 ≤ (H : ℝ) := by
        have hid : ((2 : ℝ) / (eps : ℝ) ^ 2) ^ 2 = 4 / (eps : ℝ) ^ 4 := by
          field_simp; ring
        rw [hid]; exact hH4e
      have h1 : Real.sqrt (((2 : ℝ) / (eps : ℝ) ^ 2) ^ 2) ≤ Real.sqrt (H : ℝ) :=
        Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by positivity)] at h1
    have ht1 : (1 : ℝ) ≤ Real.sqrt (H : ℝ) := by
      have h1 : Real.sqrt 1 ≤ Real.sqrt (H : ℝ) := Real.sqrt_le_sqrt (by linarith only [hH2])
      rwa [Real.sqrt_one] at h1
    have h1 : (2 / (eps : ℝ) ^ 2) * Real.sqrt (H : ℝ) ≤ (H : ℝ) := by
      calc (2 / (eps : ℝ) ^ 2) * Real.sqrt (H : ℝ) ≤ Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ) :=
            mul_le_mul_of_nonneg_right ht2 (Real.sqrt_nonneg _)
        _ = (H : ℝ) := ht
    have h2 : 2 * Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
      have h3 := mul_le_mul_of_nonneg_left h1 he2.le
      calc 2 * Real.sqrt (H : ℝ)
          = (eps : ℝ) ^ 2 * ((2 / (eps : ℝ) ^ 2) * Real.sqrt (H : ℝ)) := by field_simp
        _ ≤ (eps : ℝ) ^ 2 * (H : ℝ) := h3
    linarith only [hN_lb, ht1, h2]
  have hlnhalf : Real.log (H : ℝ) / 2 ≤ Real.log ((winTop eps H : ℕ) : ℝ) := by
    have h1 := Real.log_le_log (Real.sqrt_pos.mpr hH0) hsqrtH
    rwa [Real.log_sqrt hH0.le] at h1
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith only [h]
  have hlm : Real.log (H : ℝ) / 4 ≤ Real.log ((winBot eps H : ℕ) : ℝ) := by
    have h1 : ((winTop eps H : ℕ) : ℝ) / 3 ≤ ((winBot eps H : ℕ) : ℝ) := by
      linarith only [hnm3]
    have h2 := Real.log_le_log
      (by linarith only [hN2] : (0 : ℝ) < ((winTop eps H : ℕ) : ℝ) / 3) h1
    rw [Real.log_div (by linarith only [hN2]) (by norm_num)] at h2
    linarith only [h2, hlnhalf, hlog3, hL8]
  have hlw0 : (0 : ℝ) ≤ Real.log ((vaughanW eps H : ℕ) : ℝ) := Real.log_nonneg hw1R
  have hwn : ((vaughanW eps H : ℕ) : ℝ) ≤ ((winTop eps H : ℕ) : ℝ) := by
    nlinarith only [hw2R, hw1R]
  have hlw : Real.log ((vaughanW eps H : ℕ) : ℝ) ≤ 4 * Real.log (H : ℝ) := by
    have h1 := Real.log_le_log hw0R hwn
    linarith only [h1, hln2L, hL0]
  have hl2w0 : (0 : ℝ) ≤ Real.log (2 * ((vaughanW eps H : ℕ) : ℝ)) :=
    Real.log_nonneg (by linarith only [hw1R])
  have hl2w : Real.log (2 * ((vaughanW eps H : ℕ) : ℝ)) ≤ 4 * Real.log (H : ℝ) := by
    have hle : 2 * ((vaughanW eps H : ℕ) : ℝ) ≤ ((winTop eps H : ℕ) : ℝ) ^ 2 := by
      nlinarith only [hwn, hN2]
    have h1 := Real.log_le_log (by linarith only [hw1R]) hle
    rw [Real.log_pow] at h1; push_cast at h1; linarith only [h1, hln2L]
  have hww1 : (1 : ℝ) ≤ ((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ) := by
    nlinarith only [hw1R]
  have hlww0 : (0 : ℝ) ≤ Real.log (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ)) :=
    Real.log_nonneg hww1
  have hlww : Real.log (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ))
      ≤ 4 * Real.log (H : ℝ) := by
    have h1 := Real.log_le_log (by linarith only [hww1]) hw2R
    linarith only [h1, hln2L, hL0]
  have hl2ww0 : (0 : ℝ)
      ≤ Real.log (2 * (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ))) :=
    Real.log_nonneg (by linarith only [hww1])
  have hl2ww : Real.log (2 * (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ)))
      ≤ 4 * Real.log (H : ℝ) := by
    have hle : 2 * (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ))
        ≤ ((winTop eps H : ℕ) : ℝ) ^ 2 := by nlinarith only [hw2R, hN2]
    have h1 := Real.log_le_log (by linarith only [hww1]) hle
    rw [Real.log_pow] at h1; push_cast at h1; linarith only [h1, hln2L]
  -- ### the denominator `q`
  have harc : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [harc] at hq1 hq2
  have hQ1 : Real.log (H : ℝ) ^ 12 ≤ (q : ℝ) := le_of_lt hq1
  have hQ0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le (by linarith only [hL12big]) hQ1
  have hqH : (q : ℝ) ≤ (H : ℝ) := by
    have h1 : (H : ℝ) / Real.log (H : ℝ) ^ 12 ≤ (H : ℝ) / 2 :=
      div_le_div_of_nonneg_left hH0.le (by norm_num) hL12big
    linarith only [hq2, h1, hH2]
  have hlq0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith only [hQ1, hL12big])
  have hlq : Real.log (q : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log hQ0 hqH
  have hQ3 : (q : ℝ) * Real.log (H : ℝ) ^ 12 ≤ 4 * E * ((winTop eps H : ℕ) : ℝ) := by
    have hA : (q : ℝ) * Real.log (H : ℝ) ^ 12 ≤ 2 * (H : ℝ) := by
      have h1 : (1 : ℝ) ≤ (H : ℝ) / Real.log (H : ℝ) ^ 12 :=
        (one_le_div (pow_pos hL0 12)).mpr hL12H
      have h2 : (q : ℝ) ≤ 2 * ((H : ℝ) / Real.log (H : ℝ) ^ 12) := by linarith only [hq2, h1]
      calc (q : ℝ) * Real.log (H : ℝ) ^ 12
          ≤ (2 * ((H : ℝ) / Real.log (H : ℝ) ^ 12)) * Real.log (H : ℝ) ^ 12 :=
            mul_le_mul_of_nonneg_right h2 (pow_nonneg hL0.le 12)
        _ = 2 * (H : ℝ) := by field_simp
    have hB : (eps : ℝ) ^ 2 * (H : ℝ) ≤ 2 * ((winTop eps H : ℕ) : ℝ) := by
      linarith only [hN_lb, hN2]
    have hC : ((q : ℝ) * Real.log (H : ℝ) ^ 12) * (eps : ℝ) ^ 2
        ≤ 4 * ((winTop eps H : ℕ) : ℝ) := by nlinarith only [hA, hB, he2]
    have hD : (0 : ℝ) ≤ (q : ℝ) * Real.log (H : ℝ) ^ 12 :=
      mul_nonneg hQ0.le (pow_nonneg hL0.le 12)
    nlinarith only [mul_le_mul_of_nonneg_left hC hE0, mul_le_mul_of_nonneg_left hEe hD]
  -- ### the dyadic cut
  have hN2nat : 2 ≤ winTop eps H := by exact_mod_cast hN2
  have h2j : 2 ^ Nat.log 2 (winTop eps H / (vaughanW eps H * vaughanW eps H)) ≤ winTop eps H := by
    rcases Nat.eq_zero_or_pos (winTop eps H / (vaughanW eps H * vaughanW eps H)) with h | h
    · rw [h, Nat.log_zero_right]; omega
    · exact le_trans (Nat.pow_log_le_self 2 (by omega)) (Nat.div_le_self _ _)
  have hkkR : ((dyadicK eps H : ℕ) : ℝ) ≤ 6 * Real.log (H : ℝ) := by
    have h1 : ((2 : ℝ)) ^ Nat.log 2 (winTop eps H / (vaughanW eps H * vaughanW eps H))
        ≤ ((winTop eps H : ℕ) : ℝ) := by exact_mod_cast h2j
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h4 : (0 : ℝ)
        ≤ ((Nat.log 2 (winTop eps H / (vaughanW eps H * vaughanW eps H)) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have h5 : ((Nat.log 2 (winTop eps H / (vaughanW eps H * vaughanW eps H)) : ℕ) : ℝ)
        * 0.6931471803 ≤ 2 * Real.log (H : ℝ) := by
      nlinarith only [h2, hln2L, h3, h4]
    rw [dyadicK]
    push_cast
    linarith only [h5, hL8]
  have hkk0 : (0 : ℝ) ≤ ((dyadicK eps H : ℕ) : ℝ) := Nat.cast_nonneg _
  have hhi_eq : dyadicHi eps H = ((vaughanW eps H : ℕ) : ℝ) * 2 ^ (dyadicK eps H) := by
    rw [dyadicHi]; push_cast; ring
  have hWW0 : (0 : ℝ) ≤ ((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ) :=
    mul_nonneg hw0R.le hw0R.le
  have hhi : dyadicHi eps H * ((vaughanW eps H : ℕ) : ℝ)
      ≤ 2 * ((winTop eps H : ℕ) : ℝ)
        + 2 * (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ)) := by
    have hpow : (2 : ℝ) ^ (dyadicK eps H)
        = 2 * 2 ^ Nat.log 2 (winTop eps H / (vaughanW eps H * vaughanW eps H)) := by
      rw [dyadicK]; ring
    rcases Nat.eq_zero_or_pos (winTop eps H / (vaughanW eps H * vaughanW eps H)) with h | h
    · have hz : Nat.log 2 (winTop eps H / (vaughanW eps H * vaughanW eps H)) = 0 := by
        rw [h, Nat.log_zero_right]
      rw [hhi_eq, hpow, hz, pow_zero]
      linarith only [hN0]
    · have hdle : ((2 : ℝ)) ^ Nat.log 2 (winTop eps H / (vaughanW eps H * vaughanW eps H))
          ≤ ((winTop eps H : ℕ) : ℝ)
            / (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ)) := by
        have h1 : (2 : ℕ) ^ Nat.log 2 (winTop eps H / (vaughanW eps H * vaughanW eps H))
            ≤ winTop eps H / (vaughanW eps H * vaughanW eps H) :=
          Nat.pow_log_le_self 2 (by omega)
        have h2 : ((2 : ℝ)) ^ Nat.log 2 (winTop eps H / (vaughanW eps H * vaughanW eps H))
            ≤ ((winTop eps H / (vaughanW eps H * vaughanW eps H) : ℕ) : ℝ) := by
          exact_mod_cast h1
        refine le_trans h2 ?_
        have h3 : ((winTop eps H / (vaughanW eps H * vaughanW eps H) : ℕ) : ℝ)
            ≤ ((winTop eps H : ℕ) : ℝ) / ((vaughanW eps H * vaughanW eps H : ℕ) : ℝ) :=
          Nat.cast_div_le
        push_cast at h3
        exact h3
      have hmul := mul_le_mul_of_nonneg_left hdle
        (by linarith only [hWW0] :
          (0 : ℝ) ≤ 2 * (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ)))
      have hid : 2 * (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ))
          * (((winTop eps H : ℕ) : ℝ)
            / (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ)))
          = 2 * ((winTop eps H : ℕ) : ℝ) := by
        field_simp
      rw [hid] at hmul
      rw [hhi_eq, hpow]
      nlinarith only [hmul, hWW0]
  -- ### the collection
  have hcol : exitBd eps H q
      ≤ 12000 * Real.log (H : ℝ) ^ 2 / Real.sqrt ((vaughanW eps H : ℕ) : ℝ)
        + 60000 * E / Real.log (H : ℝ) ^ 4 := by
    refine le_trans (le_of_eq ?_)
      (exit_collect (n := ((winTop eps H : ℕ) : ℝ)) (m := ((winBot eps H : ℕ) : ℝ))
        (w := ((vaughanW eps H : ℕ) : ℝ)) (hi := dyadicHi eps H) (Q := (q : ℝ))
        (L := Real.log (H : ℝ)) (ln := Real.log ((winTop eps H : ℕ) : ℝ))
        (lm := Real.log ((winBot eps H : ℕ) : ℝ))
        (lw := Real.log ((vaughanW eps H : ℕ) : ℝ))
        (l2w := Real.log (2 * ((vaughanW eps H : ℕ) : ℝ)))
        (lww := Real.log (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ)))
        (l2ww := Real.log (2 * (((vaughanW eps H : ℕ) : ℝ) * ((vaughanW eps H : ℕ) : ℝ))))
        (lq := Real.log (q : ℝ)) (kk := ((dyadicK eps H : ℕ) : ℝ)) (E := E)
        hE1 hL8 hM2 hw1R hnm3 hMN hw4R hw2R hln0 hln2L hlm hlw0 hlw hl2w0 hl2w
        hlww0 hlww hl2ww0 hl2ww hlq0 hlq hQ0 hQ1 hQ3 hkk0 hkkR hhi)
    rw [exitBd, vinoBd]
    push_cast
    ring
  refine lt_of_le_of_lt hcol ?_
  -- ### the threshold
  have hEL24 : (0 : ℝ) ≤ E ^ 8 * Real.log (H : ℝ) ^ 24 :=
    mul_nonneg (by positivity) hL24pos
  have hw4big : 50000 ^ 8 * (E ^ 8 * Real.log (H : ℝ) ^ 24)
      ≤ ((vaughanW eps H : ℕ) : ℝ) ^ 4 := by
    have hkey1 : 10 ^ 40 * (E ^ 8 * Real.log (H : ℝ) ^ 24) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
      calc 10 ^ 40 * (E ^ 8 * Real.log (H : ℝ) ^ 24)
          = (10 ^ 40 * (E ^ 8 * Real.log (H : ℝ) ^ 24)) * 1 := by ring
        _ ≤ (10 ^ 40 * (E ^ 8 * Real.log (H : ℝ) ^ 24)) * (E * (eps : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hEe (by linarith only [hEL24])
        _ = (eps : ℝ) ^ 2 * (10 ^ 40 * E ^ 9 * Real.log (H : ℝ) ^ 24) := by ring
        _ ≤ (eps : ℝ) ^ 2 * (H : ℝ) := mul_le_mul_of_nonneg_left hmaster he2.le
    have hm4 : (eps : ℝ) ^ 2 * (H : ℝ) / 4 ≤ ((winBot eps H : ℕ) : ℝ) := by
      have h4 : (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
        have h5 := mul_le_mul_of_nonneg_left hH4 he2.le
        calc (4 : ℝ) = (eps : ℝ) ^ 2 * (4 / (eps : ℝ) ^ 2) := by field_simp
          _ ≤ (eps : ℝ) ^ 2 * (H : ℝ) := h5
      linarith only [hM_lb, h4]
    linarith only [hkey1, hm4, hM16, hEL24]
  have hwsq : (50000 * Real.log (H : ℝ) ^ 3 * E) ^ 2 ≤ ((vaughanW eps H : ℕ) : ℝ) := by
    refine (pow_le_pow_iff_left₀ (sq_nonneg _) (by linarith only [hw0R])
      (by norm_num : (4 : ℕ) ≠ 0)).mp ?_
    calc ((50000 * Real.log (H : ℝ) ^ 3 * E) ^ 2) ^ 4
        = 50000 ^ 8 * (E ^ 8 * Real.log (H : ℝ) ^ 24) := by ring
      _ ≤ ((vaughanW eps H : ℕ) : ℝ) ^ 4 := hw4big
  have hL3pos : (0 : ℝ) < Real.log (H : ℝ) ^ 3 := pow_pos hL0 3
  have hLE0 : (0 : ℝ) < 50000 * Real.log (H : ℝ) ^ 3 * E := by
    have h := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 50000) hL3pos)
      (lt_of_lt_of_le zero_lt_one hE1)
    exact h
  have hsqrtw : 50000 * Real.log (H : ℝ) ^ 3 * E
      ≤ Real.sqrt ((vaughanW eps H : ℕ) : ℝ) := by
    have h1 := Real.sqrt_le_sqrt hwsq
    rwa [Real.sqrt_sq hLE0.le] at h1
  have hfin1 : 12000 * Real.log (H : ℝ) ^ 2 / Real.sqrt ((vaughanW eps H : ℕ) : ℝ)
      ≤ (eps : ℝ) ^ 2 / (4 * Real.log (H : ℝ)) := by
    have h1 : 12000 * Real.log (H : ℝ) ^ 2 / Real.sqrt ((vaughanW eps H : ℕ) : ℝ)
        ≤ 12000 * Real.log (H : ℝ) ^ 2 / (50000 * Real.log (H : ℝ) ^ 3 * E) :=
      div_le_div_of_nonneg_left (by positivity) hLE0 hsqrtw
    refine le_trans h1 ?_
    rw [div_le_div_iff₀ hLE0 (by linarith only [hL0])]
    nlinarith only [hEe, hL3pos]
  have hLcube : 240000 * E ^ 2 ≤ Real.log (H : ℝ) ^ 3 := by
    have h1 : 240000 * E ^ 2 ≤ Real.log (H : ℝ) := by
      refine le_trans ?_ hLbig
      have h2 : E ^ 2 ≤ E ^ 9 := pow_le_pow_right₀ hE1 (by norm_num)
      calc 240000 * E ^ 2 ≤ 240000 * E ^ 9 := by linarith only [h2]
        _ ≤ 25 ^ 25 * (10 ^ 40 * E ^ 9) := by nlinarith only [hE9]
    have h3 : Real.log (H : ℝ) ≤ Real.log (H : ℝ) ^ 3 := by
      have h := pow_le_pow_right₀ hL1 (show 1 ≤ 3 by norm_num); simpa using h
    linarith only [h1, h3]
  have hfin2 : 60000 * E / Real.log (H : ℝ) ^ 4 ≤ (eps : ℝ) ^ 2 / (4 * Real.log (H : ℝ)) := by
    rw [div_le_div_iff₀ (pow_pos hL0 4) (by linarith only [hL0])]
    have hA : 240000 * E ^ 2 * ((eps : ℝ) ^ 2 * Real.log (H : ℝ))
        ≤ Real.log (H : ℝ) ^ 3 * ((eps : ℝ) ^ 2 * Real.log (H : ℝ)) :=
      mul_le_mul_of_nonneg_right hLcube (by positivity)
    have hB : 240000 * E * Real.log (H : ℝ) * 1
        ≤ 240000 * E * Real.log (H : ℝ) * (E * (eps : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hEe
        (by nlinarith only [hE0, hL0] : (0 : ℝ) ≤ 240000 * E * Real.log (H : ℝ))
    nlinarith only [hA, hB]
  have hstrict : (eps : ℝ) ^ 2 / (4 * Real.log (H : ℝ)) + (eps : ℝ) ^ 2 / (4 * Real.log (H : ℝ))
      < (eps : ℝ) ^ 2 / Real.log (H : ℝ) := by
    have hid : (eps : ℝ) ^ 2 / (4 * Real.log (H : ℝ)) + (eps : ℝ) ^ 2 / (4 * Real.log (H : ℝ))
        = (eps : ℝ) ^ 2 / (2 * Real.log (H : ℝ)) := by
      field_simp
      ring
    rw [hid, div_lt_div_iff₀ (by linarith only [hL0]) hL0]
    nlinarith only [he2, hL0]
  linarith only [hfin1, hfin2, hstrict]

/-! ## §3 — the close, and the two exports -/

/-- **`ExitClose 12` — the last stone of the S7 arc.**  `H₀(ε)` is the explicit
four-armed maximum: the window floor `4/ε²`, the `log N ≤ 2 log H` arm `ε²`, the
`log N ≥ (log H)/2` arm `4/ε⁴`, and the threshold arm `exp(25^25·10^40·(1+ε⁻²)^9)`. -/
theorem exitClose_twelve : ExitClose 12 := by
  intro eps heps
  refine ⟨max (max (⌈(4 : ℝ) / (eps : ℝ) ^ 2⌉₊ + 1) (⌈((eps : ℝ)) ^ 2⌉₊ + 1))
      (max (⌈(4 : ℝ) / (eps : ℝ) ^ 4⌉₊ + 1)
        (⌈Real.exp ((25 : ℝ) ^ 25 * (10 ^ 40 * (1 + 1 / (eps : ℝ) ^ 2) ^ 9))⌉₊ + 1)), ?_⟩
  intro H hH q hq1 hq2
  have harm : ∀ x : ℝ, ⌈x⌉₊ + 1 ≤ H → x ≤ (H : ℝ) := by
    intro x hx
    have h1 : x ≤ ((⌈x⌉₊ : ℕ) : ℝ) := Nat.le_ceil x
    have h2 : ((⌈x⌉₊ : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast (by omega : ⌈x⌉₊ ≤ H)
    linarith only [h1, h2]
  have hH4 : (4 : ℝ) / (eps : ℝ) ^ 2 ≤ (H : ℝ) :=
    harm _ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hH)
  have hHe : (eps : ℝ) ^ 2 ≤ (H : ℝ) :=
    harm _ (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hH)
  have hH4e : (4 : ℝ) / (eps : ℝ) ^ 4 ≤ (H : ℝ) :=
    harm _ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hH)
  have hHexp : Real.exp ((25 : ℝ) ^ 25 * (10 ^ 40 * (1 + 1 / (eps : ℝ) ^ 2) ^ 9)) ≤ (H : ℝ) :=
    harm _ (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hH)
  have hLbig : (25 : ℝ) ^ 25 * (10 ^ 40 * (1 + 1 / (eps : ℝ) ^ 2) ^ 9)
      ≤ Real.log (H : ℝ) := by
    have h1 := Real.log_le_log (Real.exp_pos _) hHexp
    rwa [Real.log_exp] at h1
  exact exitBd_lt_of_arms heps hH4 hHe hH4e hLbig hq1 hq2

/-- **`MinorArcBoundTight 12`, unconditionally** — the S7 analytic obligation at the
frozen exponent, with no hypotheses left. -/
theorem minorArcBoundTight_twelve : MinorArcBoundTight 12 :=
  minorArcBoundTight_twelve_of_close exitClose_twelve

/-- **`BigXiArcTight 12`, unconditionally** — the frozen S7 row itself. -/
theorem bigXiArcTight_twelve : BigXiArcTight 12 :=
  bigXiArcTight_twelve_of_close exitClose_twelve

end Salt.MR
