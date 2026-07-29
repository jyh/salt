/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.Eq26Bridge
import Salt.MR.DoorFrame
import Salt.MR.KernelCarry

/-!
# Eq26Compose — MR Theorem 3 from Step 1 and eq (26): the wave-2 stones

Source: Matomäki–Radziwiłł, arXiv `1501.04585v4`, **pp. 30–31** (Theorem 3's
mean square, eq (26), eq (27), eq (28)).  Design freeze:
`docs/exploration/eq26-freeze-0726.md` with ⟦AMENDMENT A⟧ folded — this file is
**wave 2**, the stones `E26-6`, `E26-7`, `E26-8`.  Wave 1 (`E26-0 … E26-5b`) is
`Salt.MR.Eq26Bridge`.

## The hypothesis-carry discipline

Every stone here carries its upstream as an **explicit binder in the landed
shape**, so the arc composes mechanically and nothing is silently assumed:

* `thm3_of_step1_and_eq26` carries Step 1 (`KernelCarry`'s
  `lemma14_shortInterval_meansq_kernel` :1153) as `hstep1`, with the conclusion's
  left side byte-mirrored and its right side abstracted to a variable `Bstep`;
  `thm3_meansq_of_kernel` is the composition, which is where the abstraction is
  *certified* — it feeds the landed lemma in directly.
* `thm3_chebyshev_exceptional` carries the *previous* stone's conclusion as
  `hthm3` (again with the bound abstracted), so `Bstep`/`B` unify on contact.
* `thm3_pair_exceptional` carries two such — the `f`-instance and the `f ≡ 1`
  instance — and its pointwise output is byte-fit to `Sec9Glue.sec9_eq28_exit`'s
  `hthm3f` (:521) and `hthm3one` (:524).

Lemma 4 (`Sec9Glue.Lemma4Comparison`) remains the arc's one carried external.

## E26-6 — Theorem 3's mean square (`thm3_of_step1_and_eq26`)

Step 1 controls the *two-scale difference* `(1/h₁)S₁ − (1/h₂)S₂` in mean square;
eq (26) replaces the `h₂`-average by the `X`-average **pointwise**, at the cost
of `2^J·C/(log X)^{1/20}` (`Eq26Bridge.eq26`) plus the one-lattice-point window
defect `1/h₂` (`Eq26Bridge.shortSum_eq26_window`).  With `u := (1/h₁)S₁ −
(1/h₂)S₂` and `v := (1/h₂)S₂ − c`,

`‖u + v‖² ≤ 2‖u‖² + 2‖v‖²`,

and the second term is a *constant* in `x`, so it survives `(1/X)∫_X^{2X}`
unchanged.  Hence

`(1/X)∫_X^{2X} ‖(1/h₁)S₁(x) − c‖² dx ≤ 2·Bstep + 2·(2^J·C/(log X)^{1/20} + 1/h₂)²`.

At the K-ladder's pin `J = 2` and with the window defect absorbed at the eq-(26)
scale the second term is `50C²/(log X)^{1/10}` (`thm3_meansq_pinned`) — the
freeze's "`32C²/(log X)^{1/10}`" is `2·(4C/(log X)^{1/20})²`, i.e. the same
number with the `1/h₂` window defect dropped; carrying it honestly costs the
ratio `(5/4)² = 25/16`.  `rpow_inv20_sq` is the squaring and
`one_div_rpow_absorb` the freeze's lossless absorption into `(log X)^{−1/50}`.

**⚠ `h₂` is pinned to `hTwo X` here, not free.**  Eq (26) is a statement about
the window of width exactly `h₂ = X/(log X)^{1/5}` (it saturates Lemma 4's
`y`-range at its lower endpoint), so the composition can only be run at that
`h₂`.  The landed Step-1 binder `h₂ ≤ X(log X)^{−1/5}` is met with EQUALITY
(`Eq26Bridge.hTwo_eq_mul_rpow_neg`).

## ⟦THE `hh1lo` PLACEMENT VERDICT⟧ — it sits in E26-7, not E26-6

⟦AMENDMENT A⟧ left the placement of `hh1lo : 400/δ ≤ h₁` to the executor
("state it where it bites").  It bites in **E26-7**:

* E26-6's window crossing is at the **long** scale `h₂` — the defect it pays is
  `1/h₂`, and `1/h₂ = (log X)^{1/5}/X` is *not* δ-scaled: it is absorbed into the
  eq-(26) error `C/(log X)^{1/20}`, where a lower bound on `h₁` is irrelevant.
* The **short**-scale crossing happens only when the `x`-pointwise conclusion is
  converted from `shortSum`'s half-open `(x, x+h₁]` window to `hthm3f`'s closed
  `[⌈x⌉₊, ⌊x+h₁⌋₊]` window — and that conversion is **post-Chebyshev**, inside
  E26-7.  Its defect is `1/h₁`, which must be beaten against the *target* `δ/100`
  rather than against an error that already tends to `0`; that is exactly what
  `400/δ ≤ h₁` buys (`1/h₁ ≤ δ/400`, and `δ/200 + δ/400 = 3δ/400 ≤ δ/100`).

So `thm3_of_step1_and_eq26` has **no** `h₁` lower bound beyond `1 ≤ h₁` (the
landed Step-1 binder), and `thm3_chebyshev_exceptional` carries `hh1lo`.  Catch
#253's failure mode (at `h₁ = 1` the squared bridge defect is `Θ(1)` against a
vanishing target) is thereby confined to one stone.

## E26-7 — eq (27), the exceptional set (`thm3_chebyshev_exceptional`)

Chebyshev in `MeasureTheory.volume` on `Set.Icc X (2X)` — **not** in a `Finset`:
the landed mean squares are `intervalIntegral`s over `ℝ`, and the exceptional set
is a genuine set of reals.  With `E := {x ∈ [X,2X] : δ/200 < ‖(1/h₁)S₁(x) − c‖}`,
Markov (`MeasureTheory.mul_meas_ge_le_integral_of_nonneg`) gives
`(δ/200)²·|E| ≤ ∫_X^{2X}‖·‖² ≤ X·B`, and off `E` the window conversion lands
`hthm3f`'s shape at `δ/100`.  `thm3_pair_exceptional` unions the `f`-instance
with the `f ≡ 1` instance (whose sums become cardinalities — the
`Finset.sum_const` bridge) and `thm3_pair_nonvacuous` turns the volume bound into
an actual `x`, gated in-statement on `Bf + B1 < (δ/200)²`.

## E26-8 — the `A(h)` instantiation (`Ah`, ★ the corner)

At the landed pin `A = 65536`, `P₁ = 2^A` is an absolute constant, so MR
Theorem 3's error `(log h)^{1/3}/P₁^{1/6−η}` **diverges** on the door road: true
but vacuous.  ⟦AMENDMENT A⟧'s repair makes the anchor grow with `h`,
`A ≈ (δ/8)·log₂ h` and `M := ⌈8/δ⌉`, so that `P₁ ≈ h^{δ/8}` and `Q₁ = 2^{MA} ≤ h`.

The ℕ formulation used here is

`Ah δinv h := Adoor (8·δinv) · (log₂ h / (8·δinv · Adoor (8·δinv)))`

(all divisions ℕ, i.e. floors).  Two design points:

* **Floor, never `+1`.**  `⌈(δ/8)log₂ h⌉` — the freeze's display — *breaks* the
  containment: `Q₁ = 2^{M·A} ≤ h` needs `M·A ≤ log₂ h`, which the ceiling (and
  the `+1` of the freeze's ℕ sketch) violates.  Floor division gives
  `M·A ≤ log₂ h` by construction, and `Ah_one_sided` records the matching lower
  bound `h < 2^{M(A + Adoor M)}`, so nothing is lost but a bounded, `h`-free
  factor.
* **A multiple of `Adoor M`.**  Taking the anchor to be `Adoor M · k` rather than
  a bare quotient is what lets `calFrameK_satisfiable_Ah` *reuse* `DoorFrame`'s
  gate estimate: `calE (Adoor M · k) G 2 = k · calE (Adoor M) G 2`, so
  `A_gate_logK`'s left side gains exactly `16 log k` while its right side gains
  the factor `k` — and `log k ≤ k − 1` closes it.  The frame's floor hypothesis
  is then `8·δinv·Adoor (8·δinv) ≤ log₂ h`, which is precisely ⟦AMENDMENT A⟧'s
  corrected level-1 containment arm `H_K` (`DoorFrame.log_calQK_door_one`).

Margin hygiene: `δ` enters only through the ℕ parameter `δinv` (a stand-in for
`⌈1/δ⌉`); no numeral in this file is a function of `δ₀`, and the ⟦V9c⟧ law is
kept — `calP`/`calQK` are never evaluated.

⟦ZENO residuals of this file⟧ Lemma 4 (`Lemma4Comparison`, carried);
`hMsup`/Proposition 1 (carried through `hstep1`); the `δinv ≈ 1/δ` link between
`Ah`'s ℕ parameter and the real `δ` of `eq28_clears_of_M` (a call-site
instantiation, deliberately not fixed here — MARGIN-HYGIENE).
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §0 — plumbing: the public measurability/integrability exports

`Lemma14.shortSum_measurable` is `private` and the only public integrability
export there (`shortSum_diff_sq_intervalIntegrable`) covers the **two-scale
difference** only.  E26-6 needs `‖(1/h₁)S₁ − c‖²`, a different integrand, so the
two private helpers are re-proved here rather than de-privatised (⟦AMENDMENT A⟧:
"do NOT de-private the landed line"). -/

/-- **`x ↦ Sⱼ(x)` is measurable, publicly.**  Same proof as the landed private
`Lemma14.shortSum_measurable`: the window `{x | x < m ≤ x + h}` is the interval
`[m − h, m)`, so `Sⱼ` is a finite sum of weighted indicators. -/
theorem shortSum_measurable' (a : ℕ → ℂ) (s0 : Finset ℕ) (h : ℝ) :
    Measurable (fun x : ℝ => shortSum a s0 x h) := by
  have hset : ∀ m : ℕ, {x : ℝ | x < (m : ℝ) ∧ (m : ℝ) ≤ x + h}
      = Set.Ico ((m : ℝ) - h) (m : ℝ) := by
    intro m
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  simp only [shortSum, Finset.sum_filter]
  refine Finset.measurable_sum _ (fun m _ => ?_)
  exact Measurable.ite (by rw [hset m]; exact measurableSet_Ico) measurable_const
    measurable_const

/-- The trivial uniform bound `‖Sⱼ(x)‖ ≤ ∑_{m ∈ s0} ‖aₘ‖` (the landed copy is
private). -/
private lemma shortSum_norm_le' (a : ℕ → ℂ) (s0 : Finset ℕ) (x h : ℝ) :
    ‖shortSum a s0 x h‖ ≤ ∑ m ∈ s0, ‖a m‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun m _ _ => norm_nonneg _)

/-- A bounded measurable real function is interval-integrable (the landed copy is
private). -/
private lemma bounded_meas_intervalIntegrable {g : ℝ → ℝ} {C : ℝ} (p q : ℝ)
    (hm : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) : IntervalIntegrable g volume p q :=
  ⟨MeasureTheory.Integrable.mono'
      (_root_.intervalIntegrable_const (μ := volume) (c := C) (a := p) (b := q)).1
      hm.aestronglyMeasurable (Filter.Eventually.of_forall hb),
   MeasureTheory.Integrable.mono'
      (_root_.intervalIntegrable_const (μ := volume) (c := C) (a := p) (b := q)).2
      hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)⟩

/-- **The `X`-average side condition.**  `‖(1/h)Sⱼ(x) − c‖²` is interval-integrable
on every interval, for every constant comparand `c` — the integrand Theorem 3's
mean square actually carries, as against the two-scale difference the landed
`shortSum_diff_sq_intervalIntegrable` covers. -/
theorem shortSum_sub_const_sq_intervalIntegrable (a : ℕ → ℂ) (s0 : Finset ℕ) {h : ℝ}
    (hh : 0 < h) (c : ℂ) (p q : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => ‖((1 / h : ℝ) : ℂ) * shortSum a s0 x h - c‖ ^ 2) volume p q := by
  have hm : Measurable (fun x : ℝ => ‖((1 / h : ℝ) : ℂ) * shortSum a s0 x h - c‖ ^ 2) :=
    ((((shortSum_measurable' a s0 h).const_mul _).sub measurable_const).norm).pow_const 2
  refine bounded_meas_intervalIntegrable (C := (1 / h * ∑ m ∈ s0, ‖a m‖ + ‖c‖) ^ 2) p q hm
    (fun x => ?_)
  have hc1 : ‖((1 / h : ℝ) : ℂ)‖ = 1 / h := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / h)]
  have hd : ‖((1 / h : ℝ) : ℂ) * shortSum a s0 x h - c‖
      ≤ 1 / h * ∑ m ∈ s0, ‖a m‖ + ‖c‖ := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, hc1]
    have hb := mul_le_mul_of_nonneg_left (shortSum_norm_le' a s0 x h)
      (by positivity : (0 : ℝ) ≤ 1 / h)
    linarith
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hd 2

/-- **The second `ℂ`↔`ℝ` crossing of the arc** (⟦AMENDMENT A⟧'s `+60–100`).
`KernelCarry` runs at `a : ℕ → ℂ`, eq (26) at `f : ℕ → ℝ`; the composition uses
`a := ↑f`, and every real conclusion is read off through this one identity. -/
private lemma norm_ofReal_two_sums (c₁ c₂ : ℝ) (s t : Finset ℕ) (f : ℕ → ℝ) :
    ‖((c₁ : ℝ) : ℂ) * ∑ n ∈ s, ((f n : ℝ) : ℂ)
        - ((c₂ : ℝ) : ℂ) * ∑ n ∈ t, ((f n : ℝ) : ℂ)‖
      = |c₁ * ∑ n ∈ s, f n - c₂ * ∑ n ∈ t, f n| := by
  have h : ((c₁ : ℝ) : ℂ) * ∑ n ∈ s, ((f n : ℝ) : ℂ)
      - ((c₂ : ℝ) : ℂ) * ∑ n ∈ t, ((f n : ℝ) : ℂ)
      = ((c₁ * ∑ n ∈ s, f n - c₂ * ∑ n ∈ t, f n : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-- **The squaring** `((log X)^{1/20})² = (log X)^{1/10}` — eq (26)'s error enters
Theorem 3's mean square squared. -/
theorem rpow_inv20_sq {L : ℝ} (hL : 0 ≤ L) :
    (L ^ ((1 : ℝ) / 20)) ^ 2 = L ^ ((1 : ℝ) / 10) := by
  rw [← Real.rpow_natCast (L ^ ((1 : ℝ) / 20)) 2, ← Real.rpow_mul hL]
  norm_num

/-- **The freeze's absorption, lossless**: `(log X)^{−1/10} ≤ (log X)^{−1/50}` as
soon as `log X ≥ 1`.  Theorem 1's budget is `(log X)^{−1/50}`, so squaring
eq (26)'s `−1/20` costs nothing. -/
theorem one_div_rpow_absorb {L : ℝ} (hL : 1 ≤ L) :
    1 / L ^ ((1 : ℝ) / 10) ≤ 1 / L ^ ((1 : ℝ) / 50) := by
  have hpos : (0 : ℝ) < L ^ ((1 : ℝ) / 50) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hL) _
  exact one_div_le_one_div_of_le hpos (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))

/-! ## §1 — E26-6: Theorem 3's mean square from Step 1 and eq (26) -/

/-- **The analytic core of E26-6**, stated at an abstract comparand `c`: if the
`h₂`-average is uniformly within `D` of `c` on `[X, 2X]`, then the two-scale mean
square upgrades to a mean square against `c`, at the cost `(a+b)² ≤ 2a² + 2b²`.

The `D`-term is a *constant* in `x`, so `(1/X)∫_X^{2X}` returns it unchanged —
this is the whole reason eq (26) may be pointwise while Step 1 is `L²`. -/
theorem meansq_shift_of_pointwise (a : ℕ → ℂ) (s0 : Finset ℕ) (c : ℂ)
    {X h₁ h₂ Bstep D : ℝ} (hX0 : 0 < X) (hh1 : 0 < h₁) (hh2 : 0 < h₂)
    (hpt : ∀ x ∈ Set.Icc X (2 * X),
      ‖((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂ - c‖ ≤ D)
    (hstep1 : 1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2) ≤ Bstep) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁ - c‖ ^ 2)
      ≤ 2 * Bstep + 2 * D ^ 2 := by
  have hXle : X ≤ 2 * X := by linarith
  have hI1 : IntervalIntegrable
      (fun x : ℝ => ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁ - c‖ ^ 2) volume X (2 * X) :=
    shortSum_sub_const_sq_intervalIntegrable a s0 hh1 c X (2 * X)
  have hI2 : IntervalIntegrable (fun x : ℝ => ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
      - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2) volume X (2 * X) :=
    shortSum_diff_sq_intervalIntegrable a s0 hh1 hh2 X (2 * X)
  have hIR : IntervalIntegrable (fun x : ℝ => 2 * ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
      - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2 + 2 * D ^ 2) volume X (2 * X) :=
    (hI2.const_mul 2).add _root_.intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hXle hI1 hIR (fun x hx => ?_)
  · have heval : (∫ x in X..(2 * X), (2 * ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
          - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2 + 2 * D ^ 2))
        = 2 * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2) + (2 * X - X) * (2 * D ^ 2) := by
      rw [intervalIntegral.integral_add (hI2.const_mul 2) _root_.intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    rw [heval] at hmono
    have hscale := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / X)
    have hring : 1 / X * (2 * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
          - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2) + (2 * X - X) * (2 * D ^ 2))
        = 2 * (1 / X * (∫ x in X..(2 * X), ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖ ^ 2)) + 2 * D ^ 2 := by
      field_simp
      ring
    rw [hring] at hscale
    linarith
  · -- the pointwise `(a+b)² ≤ 2a² + 2b²`
    have hv := hpt x hx
    have hsplit : ((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁ - c
        = (((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂)
          + (((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂ - c) := by ring
    have htri : ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁ - c‖
        ≤ ‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
            - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖
          + ‖((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂ - c‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hv2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
    nlinarith [sq_nonneg (‖((1 / h₁ : ℝ) : ℂ) * shortSum a s0 x h₁
        - ((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂‖
      - ‖((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂ - c‖),
      norm_nonneg (((1 / h₂ : ℝ) : ℂ) * shortSum a s0 x h₂ - c)]

/-- **E26-6 — MR Theorem 3's mean square** (p. 30), from Step 1 and eq (26).

`hstep1` is `KernelCarry.lemma14_shortInterval_meansq_kernel`'s conclusion
(:1163–:1172) with its left side byte-mirrored at `a := ↑f`, `s0 := [⌈X⌉₊,⌊4X⌋₊]∩S`,
`h₂ := hTwo X`, and its right side abstracted to `Bstep`; `hL4` is the `2^J`-row
Lemma-4 family eq (26) consumes.  The conclusion replaces the `h₂`-average by the
`X`-average:

`(1/X)∫_X^{2X} ‖(1/h₁)S₁(x) − (1/X)∑_{X≤n≤2X, n∈S} f(n)‖² dx`
`  ≤ 2·Bstep + 2·(2^J·C/(log X)^{1/20} + 1/h₂)²`.

The `1/h₂` is the one-lattice-point window defect of `shortSum_eq26_window`
(E26-5a) — the honest price of crossing from `shortSum`'s half-open window to
eq (26)'s closed one, paid once, at the LONG scale.  No `h₁` lower bound is
needed here; see ⟦THE `hh1lo` PLACEMENT VERDICT⟧ in the module docstring. -/
theorem thm3_of_step1_and_eq26 (Pseq Qseq : ℕ → ℕ) (J : ℕ) (f : ℕ → ℝ)
    {X C h₁ Bstep : ℝ} (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ hTwo X)
    (ha : ∀ m ∈ (Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n),
      ‖((f m : ℝ) : ℂ)‖ ≤ 1)
    (hL4 : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset,
      Lemma4Comparison (fun n => gJR 𝒥 Pseq Qseq n * f n) X C)
    (hstep1 : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x h₁
          - ((1 / hTwo X : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x
                (hTwo X)‖ ^ 2)
      ≤ Bstep) :
    1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x h₁
          - ((1 / X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
              (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)‖ ^ 2)
      ≤ 2 * Bstep + 2 * (2 ^ J * (C / Real.log X ^ ((1 : ℝ) / 20)) + 1 / hTwo X) ^ 2 := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hh10 : (0 : ℝ) < h₁ := lt_of_lt_of_le zero_lt_one hh1
  have hT0 : (0 : ℝ) < hTwo X := hTwo_pos hX
  have hT1 : (1 : ℝ) ≤ hTwo X := le_trans hh1 hh12
  refine meansq_shift_of_pointwise _ _ _ hX0 hh10 hT0 (fun x hx => ?_) hstep1
  rw [Set.mem_Icc] at hx
  have hwin := shortSum_eq26_window (fun n => ((f n : ℝ) : ℂ)) Pseq Qseq J hX hx.1 hx.2
    hT1 le_rfl ha
  have h26 := eq26 Pseq Qseq J f hX hx.1 hx.2 hL4
  have hmid : ‖((1 / hTwo X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + hTwo X⌋₊).filter
        (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)
      - ((1 / X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
        (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)‖
      ≤ 2 ^ J * (C / Real.log X ^ ((1 : ℝ) / 20)) := by
    rw [norm_ofReal_two_sums]
    exact h26
  have hsplit : ((1 / hTwo X : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
        ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x (hTwo X)
      - ((1 / X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
          (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)
      = (((1 / hTwo X : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
            ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x (hTwo X)
          - ((1 / hTwo X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + hTwo X⌋₊).filter
              (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ))
        + (((1 / hTwo X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + hTwo X⌋₊).filter
              (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)
            - ((1 / X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
              (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  linarith [hwin, hmid]

/-- **E26-6 at the K-ladder's pin `Jb = 2`**, with the window defect absorbed at
eq (26)'s own scale (`hdef`, an `X`-largeness binder — `1/h₂ = (log X)^{1/5}/X`
against `C/(log X)^{1/20}`).  Then `2·(4C + C)²/(log X)^{1/10}`, i.e.

`(1/X)∫_X^{2X} ‖(1/h₁)S₁ − (1/X)∑_{X≤n≤2X, n∈S} f‖² ≤ 2·Bstep + 50C²/(log X)^{1/10}`.

The freeze's `32C²/(log X)^{1/10}` is `2·(4C)²`, the same number with the `1/h₂`
window defect **dropped**; carrying it honestly costs exactly `(5/4)² = 25/16`.
`one_div_rpow_absorb` then puts this inside Theorem 1's `(log X)^{−1/50}`
budget. -/
theorem thm3_meansq_pinned (Pseq Qseq : ℕ → ℕ) (f : ℕ → ℝ)
    {X C h₁ Bstep : ℝ} (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ hTwo X)
    (hC : 0 ≤ C) (hdef : 1 / hTwo X ≤ C / Real.log X ^ ((1 : ℝ) / 20))
    (ha : ∀ m ∈ (Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq 2 n),
      ‖((f m : ℝ) : ℂ)‖ ≤ 1)
    (hL4 : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      Lemma4Comparison (fun n => gJR 𝒥 Pseq Qseq n * f n) X C)
    (hstep1 : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq 2 n)) x h₁
          - ((1 / hTwo X : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq 2 n)) x
                (hTwo X)‖ ^ 2)
      ≤ Bstep) :
    1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq 2 n)) x h₁
          - ((1 / X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
              (fun n => MemS Pseq Qseq 2 n), ((f n : ℝ) : ℂ)‖ ^ 2)
      ≤ 2 * Bstep + 50 * (C ^ 2 / Real.log X ^ ((1 : ℝ) / 10)) := by
  refine le_trans (thm3_of_step1_and_eq26 Pseq Qseq 2 f hX hh1 hh12 ha hL4 hstep1) ?_
  have hLnn : (0 : ℝ) ≤ Real.log X := le_trans zero_le_one (one_le_log_of_exp_le hX)
  have hLpos : (0 : ℝ) < Real.log X ^ ((1 : ℝ) / 20) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (one_le_log_of_exp_le hX)) _
  have hT0 : (0 : ℝ) < hTwo X := hTwo_pos hX
  have ht0 : (0 : ℝ) ≤ C / Real.log X ^ ((1 : ℝ) / 20) := div_nonneg hC hLpos.le
  have hd0 : (0 : ℝ) ≤ 1 / hTwo X := div_nonneg zero_le_one hT0.le
  have hle : (2 : ℝ) ^ (2 : ℕ) * (C / Real.log X ^ ((1 : ℝ) / 20)) + 1 / hTwo X
      ≤ 5 * (C / Real.log X ^ ((1 : ℝ) / 20)) := by
    have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
    rw [h4]
    linarith
  have key : ((2 : ℝ) ^ (2 : ℕ) * (C / Real.log X ^ ((1 : ℝ) / 20)) + 1 / hTwo X) ^ 2
      ≤ 25 * (C ^ 2 / Real.log X ^ ((1 : ℝ) / 10)) := by
    calc ((2 : ℝ) ^ (2 : ℕ) * (C / Real.log X ^ ((1 : ℝ) / 20)) + 1 / hTwo X) ^ 2
        ≤ (5 * (C / Real.log X ^ ((1 : ℝ) / 20))) ^ 2 := by
          refine pow_le_pow_left₀ ?_ hle 2
          have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 : ℕ) * (C / Real.log X ^ ((1 : ℝ) / 20)) :=
            mul_nonneg (by norm_num) ht0
          linarith
      _ = 25 * (C ^ 2 / Real.log X ^ ((1 : ℝ) / 10)) := by
          rw [mul_pow, div_pow, rpow_inv20_sq hLnn]
          norm_num
  linarith

/-! ### The two residual obligations of the Step-1 composition

`thm3_of_step1_and_eq26`'s `hstep1` binder is
`KernelCarry.lemma14_shortInterval_meansq_kernel`'s conclusion (:1163) with the
left side byte-mirrored at `a := ↑f`, `s0 := [⌈X⌉₊,⌊4X⌋₊] ∩ 𝒮`, `h₂ := hTwo X`.
Feeding the landed lemma in therefore leaves exactly two side conditions that are
not already binders of E26-6; both are discharged here, once and for all. -/

/-- **Obligation 1** — the landed Step-1 binder `h₂ ≤ X(log X)^{−1/5}`
(`KernelCarry` :1156) at `h₂ := hTwo X`: it holds with EQUALITY, `hTwo` being that
number in quotient form (`Eq26Bridge.hTwo_eq_mul_rpow_neg`). -/
theorem hTwo_meets_kernel_binder {X : ℝ} (hX : Real.exp 1 ≤ X) :
    hTwo X ≤ X * Real.log X ^ (-(1 / 5 : ℝ)) :=
  le_of_eq (hTwo_eq_mul_rpow_neg (le_trans zero_le_one (one_le_log_of_exp_le hX)))

/-- **Obligation 2** — the landed Step-1 binder `hrange` (`KernelCarry` :1159) at
the eq-(26) carrier: `[⌈X⌉₊, ⌊4X⌋₊] ∩ 𝒮` lies in `[X, 4X]` by construction, so the
carrier the window bridge needs is exactly the carrier the kernel accepts. -/
theorem eq26_carrier_hrange (Pseq Qseq : ℕ → ℕ) (J : ℕ) {X : ℝ} (hX0 : 0 ≤ X) :
    ∀ m ∈ (Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n),
      X ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * X := by
  intro m hm
  rw [Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨hlo, hhi⟩, _⟩ := hm
  constructor
  · exact le_trans (Nat.le_ceil X) (by exact_mod_cast hlo)
  · exact le_trans (by exact_mod_cast hhi) (Nat.floor_le (by linarith))

/-- **THE COMPOSITION, CERTIFIED.**  E26-6 fed by the landed Step 1 itself:
`KernelCarry.lemma14_shortInterval_meansq_kernel` (:1153) at `a := ↑f`,
`s0 := [⌈X⌉₊,⌊4X⌋₊] ∩ 𝒮`, `h₂ := hTwo X`, with its two extra side conditions
discharged by `hTwo_meets_kernel_binder` and `eq26_carrier_hrange`.

No new mathematics — the point is that `thm3_of_step1_and_eq26`'s `hstep1` binder
is EXACTLY the landed conclusion, so this is one `exact`.  Everything the arc
still owes is visible in the binders: `hL4` (Lemma 4, the carried external) and
`hMsup` (Proposition 1's supply, the freeze's "E26-6's real blocker"). -/
theorem thm3_meansq_of_kernel (Pseq Qseq : ℕ → ℕ) (J : ℕ) (f : ℕ → ℝ)
    {X C h₁ Msup δ : ℝ} (N : ℕ)
    (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh12 : h₁ ≤ hTwo X)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : ∀ m ∈ (Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n),
      ‖((f m : ℝ) : ℂ)‖ ≤ 1)
    (hL4 : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset,
      Lemma4Comparison (fun n => gJR 𝒥 Pseq Qseq n * f n) X C)
    (hMsup : ∀ T : ℝ, X / h₁ ≤ T →
      X / h₁ / T * ((∫ t in T..(2 * T), ‖dpolyA (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) t‖ ^ 2)
          + ∫ t in (-(2 * T))..(-T), ‖dpolyA (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) t‖ ^ 2)
        ≤ Msup) :
    1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x h₁
          - ((1 / X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
              (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)‖ ^ 2)
      ≤ 2 * (1 / (2 * Real.pi ^ 2) * ((2000 + 944640 * Real.pi)
            * ((Real.log X) ^ (-(14 / 45 : ℝ))
              + ((∫ t in ((Real.log X) ^ (1 / 45 : ℝ))..(X / h₁),
                    ‖dpolyA (fun n => ((f n : ℝ) : ℂ))
                      ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter
                        (fun n => MemS Pseq Qseq J n)) t‖ ^ 2)
                  + ∫ t in (-(X / h₁))..(-((Real.log X) ^ (1 / 45 : ℝ))),
                    ‖dpolyA (fun n => ((f n : ℝ) : ℂ))
                      ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter
                        (fun n => MemS Pseq Qseq J n)) t‖ ^ 2)
              + Msup)
          + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ N * (X / h₁))) ^ 2
            + 1152 * (12 * h₁ / (2 ^ N * δ)
                + (8 * h₁ / 2 ^ N) * (1 + Real.log (3 * X))) ^ 2)))
        + 2 * (2 ^ J * (C / Real.log X ^ ((1 : ℝ) / 20)) + 1 / hTwo X) ^ 2 := by
  refine thm3_of_step1_and_eq26 Pseq Qseq J f hX hh1 hh12 ha hL4 ?_
  exact lemma14_shortInterval_meansq_kernel (fun n => ((f n : ℝ) : ℂ)) _ N hX hh1 hh12
    (hTwo_meets_kernel_binder hX) hδ0 hδ1 ha
    (eq26_carrier_hrange Pseq Qseq J (le_of_lt (lt_of_lt_of_le (Real.exp_pos 1) hX)))
    hMsup

/-! ## §2 — E26-7: eq (27), the exceptional set

MR state eq (27) as a count; the honest deliverable (⟦AMENDMENT A⟧) is the
**exceptional-set form**, because the objects the kernel produces are
`intervalIntegral`s over `ℝ` and the set of bad `x` is a set of reals.  Chebyshev
therefore runs in `MeasureTheory.volume` on `Set.Icc X (2X)` — never in a
`Finset`. -/

/-- **Chebyshev/Markov on `[X, 2X]`, in `volume`.**  From a mean-square bound
`(1/X)∫_X^{2X}‖F‖² ≤ B` and a threshold `ε > 0`: the set where `‖F‖` exceeds `ε`
has volume at most `X·B/ε²`, and off it `‖F‖ ≤ ε` pointwise.

The single lattice endpoint `x = X` (the `Icc`/`Ioc` mismatch between the set and
the interval integral) is absorbed by `measure_singleton`; nothing else is
lost. -/
theorem chebyshev_exceptional_set (F : ℝ → ℂ) {X B ε : ℝ} (hF : Measurable F)
    (hX0 : 0 < X) (hε : 0 < ε)
    (hint : IntervalIntegrable (fun x : ℝ => ‖F x‖ ^ 2) volume X (2 * X))
    (hmean : 1 / X * (∫ x in X..(2 * X), ‖F x‖ ^ 2) ≤ B) :
    ∃ E : Set ℝ, E ⊆ Set.Icc X (2 * X) ∧ MeasurableSet E
      ∧ volume E ≤ ENNReal.ofReal (X * B / ε ^ 2)
      ∧ ∀ x ∈ Set.Icc X (2 * X) \ E, ‖F x‖ ≤ ε := by
  have hXle : X ≤ 2 * X := by linarith
  have hSm : MeasurableSet {x : ℝ | ε ^ 2 ≤ ‖F x‖ ^ 2} :=
    measurableSet_le measurable_const ((hF.norm).pow_const 2)
  have hfin : volume ({x : ℝ | ε ^ 2 ≤ ‖F x‖ ^ 2} ∩ Set.Ioc X (2 * X)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  -- Markov, on the restricted measure the interval integral is taken against
  have hMarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := volume.restrict (Set.Ioc X (2 * X))) (f := fun x : ℝ => ‖F x‖ ^ 2)
    (Filter.Eventually.of_forall (fun x => by positivity)) hint.1 (ε ^ 2)
  rw [MeasureTheory.measureReal_def, Measure.restrict_apply hSm,
    ← intervalIntegral.integral_of_le hXle] at hMarkov
  have hIle : (∫ x in X..(2 * X), ‖F x‖ ^ 2) ≤ X * B := by
    have h := mul_le_mul_of_nonneg_left hmean hX0.le
    rwa [show X * (1 / X * (∫ x in X..(2 * X), ‖F x‖ ^ 2))
      = ∫ x in X..(2 * X), ‖F x‖ ^ 2 by field_simp] at h
  have hreal : (volume ({x : ℝ | ε ^ 2 ≤ ‖F x‖ ^ 2} ∩ Set.Ioc X (2 * X))).toReal
      ≤ X * B / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)]
    have := hMarkov.trans hIle
    linarith
  refine ⟨{x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε < ‖F x‖}, fun x hx => hx.1, ?_, ?_, ?_⟩
  · exact measurableSet_Icc.inter ((hF.norm) measurableSet_Ioi)
  · have hsub : {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε < ‖F x‖}
        ⊆ {X} ∪ ({x : ℝ | ε ^ 2 ≤ ‖F x‖ ^ 2} ∩ Set.Ioc X (2 * X)) := by
      intro x hx
      obtain ⟨hxI, hxe⟩ := hx
      rw [Set.mem_Icc] at hxI
      rcases eq_or_lt_of_le hxI.1 with h | h
      · exact Or.inl h.symm
      · refine Or.inr ⟨?_, ⟨h, hxI.2⟩⟩
        have hsq : ε ^ 2 < ‖F x‖ ^ 2 := by nlinarith [norm_nonneg (F x)]
        exact hsq.le
    calc volume {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε < ‖F x‖}
        ≤ volume ({X} ∪ ({x : ℝ | ε ^ 2 ≤ ‖F x‖ ^ 2} ∩ Set.Ioc X (2 * X))) :=
          measure_mono hsub
      _ ≤ volume {X} + volume ({x : ℝ | ε ^ 2 ≤ ‖F x‖ ^ 2} ∩ Set.Ioc X (2 * X)) :=
          measure_union_le _ _
      _ = volume ({x : ℝ | ε ^ 2 ≤ ‖F x‖ ^ 2} ∩ Set.Ioc X (2 * X)) := by
          rw [measure_singleton, zero_add]
      _ = ENNReal.ofReal
            (volume ({x : ℝ | ε ^ 2 ≤ ‖F x‖ ^ 2} ∩ Set.Ioc X (2 * X))).toReal :=
          (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal (X * B / ε ^ 2) := ENNReal.ofReal_le_ofReal hreal
  · intro x hx
    have hnot : x ∉ {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε < ‖F x‖} := hx.2
    by_contra hc
    exact hnot ⟨hx.1, lt_of_not_ge hc⟩

/-- The triangle step that converts a bound against the `shortSum` object into a
bound against the closed-window sum: `‖B − c‖ ≤ ‖A − B‖ + ‖A − c‖`. -/
private lemma norm_sub_of_pivot (A Bc c : ℂ) {r s : ℝ} (h1 : ‖A - Bc‖ ≤ r)
    (h2 : ‖A - c‖ ≤ s) : ‖Bc - c‖ ≤ r + s := by
  have hsp : Bc - c = -(A - Bc) + (A - c) := by ring
  rw [hsp]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_neg]
  linarith

/-- **E26-7 — eq (27) in its exceptional-set form.**  From E26-6's mean square
(carried as `hthm3`, its bound abstracted to `B`), Chebyshev at the threshold
`δ/200` produces a set `E ⊆ [X, 2X]` of volume `≤ X·B/(δ/200)²` off which the
**closed-window** comparison of MR Theorem 3 holds at `δ/100` — i.e. exactly
`Sec9Glue.sec9_eq28_exit`'s `hthm3f` (:521) at `Nsh := [⌈x⌉₊, ⌊x+h₁⌋₊]`,
`Nlg := [⌈X⌉₊, ⌊2X⌋₊]`, `h := h₁`.

⟦THE `hh1lo` BITE⟧  The step from the `shortSum` bound to the closed-window bound
is `Eq26Bridge.shortSum_eq26_window` at the SHORT scale, and it costs `1/h₁`.
That is the only place an `h₁`-floor is needed on the whole arc, and it is needed
against the *target* `δ/100` rather than against a vanishing error — hence
`hh1lo : 400/δ ≤ h₁`, giving `1/h₁ ≤ δ/400` and `δ/200 + δ/400 = 3δ/400 ≤ δ/100`.
(Catch #253: at `h₁ = 1` this defect is `Θ(1)` and Theorem 3 is false as stated.)
On the door road `h ≍ log X` the binder is discharged at any fixed `δ`. -/
theorem thm3_chebyshev_exceptional (Pseq Qseq : ℕ → ℕ) (J : ℕ) (f : ℕ → ℝ)
    {X h₁ δ B : ℝ} (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh1T : h₁ ≤ hTwo X)
    (hδ : 0 < δ) (hh1lo : 400 / δ ≤ h₁)
    (ha : ∀ m ∈ (Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n),
      ‖((f m : ℝ) : ℂ)‖ ≤ 1)
    (hthm3 : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x h₁
          - ((1 / X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
              (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)‖ ^ 2)
      ≤ B) :
    ∃ E : Set ℝ, E ⊆ Set.Icc X (2 * X) ∧ MeasurableSet E
      ∧ volume E ≤ ENNReal.ofReal (X * B / (δ / 200) ^ 2)
      ∧ ∀ x ∈ Set.Icc X (2 * X) \ E,
          |1 / h₁ * ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + h₁⌋₊).filter
                (fun n => MemS Pseq Qseq J n), f n
            - 1 / X * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
                (fun n => MemS Pseq Qseq J n), f n| ≤ δ / 100 := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hh10 : (0 : ℝ) < h₁ := lt_of_lt_of_le zero_lt_one hh1
  have h400 : (400 : ℝ) ≤ h₁ * δ := by
    have h := (div_le_iff₀ hδ).mp hh1lo
    linarith
  have hinv : 1 / h₁ ≤ δ / 400 := by
    rw [div_le_div_iff₀ hh10 (by norm_num : (0 : ℝ) < 400)]
    linarith
  have hFm : Measurable (fun x : ℝ =>
      ((1 / h₁ : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
          ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x h₁
        - ((1 / X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
            (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)) :=
    ((shortSum_measurable' _ _ h₁).const_mul _).sub measurable_const
  have hint := shortSum_sub_const_sq_intervalIntegrable (fun n => ((f n : ℝ) : ℂ))
    ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) hh10
    (((1 / X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
      (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)) X (2 * X)
  obtain ⟨E, hEsub, hEm, hEvol, hEpt⟩ :=
    chebyshev_exceptional_set _ hFm hX0 (by linarith : (0 : ℝ) < δ / 200) hint hthm3
  refine ⟨E, hEsub, hEm, hEvol, fun x hx => ?_⟩
  have hxI := hx.1
  rw [Set.mem_Icc] at hxI
  have hwin := shortSum_eq26_window (fun n => ((f n : ℝ) : ℂ)) Pseq Qseq J hX hxI.1 hxI.2
    hh1 hh1T ha
  have hkey := norm_sub_of_pivot _ _ _ hwin (hEpt x hx)
  rw [← norm_ofReal_two_sums (1 / h₁) (1 / X) _ _ f]
  linarith [hkey, hinv]

/-- **E26-7's pair form** — the `f`-instance and the `f ≡ 1` instance, unioned.
`Sec9Glue.sec9_eq28_exit` needs BOTH `hthm3f` (:521) and `hthm3one` (:524) at the
SAME `x`; each is a full Theorem-3 chain, so each carries its own mean-square
hypothesis (⟦AMENDMENT A⟧: "its Step-1 supply is a second CARRIED hypothesis"),
and the exceptional sets are unioned.  The `f ≡ 1` instance's Lemma-4 rows are
free — `eq26` is uniform in `f` — and its sums collapse to cardinalities by
`Finset.sum_const`, which is `hthm3one`'s shape exactly. -/
theorem thm3_pair_exceptional (Pseq Qseq : ℕ → ℕ) (J : ℕ) (f : ℕ → ℝ)
    {X h₁ δ Bf B1 : ℝ} (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh1T : h₁ ≤ hTwo X)
    (hδ : 0 < δ) (hh1lo : 400 / δ ≤ h₁)
    (ha : ∀ m ∈ (Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n),
      ‖((f m : ℝ) : ℂ)‖ ≤ 1)
    (hthm3f : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x h₁
          - ((1 / X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
              (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)‖ ^ 2)
      ≤ Bf)
    (hthm3one : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * shortSum (fun _ => ((1 : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x h₁
          - ((1 / X : ℝ) : ℂ) * ∑ _n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
              (fun n => MemS Pseq Qseq J n), ((1 : ℝ) : ℂ)‖ ^ 2)
      ≤ B1) :
    ∃ E : Set ℝ, E ⊆ Set.Icc X (2 * X) ∧ MeasurableSet E
      ∧ volume E ≤ ENNReal.ofReal (X * Bf / (δ / 200) ^ 2)
          + ENNReal.ofReal (X * B1 / (δ / 200) ^ 2)
      ∧ ∀ x ∈ Set.Icc X (2 * X) \ E,
          |1 / h₁ * ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + h₁⌋₊).filter
                (fun n => MemS Pseq Qseq J n), f n
            - 1 / X * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
                (fun n => MemS Pseq Qseq J n), f n| ≤ δ / 100
          ∧ |1 / h₁ * (((Finset.Icc ⌈x⌉₊ ⌊x + h₁⌋₊).filter
                (fun n => MemS Pseq Qseq J n)).card : ℝ)
              - 1 / X * (((Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
                (fun n => MemS Pseq Qseq J n)).card : ℝ)| ≤ δ / 100 := by
  obtain ⟨Ef, hEfsub, hEfm, hEfvol, hEfpt⟩ :=
    thm3_chebyshev_exceptional Pseq Qseq J f hX hh1 hh1T hδ hh1lo ha hthm3f
  obtain ⟨E1, hE1sub, hE1m, hE1vol, hE1pt⟩ :=
    thm3_chebyshev_exceptional Pseq Qseq J (fun _ => (1 : ℝ)) hX hh1 hh1T hδ hh1lo
      (fun m _ => by norm_num) hthm3one
  refine ⟨Ef ∪ E1, Set.union_subset hEfsub hE1sub, hEfm.union hE1m,
    le_trans (measure_union_le _ _) (add_le_add hEfvol hE1vol), fun x hx => ?_⟩
  have hxf : x ∈ Set.Icc X (2 * X) \ Ef := ⟨hx.1, fun hc => hx.2 (Or.inl hc)⟩
  have hx1 : x ∈ Set.Icc X (2 * X) \ E1 := ⟨hx.1, fun hc => hx.2 (Or.inr hc)⟩
  refine ⟨hEfpt x hxf, ?_⟩
  have h1 := hE1pt x hx1
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using h1

/-- **E26-7's non-vacuity count.**  The exceptional set misses a point of
`[X, 2X]` as soon as the two mean squares are below the Chebyshev threshold —
the gate is stated IN the statement, `Bf + B1 < (δ/200)²`, i.e. `(δ/100)²/4`.
(`volume [X,2X] = X`, and the union bound is `X(Bf+B1)/(δ/200)²`.)

This is the step that turns Theorem 3 from an `L²` statement into the pointwise
input `sec9_eq28_exit` consumes: a single `x ∈ [X, 2X]` at which BOTH `hthm3f` and
`hthm3one` hold. -/
theorem thm3_pair_nonvacuous (Pseq Qseq : ℕ → ℕ) (J : ℕ) (f : ℕ → ℝ)
    {X h₁ δ Bf B1 : ℝ} (hX : Real.exp 1 ≤ X) (hh1 : 1 ≤ h₁) (hh1T : h₁ ≤ hTwo X)
    (hδ : 0 < δ) (hh1lo : 400 / δ ≤ h₁) (hBf : 0 ≤ Bf) (hB1 : 0 ≤ B1)
    (hgate : Bf + B1 < (δ / 200) ^ 2)
    (ha : ∀ m ∈ (Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n),
      ‖((f m : ℝ) : ℂ)‖ ≤ 1)
    (hthm3f : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * shortSum (fun n => ((f n : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x h₁
          - ((1 / X : ℝ) : ℂ) * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
              (fun n => MemS Pseq Qseq J n), ((f n : ℝ) : ℂ)‖ ^ 2)
      ≤ Bf)
    (hthm3one : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / h₁ : ℝ) : ℂ) * shortSum (fun _ => ((1 : ℝ) : ℂ))
              ((Finset.Icc ⌈X⌉₊ ⌊4 * X⌋₊).filter (fun n => MemS Pseq Qseq J n)) x h₁
          - ((1 / X : ℝ) : ℂ) * ∑ _n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
              (fun n => MemS Pseq Qseq J n), ((1 : ℝ) : ℂ)‖ ^ 2)
      ≤ B1) :
    ∃ x ∈ Set.Icc X (2 * X),
      |1 / h₁ * ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + h₁⌋₊).filter
            (fun n => MemS Pseq Qseq J n), f n
        - 1 / X * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
            (fun n => MemS Pseq Qseq J n), f n| ≤ δ / 100
      ∧ |1 / h₁ * (((Finset.Icc ⌈x⌉₊ ⌊x + h₁⌋₊).filter
            (fun n => MemS Pseq Qseq J n)).card : ℝ)
          - 1 / X * (((Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter
            (fun n => MemS Pseq Qseq J n)).card : ℝ)| ≤ δ / 100 := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  obtain ⟨E, hEsub, hEm, hEvol, hEpt⟩ :=
    thm3_pair_exceptional Pseq Qseq J f hX hh1 hh1T hδ hh1lo ha hthm3f hthm3one
  have he2 : (0 : ℝ) < (δ / 200) ^ 2 := by positivity
  have hlt : X * Bf / (δ / 200) ^ 2 + X * B1 / (δ / 200) ^ 2 < X := by
    rw [← add_div, div_lt_iff₀ he2]
    have h := mul_lt_mul_of_pos_left hgate hX0
    linarith
  have hvol : volume E < volume (Set.Icc X (2 * X)) := by
    refine lt_of_le_of_lt hEvol ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), Real.volume_Icc,
      show 2 * X - X = X by ring]
    exact (ENNReal.ofReal_lt_ofReal_iff hX0).mpr hlt
  have hnsub : ¬ Set.Icc X (2 * X) ⊆ E := fun hsub =>
    absurd (measure_mono hsub) (not_le.mpr hvol)
  obtain ⟨x, hxI, hxE⟩ := Set.not_subset.mp hnsub
  exact ⟨x, hxI, hEpt x ⟨hxI, hxE⟩⟩

/-! ## §3 — E26-8: the `A(h)` instantiation (★ the corner)

At the landed pin `A = 65536` the block bottom `P₁ = 2^A` is an ABSOLUTE
CONSTANT, so MR Theorem 3's error `(log h)^{1/3}/P₁^{1/6−η}` diverges along the
door road: the theorem is true and vacuous.  ⟦AMENDMENT A⟧'s repair makes the
anchor grow with `h` — `A ≈ (δ/8)·log₂ h`, `M := ⌈8/δ⌉`, so `P₁ ≈ h^{δ/8}` and
`Q₁ = 2^{M·A} ≤ h`, meeting MR p. 31's `[P₁, Q₁] ⊆ [1, h]`.

`δ` enters only as the ℕ parameter `δinv` (the call site's `⌈1/δ⌉`); no numeral
below is a function of `δ₀` (MARGIN-HYGIENE), and no `calP`/`calQK` is ever
evaluated (⟦V9c⟧). -/

/-- **`A_gate_logK`'s arithmetic at the scaled anchor**, stated over abstract reals.

`16(log 4M + log k + log e₂) ≤ (1/24)(68719476736(L+1)k·log 2 − 1)`, from the
three `DoorFrame` bounds plus `log k ≤ k − 1`.  The margin: after
`L·k·log2 ≥ L·log2` and `k·log2 ≥ log2`, the residue is `≈ 2.86·10⁹·log 2 > 1/24`.

⚠ **Stated abstractly on purpose.**  With the atoms in their native form — `↑k`,
`↑(Nat.log 2 M)`, i.e. `Nat.cast` of compound terms — `linarith` fails on this
same goal; generalising them makes the identical certificate go through
first try.  (New trap: `linarith`'s preprocessing and `Nat.cast` atoms.) -/
private lemma gate_log_arith {L kk a1 a2 a3 l2 : ℝ} (hl2 : 0.6931471803 < l2)
    (hL0' : 0 ≤ L * l2) (hb1 : a1 ≤ (L + 3) * l2) (hb2 : a3 ≤ (2 * L + 52) * l2)
    (hlogk : a2 ≤ kk - 1) (hp2 : 0 ≤ (kk - 1) * l2) (hp3 : 0 ≤ L * l2 * (kk - 1))
    (hkey : 16 * (kk - 1) ≤ 24 * ((kk - 1) * l2)) :
    4 * 2 ^ 2 * (a1 + (a2 + a3)) ≤ 1 / 12 / 2 * (68719476736 * (L + 1) * kk * l2 - 1) := by
  linarith

/-- **The `k`-scaled door frame** — `CalFrameK` at the anchor `Adoor M · k`, for
every `k ≥ 1` and every `M ≥ 1`.  At `k = 1` this IS
`DoorFrame.calFrameK_satisfiable_door`; the scaling is what `Ah` needs.

The gate that moves is `A_gate_logK`, and it moves by exactly one logarithm:
`calE (Adoor M · k) G 2 = k · calE (Adoor M) G 2`, so the left side gains
`16 log k` while the right side gains the factor `k` — and `log k ≤ k − 1`
(`Real.log_le_sub_one_of_pos`) closes it with room to spare (`16·(k−1)` against
`(1/24)·68719476736·(k−1)·log 2`).  Every other field is `DoorFrame`'s verbatim: the
`G_gateK` equality `256M ≤ (1/12)(3072M)`, the `P₁ ≥ 64` floor, the `H₁ = P₁^{1/6}`
K-3 width. -/
theorem calFrameK_satisfiable_scaled {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k) :
    CalFrameK (1 / 12)
      (((calP (Adoor M * k) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6))
      (Adoor M * k) (3072 * M) M 2 (calQK (Adoor M * k) (3072 * M) M 2) := by
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) := Nat.cast_nonneg _
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL0' : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) * Real.log 2 := mul_nonneg hL0 hlog2nn
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hkR
  have hA24 : (24 : ℕ) ≤ Adoor M * k :=
    le_trans (le_trans (by norm_num) (Adoor_ge M)) (Nat.le_mul_of_pos_right _ (by omega))
  have h64 : (64 : ℕ) ≤ calP (Adoor M * k) (3072 * M) 1 := by
    have hE : (6 : ℕ) ≤ calE (Adoor M * k) (3072 * M) 1 := by
      rw [calE_one]; omega
    have h6 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [calP, h6]
    exact Nat.pow_le_pow_right (by norm_num) hE
  have h64R : (64 : ℝ) ≤ ((calP (Adoor M * k) (3072 * M) 1 : ℕ) : ℝ) := by exact_mod_cast h64
  have hP1pos : (0 : ℝ) < ((calP (Adoor M * k) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hcalE2 : calE (Adoor M * k) (3072 * M) 2 = k * calE (Adoor M) (3072 * M) 2 := by
    simp only [calE]
    ring
  have hEpos : 0 < calE (Adoor M) (3072 * M) 2 := by
    rw [calE_door_two]
    exact Nat.mul_pos (by norm_num) (Nat.mul_pos (Nat.succ_pos _) hM)
  refine
    { eta_pos := by norm_num, eta_lt := by norm_num, one_le_Jb := by norm_num,
      one_le_G := by omega, one_le_M := hM, G_gateK := by push_cast; linarith,
      A_gate_lin := ?_, A_gate_logK := ?_, A_floor := hA24,
      H1_two := ?_, H1_pin := ?_, Q_le_Xd := le_rfl }
  · -- `A_gate_lin`: `2Jb = 4 ≤ 24 ≤ Adoor M · k`
    have h4 : ((24 : ℕ) : ℝ) ≤ ((Adoor M * k : ℕ) : ℝ) := by exact_mod_cast hA24
    push_cast at h4 ⊢
    linarith
  · -- `A_gate_logK`: `DoorFrame`'s estimate, plus the one logarithm `log k`
    have hlogsplit : Real.log ((k * calE (Adoor M) (3072 * M) 2 : ℕ) : ℝ)
        = Real.log (k : ℝ) + Real.log ((calE (Adoor M) (3072 * M) 2 : ℕ) : ℝ) := by
      have hk0 : ((k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hE0 : ((calE (Adoor M) (3072 * M) 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hEpos.ne'
      push_cast
      exact Real.log_mul hk0 hE0
    have hlogk : Real.log (k : ℝ) ≤ (k : ℝ) - 1 := Real.log_le_sub_one_of_pos hkpos
    have hb1 := log_four_M_door hM
    have hb2 := log_calE_door_two hM
    have hp1 : ((k : ℝ) - 1) * 0.6931471803 ≤ ((k : ℝ) - 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (by linarith)
    have hp2 : (0 : ℝ) ≤ ((k : ℝ) - 1) * Real.log 2 := by nlinarith
    have hp3 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) * Real.log 2 * ((k : ℝ) - 1) :=
      mul_nonneg hL0' (by linarith)
    have hkey : 16 * ((k : ℝ) - 1) ≤ 24 * (((k : ℝ) - 1) * Real.log 2) := by linarith
    rw [hcalE2, hlogsplit]
    push_cast
    rw [Adoor_cast]
    exact gate_log_arith hl2 hL0' hb1 hb2 hlogk hp2 hp3 hkey
  · -- `H1_two`: `2 = 64^{1/6} ≤ P₁^{1/6}`
    calc (2 : ℝ) = (64 : ℝ) ^ ((1 : ℝ) / 6) := by
          rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast 2 6,
            ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ ((calP (Adoor M * k) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6) :=
          Real.rpow_le_rpow (by norm_num) h64R (by norm_num)
  · -- `H1_pin`: `(P₁^{1/6})³ = P₁^{1/2}` — equality, as at the pinned frame
    have hid : ((((calP (Adoor M * k) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) ^ (3 : ℕ))
        = ((calP (Adoor M * k) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (((calP (Adoor M * k) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) 3,
        ← Real.rpow_mul hP1pos.le, show (1 : ℝ) / 6 * ((3 : ℕ) : ℝ) = (1 : ℝ) / 2 by norm_num]
    rw [hid]

/-- **THE `h`-DEPENDENT ANCHOR** `A(h)`.  With `M := 8·δinv` (the eq-(28) demand
scale `⌈8/δ⌉`) and `L := ⌊log₂ h⌋`,

`Ah δinv h := Adoor M · ⌊L / (M · Adoor M)⌋`,

so that `M · Ah δinv h ≤ L` — hence `Q₁ = 2^{M·A} ≤ 2^L ≤ h` — while
`L < M · (Ah δinv h + Adoor M)`, i.e. `P₁ = 2^{Ah} ≈ h^{1/M} = h^{δ/8}` up to a
bounded, `h`-free factor (`Ah_one_sided`).

**⚠ Floor, never ceiling, and never `+1`.**  The freeze's display `⌈(δ/8)log₂ h⌉`
(and the ℕ sketch `L/(8δinv) + 1`) BREAK the containment: `Q₁ ≤ h` demands
`M·A ≤ log₂ h`, which the ceiling violates at every `h` that is not an exact
power.  ℕ division is the floor, and the floor is what makes `Ah_containment` a
theorem.

**⚠ Why a multiple of `Adoor M`.**  A bare quotient `L/M` would satisfy the
containment but could not close `CalFrameK`'s `A_gate_logK` uniformly (the gate
needs the anchor to dominate `log(A·G)`).  Factoring the anchor as `Adoor M · k`
lets the frame ride `DoorFrame`'s own estimate — see
`calFrameK_satisfiable_scaled`.  The price is the frame's floor hypothesis
`M·Adoor M ≤ log₂ h`, which is exactly ⟦AMENDMENT A⟧'s corrected LEVEL-1
containment arm `H_K` (`DoorFrame.log_calQK_door_one`), not a new demand. -/
def Ah (δinv h : ℕ) : ℕ :=
  Adoor (8 * δinv) * (Nat.log 2 h / (8 * δinv * Adoor (8 * δinv)))

/-- `M · A(h) ≤ ⌊log₂ h⌋` — the floor-division identity the containment rests on. -/
theorem Ah_mul_le (δinv h : ℕ) : 8 * δinv * Ah δinv h ≤ Nat.log 2 h := by
  have h1 : 8 * δinv * Ah δinv h
      = 8 * δinv * Adoor (8 * δinv) * (Nat.log 2 h / (8 * δinv * Adoor (8 * δinv))) := by
    simp only [Ah]
    ring
  rw [h1]
  exact Nat.mul_div_le _ _

/-- **`P₁ ≈ h^{δ/8}`, one-sided**: `h < 2^{M·(A(h) + Adoor M)} = (P₁·2^{Adoor M})^M`.
Together with `Ah_containment`'s `2^{M·A(h)} ≤ h` this pins `P₁` to `h^{1/M}` up to
the `h`-free factor `2^{Adoor M}` — the whole point of the reparametrisation:
`P₁ → ∞` with `h`, so Theorem 3's error `(log h)^{1/3}/P₁^{1/6−η}` tends to `0`
instead of diverging as it does at the constant pin `A = 65536`. -/
theorem Ah_one_sided (δinv h : ℕ) (hδ : 1 ≤ δinv) :
    h < 2 ^ (8 * δinv * (Ah δinv h + Adoor (8 * δinv))) := by
  have hBpos : 0 < 8 * δinv * Adoor (8 * δinv) :=
    Nat.mul_pos (by omega) (lt_of_lt_of_le Nat.zero_lt_one (one_le_Adoor _))
  have hlt := Nat.lt_mul_div_succ (Nat.log 2 h) hBpos
  have hexp : 8 * δinv * (Ah δinv h + Adoor (8 * δinv))
      = 8 * δinv * Adoor (8 * δinv) * (Nat.log 2 h / (8 * δinv * Adoor (8 * δinv)) + 1) := by
    simp only [Ah]
    ring
  rw [hexp]
  refine lt_of_lt_of_le (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) h) ?_
  exact Nat.pow_le_pow_right (by norm_num) hlt

/-- **E26-8's containment** `[P₁, Q₁] ⊆ [1, h]` (MR p. 31) at the `h`-dependent
anchor, for every base `G`: `1 ≤ P₁`, `P₁ ≤ Q₁` (the K-widening,
`calP_le_calQK`), and `Q₁ = 2^{M·A(h)} ≤ 2^{⌊log₂h⌋} ≤ h` (`Ah_mul_le` and
`Nat.pow_log_le_self`).  This is the arm the constant pin `A = 65536` could only
satisfy for `h ≥ 2^{800·65536}`, i.e. never on the door road. -/
theorem Ah_containment (δinv h G : ℕ) (hδ : 1 ≤ δinv) (hh : 1 ≤ h) :
    1 ≤ calP (Ah δinv h) G 1
      ∧ calP (Ah δinv h) G 1 ≤ calQK (Ah δinv h) G (8 * δinv) 1
      ∧ calQK (Ah δinv h) G (8 * δinv) 1 ≤ h := by
  refine ⟨Nat.one_le_two_pow, calP_le_calQK (by omega) le_rfl, ?_⟩
  rw [calQK, calE_one]
  calc 2 ^ (1 ^ 2 * (8 * δinv) * Ah δinv h) ≤ 2 ^ Nat.log 2 h := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        simpa using Ah_mul_le δinv h
    _ ≤ h := Nat.pow_log_le_self 2 (by omega)

/-- **THE FRAME AT THE `h`-DEPENDENT ANCHOR** (`calFrameK_satisfiable_Ah`).
`CalFrameK` is inhabited at `A = Ah δinv h`, `G = 3072M`, `M = 8·δinv`, `Jb = 2`,
`H₁ = P₁^{1/6}`, `X_d = Q_{Jb}` — for every `δinv ≥ 1` and every `h` past the door
floor `M·Adoor M ≤ log₂ h`.  All twelve gates are `calFrameK_satisfiable_scaled`'s;
the floor hypothesis is what makes `k = ⌊log₂h/(M·Adoor M)⌋ ≥ 1`.

Together with `Ah_containment` this is the corner turned: the K-station frame and
MR p. 31's block containment hold SIMULTANEOUSLY, at an anchor that grows with
`h`.  Neither was available at the constant pin. -/
theorem calFrameK_satisfiable_Ah (δinv h : ℕ) (hδ : 1 ≤ δinv)
    (hfloor : 8 * δinv * Adoor (8 * δinv) ≤ Nat.log 2 h) :
    CalFrameK (1 / 12)
      (((calP (Ah δinv h) (3072 * (8 * δinv)) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6))
      (Ah δinv h) (3072 * (8 * δinv)) (8 * δinv) 2
      (calQK (Ah δinv h) (3072 * (8 * δinv)) (8 * δinv) 2) := by
  have hBpos : 0 < 8 * δinv * Adoor (8 * δinv) :=
    Nat.mul_pos (by omega) (lt_of_lt_of_le Nat.zero_lt_one (one_le_Adoor _))
  have hk1 : 1 ≤ Nat.log 2 h / (8 * δinv * Adoor (8 * δinv)) :=
    (Nat.one_le_div_iff hBpos).mpr hfloor
  simp only [Ah]
  exact calFrameK_satisfiable_scaled (by omega) hk1

/-- **The twelve `LevelGates` at the `A(h)` family**, free from the frame
(`levelGates_calibratedK`) — the `DoorFrame` corollary, transplanted to the
`h`-dependent anchor. -/
theorem levelGates_calibrated_Ah (δinv h : ℕ) (hδ : 1 ≤ δinv)
    (hfloor : 8 * δinv * Adoor (8 * δinv) ≤ Nat.log 2 h) :
    ∀ j ∈ Finset.Icc 2 2,
      LevelGates (calP (Ah δinv h) (3072 * (8 * δinv)))
        (calQK (Ah δinv h) (3072 * (8 * δinv)) (8 * δinv))
        (calH ((((calP (Ah δinv h) (3072 * (8 * δinv)) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6))))
        (1 / 12) ((calP (Ah δinv h) (3072 * (8 * δinv))) 1)
        (calQK (Ah δinv h) (3072 * (8 * δinv)) (8 * δinv) 2) j :=
  levelGates_calibratedK (calFrameK_satisfiable_Ah δinv h hδ hfloor)

end Salt.MR
