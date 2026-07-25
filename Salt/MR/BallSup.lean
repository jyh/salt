/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszDirect
import Salt.MR.Renormalise
import Salt.MR.SevenEighths
import Salt.Mertens.Third

/-!
# BallSup — the CENTRE-TO-BALL transfer (H-7)

The last stone of the H-block (`docs/exploration/hsup-design.md`, ⟦THE H-BLOCK FREEZE v2⟧,
node **H-7**): the assembly of the four landed H-stones into
`SeamBallWeighted.ball_leg_of_sup_weighted`'s exact binder `hSup′`

  `∀ t, seamT0 X ≤ |t| → |t| ≤ T → |t − t₁| ≤ seamRad X →
     ∀ m ≤ N, ‖A_t(m)‖ ≤ S·m/(1+|t−t₁|)`.

## THE B3 PAGE VERDICT — the plain datum suffices

MRT's A.6 runs the renormalisation through the `𝒥`-machinery (the `g_J` smooth parts,
`JFactor`'s alternating Dirichlet identity), because their target exponent needs the ⅞-cut of
the prime budget.  **At the grade `hSup′` actually demands, the `𝒥`-layer is not needed.**
The arithmetic, worked here in full:

* GS 7.1 (`renormalise_shifted`) carries the error factor
  `exp(∑_{p≤x} ‖1 − f(p)p^{−it₁}‖/p)`.
* Cauchy–Schwarz (`SevenEighths.sum_norm_one_sub_div_le`) with the unit-disc device
  `‖1−z‖² ≤ 2−2ℜz` gives `∑_{p≤x} ‖1 − u(p)‖/p ≤ √(2·P(x))·√(M)` with `P(x) = ∑_{p≤x} 1/p`
  the Mertens mass and `M = 𝔻(f, n^{it₁}; x)²` the pretentious distance.
* The A.4 **ball** hypothesis `M ≤ P(x)/8` (`hMball`; the exact convention of
  `SevenEighths.seven_eighths_bound_primes`) turns this into `≤ P(x)/2`.
* Mertens-2 (`Salt.Mertens.mertens_second_sharp_real`) then gives
  `exp(P(x)/2) ≤ √(log x)·e^{M₂/2+6}` — a `(log x)^{1/2}` budget, NOT the `(log x)^{7/8}`
  that would need the `𝒥`-cut.
* Composed with GS 7.1's `x/log x` prefactor the error is
  `≪ x·(log x)^{−1/2}·log(3+|t−t₁|(1+log x))`, i.e. **exactly the `(log X)^{−1/2+ε}` second
  term of the frozen interface** — the term the `𝒥`-layer was feared to be needed for.
* Cost of the weight: the binder's `/(1+|t−t₁|)` shape multiplies the error by
  `1+|t−t₁| ≤ 1+(log X)^{1/16}`, so the honest second term of `S` is
  `(log X)^{−1/2+1/16+o(1)} = (log X)^{−7/16+o(1)}`.  The live band's main term is
  `e^{−M/(2e)} ≥ (log X)^{−1/(32e)} = (log X)^{−0.0115…}` (M < (1/16)loglog X, freeze v2 §5),
  so the second term is smaller by a factor `(log X)^{−0.42…}` — **the grade closes with a
  large margin, with NO `𝒥`-layer, no `hA11`, no `hEuler`, no `JFactor` import.**

## What is proved and what is named

* `center_to_ball_transfer` (**B2**) — the abstract transfer at ONE scale: a direct
  consumption of `renormalise_shifted` + `renormalise_factor_norm(_le)`.  Unconditional.
* `budget_le_half_abstract`, `budget_le_half`, `exp_budget_le` (**B3**) — the budget page.
* `transfer_at_scale` — B2 ∘ B3: the transfer with the error already in `ballErr` form.
* `ball_sup_of_center` (**B4**) — the exit, in `ball_leg_of_sup_weighted`'s binder shape.
* `intervalIntegrable_seam_lseries_div` (**B1 / H-6a**) — the socketed integrability hint of
  `HalaszDirect.halasz_direct_ball(_window)`, DISCHARGED.

**The named hypotheses of `ball_sup_of_center`** (each one a real, recorded gap, none of them
forced closed):

* `hCenter` — the CENTRE bound `‖∑_{n≤k} f(n)n^{−it₁}‖ ≤ S₀·k` for `⌊X⌋₊ ≤ k ≤ N`.  This is
  the Halász pointwise bound AT THE CENTRE.  Our σ-integral core
  (`halasz_direct_ball_window`) bounds the `L`-series σ-integral, not the partial sum; the
  step between them is GHS Prop 2.1 / the S1′ hat representation
  (`prop21_unconditional_clean`), which is a separate wire.  H-7's content is the transfer
  FROM the centre TO the ball, and that is what is proved here.
* `hMball` — the A.4 ball dichotomy in Mertens-mass form
  (`𝔻(f,n^{it₁};x)² ≤ P(x)/8` for `x ∈ [X,2X]`).  `PropA3Core.dist_split_A4_frozen` states
  the branch-b centre cap as `≤ (1/16)·loglog X`; converting `(1/16)loglog X ≤ P(x)/8`
  needs `12/log X − M₂ ≤ (1/2)loglog X`, i.e. a large-`X` threshold plus a numeric lower
  bound on the Meissel–Mertens constant `M₂` — neither is in the corpus, so the conversion
  is NOT performed here (recorded, not hidden).  The `[X,2X]` range (rather than the single
  scale `X`) is because the partial sums run to `m ≤ N ≤ 2X`.
* `hDatum` — the dyadic-vs-full datum bridge `a n = f n` for `n > X`, paired with the row's
  own `hsupp` (`a n = 0` for `n ≤ X`).  Together they say the seam row's dyadic coefficient
  sequence IS the restriction of a 1-bounded multiplicative `f` to `(X, 2X]`; the honest
  identity `A_t(m) = F_t(m) − F_t(X)` (`spolyA_datum_split`) is then a theorem, not an
  assumption.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §0 — two conventions bridges -/

/-- The two prime-set conventions of the corpus agree: `renormalise`'s
`(Icc 1 ⌊x⌋₊).filter Prime` is `pretDistSq`/`SPartial`'s `(range (⌊x⌋₊+1)).filter Prime`. -/
lemma primes_Icc_eq_range (n : ℕ) :
    (Finset.Icc 1 n).filter Nat.Prime = (Finset.range (n + 1)).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, h2⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h1, hp⟩; exact ⟨⟨hp.one_lt.le, by omega⟩, hp⟩

/-- `spolyA`'s `cpow` term in `eIu` form: `c/n^{it} = c·n^{−it}` for `n ≠ 0`.  (The corpus
writes `n^{iu}` as `exp(I·u·log n)` — `cpow`'s norm lemmas are gated off `Re s = 0`.) -/
lemma div_cpow_eq_eIu (c : ℂ) (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    c / (n : ℂ) ^ ((t : ℂ) * Complex.I) = c * eIu (-t) n := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, eIu_eq, div_eq_mul_inv,
    ← Complex.exp_neg]
  congr 1
  push_cast
  ring_nf

/-! ## §1 (B3) — the budget page: the plain-datum prime sum

The exponent `∑_{p≤x} ‖1 − f(p)p^{−it₁}‖/p` of GS 7.1's error, bounded through
Cauchy–Schwarz + the A.4 ball hypothesis + Mertens-2. -/

/-- **The Cauchy–Schwarz half-cut, abstract.**  On any finite set of positive integers, a
1-bounded `u` whose distance mass is at most an eighth of the Mertens mass has
`∑ ‖1 − u(p)‖/p ≤ (1/2)·∑ 1/p`.

The certificate is exact: `√(2P)·√(P/8) = √(P²/4) = P/2`.  (This is the `𝒥`-free analogue of
`seven_eighths_bound`: without the exceptional set the constant is `1/2`, not `7/8`.) -/
lemma budget_le_half_abstract {S : Finset ℕ} {u : ℕ → ℂ}
    (hS : ∀ p ∈ S, 0 < p) (hu : ∀ p ∈ S, ‖u p‖ ≤ 1)
    (hM : ∑ p ∈ S, (1 - (u p).re) / (p : ℝ) ≤ (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 8) :
    ∑ p ∈ S, ‖1 - u p‖ / (p : ℝ) ≤ (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 2 := by
  have hP0 : (0 : ℝ) ≤ ∑ p ∈ S, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hM0 : (0 : ℝ) ≤ ∑ p ∈ S, (1 - (u p).re) / (p : ℝ) :=
    Finset.sum_nonneg fun p hp =>
      div_nonneg (by linarith [le_trans (Complex.re_le_norm (u p)) (hu p hp)])
        (Nat.cast_nonneg p)
  have hCS := sum_norm_one_sub_div_le S u hS hu
  have h2 : (∑ p ∈ S, (2 : ℝ) / (p : ℝ)) = 2 * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [h2] at hCS
  refine hCS.trans ?_
  rw [← Real.sqrt_mul (by positivity)]
  calc Real.sqrt (2 * (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) * ∑ p ∈ S, (1 - (u p).re) / (p : ℝ))
      ≤ Real.sqrt (((∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / 2 := Real.sqrt_sq (by linarith)

/-- **The budget's half-cut at the primes `≤ x`** — the A.4 ball hypothesis in the
Mertens-mass convention of `seven_eighths_bound_primes`, delivered in `renormalise`'s own
`(Icc 1 ⌊x⌋₊).filter Prime` shape. -/
lemma budget_le_half {u : ℕ → ℂ} {x : ℝ} (hu : ∀ p, ‖u p‖ ≤ 1)
    (hM : pretDistSq u (fun _ => 1) x ≤ Salt.Mertens.SPartial x / 8) :
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - u p‖ / (p : ℝ)
      ≤ Salt.Mertens.SPartial x / 2 := by
  have hMeq : pretDistSq u (fun _ => 1) x
      = ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 - (u p).re) / (p : ℝ) := by
    unfold pretDistSq
    exact Finset.sum_congr rfl fun p _ => by rw [map_one, mul_one]
  rw [hMeq] at hM
  unfold Salt.Mertens.SPartial at hM ⊢
  rw [primes_Icc_eq_range]
  exact budget_le_half_abstract (fun p hp => (Finset.mem_filter.mp hp).2.pos)
    (fun p _ => hu p) hM

/-- **The exponentiated budget (the B3 headline).**  Under the A.4 ball hypothesis the GS 7.1
error factor is `(log x)^{1/2}`-grade:

  `exp(∑_{p≤x} ‖1 − u(p)‖/p) ≤ √(log x)·exp(M₂/2 + 6)`,

`M₂` the Meissel–Mertens constant.  This is the exact statement that makes the `𝒥`-layer
unnecessary for `hSup′` — see the module docstring. -/
lemma exp_budget_le {u : ℕ → ℂ} {x : ℝ} (hx : 3 ≤ x) (hu : ∀ p, ‖u p‖ ≤ 1)
    (hM : pretDistSq u (fun _ => 1) x ≤ Salt.Mertens.SPartial x / 8) :
    Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - u p‖ / (p : ℝ))
      ≤ Real.sqrt (Real.log x) * Real.exp (Salt.Mertens.mertensM / 2 + 6) := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hE : Real.exp 1 ≤ x := by
    have := Real.exp_one_lt_d9
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hE
  have hmert := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hx2)
  have h12 : 12 / Real.log x ≤ 12 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hb := budget_le_half hu hM
  have hstep : (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - u p‖ / (p : ℝ))
      ≤ Real.log (Real.log x) / 2 + (Salt.Mertens.mertensM / 2 + 6) := by
    linarith [hmert.2]
  have hsqrt : Real.exp (Real.log (Real.log x) / 2) = Real.sqrt (Real.log x) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith)]
    congr 1
    ring
  calc Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - u p‖ / (p : ℝ))
      ≤ Real.exp (Real.log (Real.log x) / 2 + (Salt.Mertens.mertensM / 2 + 6)) :=
        Real.exp_le_exp.mpr hstep
    _ = Real.exp (Real.log (Real.log x) / 2) * Real.exp (Salt.Mertens.mertensM / 2 + 6) :=
        Real.exp_add _ _
    _ = Real.sqrt (Real.log x) * Real.exp (Salt.Mertens.mertensM / 2 + 6) := by rw [hsqrt]

/-! ## §2 (B2) — the centre-to-ball transfer at one scale -/

/-- **B2 — the centre-to-ball transfer, abstract and unconditional.**  For a 1-bounded
multiplicative `f`, any frequencies `t, t₁` and any `x ≥ 2`:

  `‖∑_{n≤x} f(n)n^{−it}‖ ≤ (√2/(1+|t−t₁|))·‖∑_{n≤x} f(n)n^{−it₁}‖ + (GS 7.1's error at
   α = t₁ − t)`.

A direct consumption of `renormalise_shifted` (the MRT-shape corollary, correct sign) with
`renormalise_factor_norm` + `renormalise_factor_norm_le` for the modulus page
`(1+u²)^{−1/2} ≤ √2/(1+|u|)`.  The `x`-uniformity is free: `renormalise` holds at every
`x ≥ 2`. -/
theorem center_to_ball_transfer {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b)
    (hfle : ∀ n, ‖f n‖ ≤ 1) (t t₁ : ℝ) {x : ℝ} (hx : 2 ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu (-t) n‖
      ≤ Real.sqrt 2 / (1 + |t - t₁|) * ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu (-t₁) n‖
        + renormaliseConst * (x / Real.log x)
            * (1 + Real.log (3 + |t - t₁| * (1 + Real.log x)))
            * Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
                ‖1 - f p * eIu (-t₁) p‖ / p) := by
  have h := renormalise_shifted hf1 hfmul hfle t t₁ hx
  rw [abs_sub_comm t₁ t] at h
  have hρ : ‖eIu (t₁ - t) x / (1 + Complex.I * ((t₁ - t : ℝ) : ℂ))‖
      ≤ Real.sqrt 2 / (1 + |t - t₁|) := by
    rw [renormalise_factor_norm]
    have hle := renormalise_factor_norm_le (t₁ - t)
    rwa [abs_sub_comm t₁ t] at hle
  set A := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu (-t) n with hA
  set B := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu (-t₁) n with hB
  set ρ := eIu (t₁ - t) x / (1 + Complex.I * ((t₁ - t : ℝ) : ℂ)) with hρdef
  calc ‖A‖ = ‖(A - ρ * B) + ρ * B‖ := by ring_nf
    _ ≤ ‖A - ρ * B‖ + ‖ρ * B‖ := norm_add_le _ _
    _ ≤ (renormaliseConst * (x / Real.log x)
            * (1 + Real.log (3 + |t - t₁| * (1 + Real.log x)))
            * Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
                ‖1 - f p * eIu (-t₁) p‖ / p))
          + Real.sqrt 2 / (1 + |t - t₁|) * ‖B‖ := by
        rw [norm_mul]
        exact add_le_add h (mul_le_mul_of_nonneg_right hρ (norm_nonneg _))
    _ = Real.sqrt 2 / (1 + |t - t₁|) * ‖B‖
          + renormaliseConst * (x / Real.log x)
            * (1 + Real.log (3 + |t - t₁| * (1 + Real.log x)))
            * Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
                ‖1 - f p * eIu (-t₁) p‖ / p) := by ring

/-! ## §3 — the error majorant and its constants -/

/-- The plain-datum error constant: GS 7.1's `C` times the Mertens exponential. -/
noncomputable def ballSupC : ℝ := renormaliseConst * Real.exp (Salt.Mertens.mertensM / 2 + 6)

lemma ballSupC_pos : 0 < ballSupC := by
  have h28 : (28 : ℝ) ≤ renormaliseConst := by
    rw [renormaliseConst_eq]
    nlinarith [one_le_exp_eight, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  exact mul_pos (by linarith) (Real.exp_pos _)

/-- **The error majorant.**  `ballErr x r = C·(x/√(log x))·(1 + log(3 + r(1+log x)))` — GS
7.1's error with the `(log x)^{1/2}` budget already substituted (`exp_budget_le`) and the
`x/log x · √(log x) = x/√(log x)` collapse performed.  The `(log x)^{−1/2}` is the frozen
interface's second term. -/
noncomputable def ballErr (x r : ℝ) : ℝ :=
  ballSupC * (x / Real.sqrt (Real.log x)) * (1 + Real.log (3 + r * (1 + Real.log x)))

/-- The ball's log-factor at its widest: `r ≤ seamRad X` and `x ≤ 2X`. -/
noncomputable def ballLterm (X : ℝ) : ℝ :=
  1 + Real.log (3 + seamRad X * (1 + Real.log (2 * X)))

/-- The tail (second) term's coefficient in `ballSupS`, before the weight is paid. -/
noncomputable def ballTail (X : ℝ) : ℝ :=
  4 * ballSupC * ballLterm X / Real.sqrt (Real.log X)

/-- **The exit constant `S`.**  `S = 2√2·S₀ + ballTail X·(1 + seamRad X)`: the centre bound
amplified by the renormalisation modulus (`√2`, twice — once per endpoint of the dyadic
window), plus the `(log X)^{−1/2}` error paid at the weight `1+|t−t₁| ≤ 1+(log X)^{1/16}`,
i.e. a `(log X)^{−7/16+o(1)}` second term. -/
noncomputable def ballSupS (X S₀ : ℝ) : ℝ :=
  2 * Real.sqrt 2 * S₀ + ballTail X * (1 + seamRad X)

lemma ballLterm_pos {X : ℝ} (hX : 3 ≤ X) : 0 < ballLterm X := by
  have hrad : 0 ≤ seamRad X := seamRad_nonneg (Real.log_nonneg (by linarith))
  have hlog : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have h3 : (1 : ℝ) ≤ 3 + seamRad X * (1 + Real.log (2 * X)) := by nlinarith
  have := Real.log_nonneg h3
  unfold ballLterm
  linarith

lemma ballTail_nonneg {X : ℝ} (hX : 3 ≤ X) : 0 ≤ ballTail X := by
  have h1 := ballLterm_pos hX
  have h2 := ballSupC_pos
  unfold ballTail
  positivity

lemma ballSupS_nonneg {X S₀ : ℝ} (hX : 3 ≤ X) (hS₀ : 0 ≤ S₀) : 0 ≤ ballSupS X S₀ := by
  have h1 := ballTail_nonneg hX
  have hrad : 0 ≤ seamRad X := seamRad_nonneg (Real.log_nonneg (by linarith))
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold ballSupS
  have : 0 ≤ ballTail X * (1 + seamRad X) := by positivity
  nlinarith

/-- `x/L·√L = x/√L` — the collapse that turns GS 7.1's `x/log x` prefactor and the
`(log x)^{1/2}` budget into the `(log x)^{−1/2}` grade. -/
lemma div_log_mul_sqrt (x : ℝ) {L : ℝ} (hL : 0 < L) :
    x / L * Real.sqrt L = x / Real.sqrt L := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hs), div_mul_eq_mul_div, mul_assoc,
    Real.mul_self_sqrt hL.le, mul_div_assoc, div_self (ne_of_gt hL), mul_one]

/-- **B2 ∘ B3 — the transfer with the error already in `ballErr` form.**  The consumable
one-scale statement: under the A.4 ball hypothesis at scale `x`, the whole GS 7.1 error is
`≤ ballErr x |t−t₁|`. -/
theorem transfer_at_scale {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b)
    (hfle : ∀ n, ‖f n‖ ≤ 1) {t t₁ x : ℝ} (hx : 3 ≤ x)
    (hM : pretDistSq (fun n => f n * eIu (-t₁) n) (fun _ => 1) x
      ≤ Salt.Mertens.SPartial x / 8) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu (-t) n‖
      ≤ Real.sqrt 2 / (1 + |t - t₁|) * ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu (-t₁) n‖
        + ballErr x |t - t₁| := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hE : Real.exp 1 ≤ x := by
    have := Real.exp_one_lt_d9
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hE
  have hu : ∀ p, ‖f p * eIu (-t₁) p‖ ≤ 1 := by
    intro p
    rw [norm_mul, norm_eIu, mul_one]
    exact hfle p
  have hbud := exp_budget_le hx hu hM
  refine (center_to_ball_transfer hf1 hfmul hfle t t₁ hx2).trans ?_
  have hpre : (0 : ℝ) ≤ renormaliseConst * (x / Real.log x)
      * (1 + Real.log (3 + |t - t₁| * (1 + Real.log x))) := by
    have h28 : (28 : ℝ) ≤ renormaliseConst := by
      rw [renormaliseConst_eq]
      nlinarith [one_le_exp_eight, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
    have hL : (1 : ℝ) ≤ 3 + |t - t₁| * (1 + Real.log x) := by
      nlinarith [abs_nonneg (t - t₁)]
    have := Real.log_nonneg hL
    have hxl : (0 : ℝ) ≤ x / Real.log x := by positivity
    have : (0 : ℝ) ≤ 1 + Real.log (3 + |t - t₁| * (1 + Real.log x)) := by linarith
    positivity
  have hkey : renormaliseConst * (x / Real.log x)
        * (1 + Real.log (3 + |t - t₁| * (1 + Real.log x)))
        * Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ‖1 - f p * eIu (-t₁) p‖ / p)
      ≤ ballErr x |t - t₁| := by
    refine (mul_le_mul_of_nonneg_left hbud hpre).trans (le_of_eq ?_)
    unfold ballErr ballSupC
    rw [← div_log_mul_sqrt x (by linarith : (0 : ℝ) < Real.log x)]
    ring
  linarith

/-! ## §4 — the datum bridge -/

/-- **The dyadic datum bridge.**  If `a` vanishes on `n ≤ X` and agrees with `f` on `n > X`,
then the seam row's twisted partial sum is the DIFFERENCE of two full partial sums:

  `A_t(m) = F_t(m) − F_t(X)`,  `F_t(u) = ∑_{n≤u} f(n)n^{−it}`,

for every `m ≥ ⌊X⌋₊`.  (Both endpoints are half-open-safe: the identity never assumes the
dyadic window is closed at `X` — `hsupp` and `hDatum` split at `n ≤ X` vs `n > X`.) -/
lemma spolyA_datum_split {a f : ℕ → ℂ} {X : ℝ} (hX0 : 0 ≤ X)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hDatum : ∀ n : ℕ, X < (n : ℝ) → a n = f n)
    (t : ℝ) {m : ℕ} (hm : ⌊X⌋₊ ≤ m) :
    spolyA a t m
      = (∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n)
        - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n * eIu (-t) n := by
  classical
  have hAe : spolyA a t m = ∑ n ∈ Finset.Icc 1 m, a n * eIu (-t) n := by
    unfold spolyA
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact div_cpow_eq_eIu (a n) t (by omega)
  have hsub : Finset.Icc 1 ⌊X⌋₊ ⊆ Finset.Icc 1 m := Finset.Icc_subset_Icc_right hm
  have h1 : (∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 ⌊X⌋₊, f n * eIu (-t) n)
      + ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n * eIu (-t) n
      = ∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n := Finset.sum_sdiff hsub
  have h2 : (∑ n ∈ Finset.Icc 1 m, a n * eIu (-t) n)
      = ∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 ⌊X⌋₊, a n * eIu (-t) n := by
    refine (Finset.sum_subset Finset.sdiff_subset ?_).symm
    intro n hn hn'
    have hnX : n ∈ Finset.Icc 1 ⌊X⌋₊ := by
      by_contra hc
      exact hn' (Finset.mem_sdiff.mpr ⟨hn, hc⟩)
    have hle : (n : ℝ) ≤ X :=
      le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hnX).2) (Nat.floor_le hX0)
    rw [hsupp n hle, zero_mul]
  have h3 : (∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 ⌊X⌋₊, a n * eIu (-t) n)
      = ∑ n ∈ Finset.Icc 1 m \ Finset.Icc 1 ⌊X⌋₊, f n * eIu (-t) n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_sdiff.mp hn
    have hgt : ⌊X⌋₊ < n := by
      by_contra hc
      exact hn2 (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn1).1, by omega⟩)
    rw [hDatum n ((Nat.floor_lt hX0).mp hgt)]
  rw [hAe, h2, h3, ← h1]
  ring

/-! ## §5 — the error majorant on the dyadic range -/

/-- The error majorant, uniformly over the dyadic range `x ∈ [X, 2X]` and the ball's
frequencies `|t−t₁| ≤ seamRad X`.  Both monotonicities are elementary: `x/√(log x)` is
increasing and the log-factor is increasing in both `r` and `x`. -/
lemma ballErr_le {X x r : ℝ} (hX : 3 ≤ X) (hx : X ≤ x) (hx2 : x ≤ 2 * X)
    (hr : 0 ≤ r) (hrad : r ≤ seamRad X) :
    ballErr x r ≤ ballTail X * X / 2 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hE : Real.exp 1 ≤ X := by
    have := Real.exp_one_lt_d9
    linarith
  have hlogX : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hE
  have hlogx : Real.log X ≤ Real.log x := Real.log_le_log hX0 hx
  have hsX : 0 < Real.sqrt (Real.log X) := Real.sqrt_pos.mpr (by linarith)
  have hmono : Real.sqrt (Real.log X) ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt hlogx
  -- (i) the `x/√(log x)` factor
  have hxq : x / Real.sqrt (Real.log x) ≤ 2 * X / Real.sqrt (Real.log X) := by
    rw [div_le_div_iff₀ (lt_of_lt_of_le hsX hmono) hsX]
    have ha : x * Real.sqrt (Real.log X) ≤ 2 * X * Real.sqrt (Real.log X) :=
      mul_le_mul_of_nonneg_right hx2 hsX.le
    have hb : 2 * X * Real.sqrt (Real.log X) ≤ 2 * X * Real.sqrt (Real.log x) :=
      mul_le_mul_of_nonneg_left hmono (by linarith)
    linarith
  -- (ii) the log-factor
  have hlog2X : Real.log x ≤ Real.log (2 * X) := Real.log_le_log hx0 (by linarith)
  have hlogx0 : (0 : ℝ) ≤ Real.log x := by linarith
  have hinner : 3 + r * (1 + Real.log x) ≤ 3 + seamRad X * (1 + Real.log (2 * X)) := by
    have : r * (1 + Real.log x) ≤ seamRad X * (1 + Real.log (2 * X)) :=
      mul_le_mul hrad (by linarith) (by linarith) (le_trans hr hrad)
    linarith
  have hpos : (0 : ℝ) < 3 + r * (1 + Real.log x) := by nlinarith
  have hLog : 1 + Real.log (3 + r * (1 + Real.log x)) ≤ ballLterm X := by
    unfold ballLterm
    have := Real.log_le_log hpos hinner
    linarith
  -- assemble
  have hC := ballSupC_pos
  have hLt := ballLterm_pos hX
  have hq0 : (0 : ℝ) ≤ x / Real.sqrt (Real.log x) := by positivity
  have hlogpos : (0 : ℝ) ≤ 1 + Real.log (3 + r * (1 + Real.log x)) := by
    have := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 3 + r * (1 + Real.log x))
    linarith
  calc ballErr x r
      = ballSupC * (x / Real.sqrt (Real.log x))
          * (1 + Real.log (3 + r * (1 + Real.log x))) := rfl
    _ ≤ ballSupC * (2 * X / Real.sqrt (Real.log X)) * ballLterm X := by
        gcongr
    _ = ballTail X * X / 2 := by
        unfold ballTail
        ring

/-! ## §6 (B4) — THE EXIT: `ball_leg_of_sup_weighted`'s binder -/

/-- **B4 — `ball_sup_of_center`: the H-7 exit.**  The centre bound transfers to the whole
ball, in exactly `SeamBallWeighted.ball_leg_of_sup_weighted`'s binder shape

  `∀ t, seamT0 X ≤ |t| → |t| ≤ T → |t − t₁| ≤ seamRad X →
     ∀ m ≤ N, ‖spolyA a t m‖ ≤ (ballSupS X S₀)·m/(1+|t−t₁|)`,

with `ballSupS X S₀ = 2√2·S₀ + ballTail X·(1+seamRad X)`, the second term of grade
`(log X)^{−7/16+o(1)}`.

**The page.**  `hDatum`+`hsupp` give `A_t(m) = F_t(m) − F_t(⌊X⌋₊)` (`spolyA_datum_split`).
Each of the two full partial sums is transferred to the centre by `transfer_at_scale`
(GS 7.1 at `α = t₁−t`, modulus `≤ √2/(1+|t−t₁|)`, error `≤ ballErr`), and `hCenter` bounds
the two centre sums by `S₀·m` and `S₀·⌊X⌋₊ ≤ S₀·m`.  The two errors are majorised uniformly
on `[X,2X]` by `ballTail X·X/2 ≤ ballTail X·m/2` each; paying the weight
`1+|t−t₁| ≤ 1+seamRad X` completes the constant.  Below `⌊X⌋₊` the sum is empty by `hsupp`.

**Named hypotheses** — `hCenter` (the centre's Halász bound, the S1′/Prop 2.1 wire),
`hMball` (the A.4 ball dichotomy in Mertens-mass form), `hDatum` (the dyadic bridge).  See
the module docstring for why each is carried rather than discharged. -/
theorem ball_sup_of_center {N : ℕ} {a f : ℕ → ℂ} {X T t₁ S₀ : ℝ}
    (hX : 3 ≤ X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X)
    (hf1 : f 1 = 1) (hfmul : ∀ p q : ℕ, Nat.Coprime p q → f (p * q) = f p * f q)
    (hfle : ∀ n, ‖f n‖ ≤ 1) (hS₀ : 0 ≤ S₀)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hDatum : ∀ n : ℕ, X < (n : ℝ) → a n = f n)
    (hCenter : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖∑ n ∈ Finset.Icc 1 k, f n * eIu (-t₁) n‖ ≤ S₀ * k)
    (hMball : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (fun n => f n * eIu (-t₁) n) (fun _ => 1) x
        ≤ Salt.Mertens.SPartial x / 8) :
    ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ ballSupS X S₀ * m / (1 + |t - t₁|) := by
  intro t _hann0 _hann1 hball m hm
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hd : (0 : ℝ) < 1 + |t - t₁| := by positivity
  have hrad0 : (0 : ℝ) ≤ seamRad X := seamRad_nonneg (Real.log_nonneg (by linarith))
  have hSnn : 0 ≤ ballSupS X S₀ := ballSupS_nonneg hX hS₀
  rw [le_div_iff₀ hd]
  rcases le_or_gt m ⌊X⌋₊ with hcase | hcase
  · -- below the dyadic window the polynomial is empty
    have hz : spolyA a t m = 0 := by
      unfold spolyA
      refine Finset.sum_eq_zero fun n hn => ?_
      have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
      have hle : (n : ℝ) ≤ X :=
        le_trans (Nat.cast_le.mpr (le_trans hnm hcase)) (Nat.floor_le hX0)
      rw [hsupp n hle, zero_div]
    rw [hz, norm_zero, zero_mul]
    positivity
  · -- the live range `⌊X⌋₊ < m ≤ N ≤ 2X`
    have hkm : ⌊X⌋₊ ≤ m := le_of_lt hcase
    have hXm : X < (m : ℝ) := (Nat.floor_lt hX0).mp hcase
    have hmN : (m : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hm
    have hm2X : (m : ℝ) ≤ 2 * X := le_trans hmN hN2
    have hm3 : (3 : ℝ) ≤ (m : ℝ) := le_trans hX hXm.le
    have hkN : ⌊X⌋₊ ≤ N := Nat.cast_le.mp (le_trans (Nat.floor_le hX0) hXN)
    have hkle : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hkm
    -- the datum split
    have hsplit := spolyA_datum_split hX0 hsupp hDatum t hkm
    -- the transfer at scale `m`
    have hAm : ‖∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n‖
        ≤ Real.sqrt 2 / (1 + |t - t₁|) * (S₀ * (m : ℝ)) + ballErr (m : ℝ) |t - t₁| := by
      have h := transfer_at_scale hf1 hfmul hfle (t := t) (t₁ := t₁) (x := (m : ℝ)) hm3
        (hMball (m : ℝ) hXm.le hm2X)
      rw [Nat.floor_natCast] at h
      refine h.trans ?_
      have hq : (0 : ℝ) ≤ Real.sqrt 2 / (1 + |t - t₁|) := by positivity
      have := mul_le_mul_of_nonneg_left (hCenter m hkm hm) hq
      linarith
    -- the transfer at scale `X`
    have hAX : ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n * eIu (-t) n‖
        ≤ Real.sqrt 2 / (1 + |t - t₁|) * (S₀ * (m : ℝ)) + ballErr X |t - t₁| := by
      have h := transfer_at_scale hf1 hfmul hfle (t := t) (t₁ := t₁) (x := X) hX
        (hMball X le_rfl (by linarith))
      refine h.trans ?_
      have hq : (0 : ℝ) ≤ Real.sqrt 2 / (1 + |t - t₁|) := by positivity
      have hc := hCenter ⌊X⌋₊ le_rfl hkN
      have hmono : S₀ * ((⌊X⌋₊ : ℕ) : ℝ) ≤ S₀ * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hkle hS₀
      have := mul_le_mul_of_nonneg_left (le_trans hc hmono) hq
      linarith
    -- the two errors
    have hEm : ballErr (m : ℝ) |t - t₁| ≤ ballTail X * (m : ℝ) / 2 := by
      refine (ballErr_le hX hXm.le hm2X (abs_nonneg _) hball).trans ?_
      have := ballTail_nonneg hX
      have : ballTail X * X ≤ ballTail X * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hXm.le (ballTail_nonneg hX)
      linarith
    have hEX : ballErr X |t - t₁| ≤ ballTail X * (m : ℝ) / 2 := by
      refine (ballErr_le hX le_rfl (by linarith) (abs_nonneg _) hball).trans ?_
      have : ballTail X * X ≤ ballTail X * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hXm.le (ballTail_nonneg hX)
      linarith
    -- assemble the pointwise bound
    have hnorm : ‖spolyA a t m‖
        ≤ ‖∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n‖
          + ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n * eIu (-t) n‖ := by
      rw [hsplit]
      exact norm_sub_le _ _
    have hmain : ‖spolyA a t m‖
        ≤ 2 * (Real.sqrt 2 / (1 + |t - t₁|) * (S₀ * (m : ℝ))) + ballTail X * (m : ℝ) := by
      linarith
    -- pay the weight
    have hQd : Real.sqrt 2 / (1 + |t - t₁|) * (1 + |t - t₁|) = Real.sqrt 2 :=
      div_mul_cancel₀ _ (ne_of_gt hd)
    have hTm : (0 : ℝ) ≤ ballTail X * (m : ℝ) := by
      have := ballTail_nonneg hX
      positivity
    calc ‖spolyA a t m‖ * (1 + |t - t₁|)
        ≤ (2 * (Real.sqrt 2 / (1 + |t - t₁|) * (S₀ * (m : ℝ)))
            + ballTail X * (m : ℝ)) * (1 + |t - t₁|) :=
          mul_le_mul_of_nonneg_right hmain hd.le
      _ = 2 * (Real.sqrt 2 / (1 + |t - t₁|) * (1 + |t - t₁|)) * (S₀ * (m : ℝ))
            + ballTail X * (m : ℝ) * (1 + |t - t₁|) := by ring
      _ = 2 * Real.sqrt 2 * (S₀ * (m : ℝ)) + ballTail X * (m : ℝ) * (1 + |t - t₁|) := by
          rw [hQd]
      _ ≤ 2 * Real.sqrt 2 * (S₀ * (m : ℝ))
            + ballTail X * (m : ℝ) * (1 + seamRad X) := by
          have := mul_le_mul_of_nonneg_left (by linarith : 1 + |t - t₁| ≤ 1 + seamRad X) hTm
          linarith
      _ = ballSupS X S₀ * (m : ℝ) := by
          unfold ballSupS
          ring

/-! ## §7 (B1 / H-6a) — the socketed integrability hint, DISCHARGED

`HalaszDirect.halasz_direct_ball(_window)` carries the σ-integrability of
`σ ↦ ‖L(ℓ(seamCoeff …))(1+σ+it)‖/σ` as a hypothesis.  It is the generic continuity route:
the datum is 1-bounded, so its abscissa of absolute convergence is `≤ 1`
(`HalaszRep.abscissa_ellLin_le_one`), `LSeries` is differentiable — hence continuous — on
`{Re s > abscissa}`, and on `[1/logX, b]` the real part `1+σ ≥ 1 + 1/logX` stays strictly
right of `1`.  Division by `σ` is safe because `σ ≥ 1/logX > 0` there. -/

/-- The vertical-line restriction `σ ↦ L(a)(1+σ+it)` is continuous on any `uIcc c d` with
`0 < c ≤ d`, when `a`'s abscissa of absolute convergence is `≤ 1`. -/
lemma continuousOn_LSeries_sigma {a : ℕ → ℂ} (ha : LSeries.abscissaOfAbsConv a ≤ 1)
    {t c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    ContinuousOn (fun σ : ℝ => LSeries a (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I))
      (Set.uIcc c d) := by
  have hmaps : Set.MapsTo (fun σ : ℝ => ((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)
      (Set.uIcc c d) {z : ℂ | LSeries.abscissaOfAbsConv a < z.re} := by
    intro σ hσ
    rw [Set.uIcc_of_le hcd] at hσ
    have hσc : c ≤ σ := (Set.mem_Icc.mp hσ).1
    have hre : (1 : ℝ) < (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im]
      linarith
    exact ha.trans_lt (by exact_mod_cast hre)
  have hcont : ContinuousOn (fun σ : ℝ => ((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)
      (Set.uIcc c d) :=
    (((Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).add
      continuous_const)).continuousOn
  exact (LSeries_differentiableOn a).continuousOn.comp hcont hmaps

/-- **B1 / H-6a — the `halasz_direct_ball` hint, discharged.**  The σ-integrand of the ball
arm's direct-form Halász core is interval-integrable on `[1/logX, b]`. -/
theorem intervalIntegrable_seam_lseries_div {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t X b : ℝ} (hL : 0 < Real.log X) (hb : 1 / Real.log X ≤ b) :
    IntervalIntegrable
      (fun σ : ℝ => ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      volume (1 / Real.log X) b := by
  have hc : (0 : ℝ) < 1 / Real.log X := by positivity
  have hbd : ∀ p, p.Prime → ‖seamCoeff (ellLin g) (fun _ => 1) t₀ p‖ ≤ 1 := fun p _ =>
    norm_seamCoeff_le (ellLin_norm_le_one g hg) (fun _ => le_of_eq norm_one) t₀ p
  have habs := abscissa_ellLin_le_one (seamCoeff (ellLin g) (fun _ => 1) t₀) hbd
  refine ContinuousOn.intervalIntegrable ?_
  refine ((continuousOn_LSeries_sigma (t := t) habs hc hb).norm).div
    continuousOn_id fun σ hσ => ?_
  rw [Set.uIcc_of_le hb] at hσ
  exact ne_of_gt (lt_of_lt_of_le hc (Set.mem_Icc.mp hσ).1)

/-- **The ball arm's direct Halász core, HINT-FREE.**  `halasz_direct_ball_window` with its
socketed integrability hypothesis discharged by `intervalIntegrable_seam_lseries_div`.

**BALL ARM ONLY** — this cites `halasz_direct_ball_window`, which cites
`sigma_cutoff_pretentious_half` (`c = 1/(2e)`).  Freeze v2's LIVE GUARD, verbatim: *"L3's arm
cites `sigma_cutoff_pretentious_of_gen` (c = 1/e); the ball's arm cites `_half`
(c = 1/(2e)); a citation of `_half` in any §8.3 consumer is a STOP."*  A §8.3/L3 consumer of
THIS statement is a STOP — use `halasz_direct_gen`. -/
theorem halasz_direct_ball_window_free {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t t₁ X T b : ℝ} (hL : 3 ≤ Real.log X) (hTX : T ≤ X)
    (hb : 1 / Real.log X ≤ b) (hb1 : b ≤ 1)
    (hM0 : 0 ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
    (hann : t ∈ seamAnn X T) (hball : t ∈ seamBall X t₁) :
    (∫ σ in (1 / Real.log X)..b,
        ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1))
          * Real.exp (-(1 / (2 * Real.exp 1))
              * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
          * Real.log X :=
  halasz_direct_ball_window hg hL hTX hb hb1 hM0 hann hball
    (intervalIntegrable_seam_lseries_div hg (by linarith) hb)

end Salt.MR
