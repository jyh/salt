/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszCore
import Salt.MR.Decomp

/-!
# JFactor — the `𝒥`-factorisation of MRT (A.11)–(A.13)  (H-block node **H-5**)

Design block: `docs/exploration/hsup-design.md`, ⟦THE H-BLOCK FREEZE v2⟧ (ladder v2,
node H-5).  Source: Matomäki–Radziwiłł–Tao, arXiv `1503.05121v3`, Appendix A,
pp. 25–27 — the displays (A.11), (A.12), (A.13) and Lemma A.8.

The object.  MRT split the `y`-smooth part of a `1`-bounded multiplicative `f` by the
*block-avoidance* data: `g_j` is the multiplicative indicator with `g_j(p^k) = 1` iff
`p` lies outside the `j`-th prime block, `𝒮_𝒥(s) = ∑_n s_𝒥(n)/n^s` with
`s_𝒥 = f·g_𝒥·1_{y-smooth}` and `g_𝒥 = ∏_{j∈𝒥} g_j`.  Inclusion–exclusion,
`∏_j (1 - g_j) = ∑_{𝒥} (-1)^{#𝒥} g_𝒥`, turns the alternating sum of the `𝒮_𝒥` into a
single Euler product whose block factors are each `≤ 1`; the exit (A.13) is
`|∑_𝒥 (-1)^{#𝒥} 𝒮_𝒥(σ+it)| ≪ |𝒮_∅(σ+it)|^{1/2} ∏_{p≤y}(1+p^{-σ})^{1/2}`.

## ⟦STEP-0: THE HALF-OPEN PIN⟧ (mandatory, freeze-flagged)

MRT are internally inconsistent about the blocks: p. 21 (the construction of the
`P_j, Q_j`) writes the **closed** blocks `[P_j, Q_j]`, while pp. 25–26 ((A.11) and the
definition of `α_j, θ_j`) write the **half-open** blocks `(P_j, Q_j]`.

**The pin: this file uses the CLOSED block `[P, Q]`, matching the corpus.**  The
corpus fixed this convention long before H-5: `Decomp.primeBlockPoly` sums over
`(Finset.Icc P Q).filter Nat.Prime`, `Decomp.BlockPrimeDivs` filters on `P ≤ p ∧ p ≤ Q`,
and `TypicalDensity.primeBand P Q = (Finset.Icc P Q).filter Nat.Prime`.  `jBlock` below
is that same Finset, and `blockSum_one_eq_primeBlockPoly` machine-checks the
identification with `primeBlockPoly` at `σ = 1`.  **The MRT deviation is therefore
`(P_j, Q_j] ↝ [P_j, Q_j]`** — harmless for every statement here (all the block stones
below are proved for an *arbitrary* finite set of positive integers, so the endpoint
convention is a downstream instantiation choice, not a hypothesis of any proof), and it
is the convention the `𝒰`-machinery (`Decomp.Tset`/`Uset`, `USetThin`) consumes.

## The stones

* `prod_one_sub_eq_alt_sum` (J1) — inclusion–exclusion over the block data, for
  commuting ring elements: `∏_{j∈s}(1-g j) = ∑_{𝒥⊆s} (-1)^{#𝒥} ∏_{j∈𝒥} g j`.
* `blockAvoid`, `prod_one_sub_blockAvoid` (J1) — the corpus-shaped indicator version:
  the product of `1 - g_j` over the blocks is `1_𝒮`, the indicator of the `n` carrying a
  prime factor in *every* block (`1 ≤ blockOmega`, `Decomp`'s own predicate).
* `alt_sum_blockAvoid_dirichlet` (J1) — (A.11)'s first line as a finite-sum identity:
  the `𝒥`-alternating sum of the `g_𝒥`-twisted sums is the `1_𝒮`-twisted sum.
* `norm_exp_half_sub_sq`, `norm_exp_half_sub_le`, `norm_exp_half_sub_le'` (J2) —
  MRT (A.12) on the LANDED `halasz_cosh_ineq`: the law-of-cosines expansion
  `‖e^{z/2} - e^{-z/2}‖² = e^{Re z} + e^{-Re z} - 2cos(Im z)` and hence
  `‖e^{z/2} - e^{-z/2}‖ ≤ e^{‖z‖/2}`.
* `norm_blockSum_le`, `block_factor_le_one` (J3) — "the expression on the last line of
  (A.11) is always `≤ 1`" (p. 27, the sentence following Lemma A.8), unconditionally:
  no Euler exp-approximation is needed for this step.
* `euler_block_regroup`, `one_sub_inv_exp_eq`, `norm_one_sub_inv_exp_le`,
  `jfactor_A11_middle` (J3, the `hEuler`-conditional arm) — (A.11)'s middle step proved
  *exactly* (no `≪`), with the Euler exp-approximation `block product = exp(z_j)` as the
  named hypothesis.
* `norm_le_sqrt_mul_sqrt` (J4) — **the birth of the ½**: `‖E‖ ≤ W ⟹ ‖E‖ ≤ √‖E‖·√W`.
* `jfactor_alt_sum_le`, `jfactor_alt_sum_le_euler` (J4) — the (A.13) exit.

## Honest scope (what is a hypothesis and why)

The (A.11) *factorisation itself* — the passage from the `1_𝒮`-twisted Dirichlet sum to
`(the y-smooth Euler product) × ∏_j (block product - 1)` and then to the displayed
half-power majorant — is an Euler-product identity for `y`-smooth multiplicative
functions plus MRT's `≪`-step; it is **not** proved here.  `jfactor_alt_sum_le` takes it
as the named hypothesis `hA11` (with an explicit constant `C`, so the source's `≪` is
honest) and discharges exactly the part H-5 owns: every block correction factor is `≤ 1`,
hence drops out.  This is the Zeno-honest split flagged at dispatch.

## The ½ (the S-3 guard's stone)

`Real.sqrt ‖Sfull‖ * Real.sqrt W` in `jfactor_alt_sum_le` is the origin of the
ball-route grade halving: MRT's `|𝒮_∅|^{1/2} ∏_{p≤y}(1+p^{-σ})^{1/2}` in (A.13), which
propagates through (A.14) into p. 28's `exp(-M/2)`.  **This factor is the origin of the
ball-route grade halving; the §8.3/L3 arm does NOT consume this file** (the S-3
route-scoping, `docs/exploration/hsup-design.md`): L3's arm cites
`sigma_cutoff_pretentious_of_gen` (`c = 1/e`), the ball's arm cites the `_half` instance
(`c = 1/(2e)`), and a citation of this file — or of `_half` — in any §8.3 consumer is a
STOP.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §0  The pinned prime block (STEP 0) -/

/-- **The prime block `[P, Q]` — the STEP-0 pin.**  The primes `p` with `P ≤ p ≤ Q`,
i.e. exactly the index set of `Decomp.primeBlockPoly` (and of
`TypicalDensity.primeBand`).  MRT's Appendix-A displays write the half-open `(P_j, Q_j]`
while their p. 21 construction writes the closed `[P_j, Q_j]`; **the corpus's closed
convention wins** (see the module docstring). -/
def jBlock (P Q : ℕ) : Finset ℕ := (Finset.Icc P Q).filter Nat.Prime

lemma mem_jBlock {P Q p : ℕ} : p ∈ jBlock P Q ↔ (P ≤ p ∧ p ≤ Q) ∧ p.Prime := by
  rw [jBlock, Finset.mem_filter, Finset.mem_Icc]

/-- Block members are positive (they are primes). -/
lemma jBlock_pos {P Q : ℕ} : ∀ p ∈ jBlock P Q, 0 < p := by
  intro p hp
  exact (mem_jBlock.mp hp).2.pos

/-! ## §1  J1 — the inclusion–exclusion identity -/

/-- **J1 — inclusion–exclusion over the block data.**  For commuting ring elements,
`∏_{j∈s} (1 - g j) = ∑_{𝒥 ⊆ s} (-1)^{#𝒥} ∏_{j∈𝒥} g j`.  This is the identity MRT use
(p. 26, the first line of (A.11)) to convert the `𝒥`-alternating sum of the `𝒮_𝒥` into a
single sum over the `n` with a block prime factor in every block. -/
theorem prod_one_sub_eq_alt_sum {R ι : Type*} [CommRing R] (s : Finset ι) (g : ι → R) :
    ∏ j ∈ s, (1 - g j) = ∑ 𝒥 ∈ s.powerset, (-1) ^ 𝒥.card * ∏ j ∈ 𝒥, g j := by
  calc ∏ j ∈ s, (1 - g j) = ∏ j ∈ s, (1 + (-g j)) :=
        Finset.prod_congr rfl (fun j _ => by ring)
    _ = ∑ 𝒥 ∈ s.powerset, ∏ j ∈ 𝒥, (-g j) := Finset.prod_one_add s
    _ = ∑ 𝒥 ∈ s.powerset, (-1) ^ 𝒥.card * ∏ j ∈ 𝒥, g j :=
        Finset.sum_congr rfl (fun 𝒥 _ => Finset.prod_neg g)

/-- **`g_j` — the block-avoidance indicator** (MRT p. 25: the multiplicative function
with `g_j(p^k) = 1` iff `p ∉` block `j`).  Corpus-shaped: `g_j(n) = 1` exactly when `n`
has *no* prime factor in the block `[P, Q]`, i.e. when `Decomp`'s `blockOmega P Q n`
vanishes — the very predicate cutting out the coprime tail of `ramare_decomp`. -/
def blockAvoid (P Q n : ℕ) : ℂ := if blockOmega P Q n = 0 then 1 else 0

/-- **J1 (the indicator form) — `∏_j (1 - g_j) = 1_𝒮`.**  The product over a finite set
`s` of block indices is the indicator of the `n` having at least one prime factor in
*every* block `j ∈ s` (MRT's `𝒮`, p. 25). -/
theorem prod_one_sub_blockAvoid (s : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (n : ℕ) :
    ∏ j ∈ s, (1 - blockAvoid (Pseq j) (Qseq j) n)
      = if ∀ j ∈ s, 1 ≤ blockOmega (Pseq j) (Qseq j) n then 1 else 0 := by
  by_cases h : ∃ j ∈ s, blockOmega (Pseq j) (Qseq j) n = 0
  · obtain ⟨j, hj, hj0⟩ := h
    have hnot : ¬ ∀ j ∈ s, 1 ≤ blockOmega (Pseq j) (Qseq j) n := by
      intro hall
      have := hall j hj
      omega
    rw [if_neg hnot]
    exact Finset.prod_eq_zero hj (by rw [blockAvoid, if_pos hj0, sub_self])
  · have hall : ∀ j ∈ s, 1 ≤ blockOmega (Pseq j) (Qseq j) n := by
      intro j hj
      by_contra hc
      exact h ⟨j, hj, by omega⟩
    rw [if_pos hall]
    refine Finset.prod_eq_one (fun j hj => ?_)
    have hj' := hall j hj
    rw [blockAvoid, if_neg (by omega), sub_zero]

/-- **J1 — (A.11)'s first line, as a finite-sum identity.**  For any coefficient
sequence `c` (the consumer's `f(n)/n^{σ+it}`) and any finite index set `N` of `n`'s (the
consumer's `y`-smooth integers), the `𝒥`-alternating sum of the `g_𝒥`-twisted sums is
the `1_𝒮`-twisted sum:
`∑_{𝒥⊆s} (-1)^{#𝒥} ∑_{n∈N} c n · g_𝒥(n) = ∑_{n∈N} c n · 1_𝒮(n)`. -/
theorem alt_sum_blockAvoid_dirichlet (s N : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (c : ℕ → ℂ) :
    ∑ 𝒥 ∈ s.powerset, (-1) ^ 𝒥.card *
        ∑ n ∈ N, c n * ∏ j ∈ 𝒥, blockAvoid (Pseq j) (Qseq j) n
      = ∑ n ∈ N, c n *
          (if ∀ j ∈ s, 1 ≤ blockOmega (Pseq j) (Qseq j) n then 1 else 0) := by
  have hstep : ∑ 𝒥 ∈ s.powerset, (-1 : ℂ) ^ 𝒥.card *
        ∑ n ∈ N, c n * ∏ j ∈ 𝒥, blockAvoid (Pseq j) (Qseq j) n
      = ∑ 𝒥 ∈ s.powerset, ∑ n ∈ N,
          c n * ((-1 : ℂ) ^ 𝒥.card * ∏ j ∈ 𝒥, blockAvoid (Pseq j) (Qseq j) n) := by
    refine Finset.sum_congr rfl (fun 𝒥 _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← Finset.mul_sum, ← prod_one_sub_eq_alt_sum, prod_one_sub_blockAvoid]

/-! ## §2  J2 — MRT (A.12) on the landed `halasz_cosh_ineq`

MRT (A.12) (p. 26): `|exp(½(α+iθ)) - exp(-½(α+iθ))| ≤ exp(½√(α²+θ²))`.  Their proof is
"square both sides and apply the law of cosines" — the squared left side is exactly
`e^α + e^{-α} - 2cos θ`, and Lemma A.8 (`halasz_cosh_ineq`, LANDED in `HalaszCore`) bounds
that by `e^{√(α²+θ²)}`. -/

/-- **J2 (the law of cosines).**  The exact identity behind MRT's "squaring both sides
and applying the law of cosines":
`‖e^{(α+iθ)/2} - e^{-(α+iθ)/2}‖² = e^α + e^{-α} - 2cos θ`.
(Both `e^{±(α+iθ)/2}` have modulus `e^{±α/2}` and their arguments differ by `θ`.) -/
theorem norm_exp_half_sub_sq (α θ : ℝ) :
    ‖Complex.exp (((α : ℂ) + (θ : ℂ) * Complex.I) / 2)
        - Complex.exp (-(((α : ℂ) + (θ : ℂ) * Complex.I) / 2))‖ ^ 2
      = Real.exp α + Real.exp (-α) - 2 * Real.cos θ := by
  have harg : ((α : ℂ) + (θ : ℂ) * Complex.I) / 2
      = ((α / 2 : ℝ) : ℂ) + ((θ / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [harg]
  set w : ℂ := Complex.exp (((α / 2 : ℝ) : ℂ) + ((θ / 2 : ℝ) : ℂ) * Complex.I)
      - Complex.exp (-(((α / 2 : ℝ) : ℂ) + ((θ / 2 : ℝ) : ℂ) * Complex.I)) with hw
  have hre : w.re = (Real.exp (α / 2) - Real.exp (-(α / 2))) * Real.cos (θ / 2) := by
    rw [hw]
    simp only [Complex.sub_re, Complex.exp_re, Complex.neg_re, Complex.neg_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Real.cos_neg,
      mul_zero, mul_one, sub_zero, add_zero, zero_add]
    ring
  have him : w.im = (Real.exp (α / 2) + Real.exp (-(α / 2))) * Real.sin (θ / 2) := by
    rw [hw]
    simp only [Complex.sub_im, Complex.exp_im, Complex.neg_re, Complex.neg_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Real.sin_neg,
      mul_zero, mul_one, sub_zero, add_zero, zero_add]
    ring
  have hnormsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [hnormsq, hre, him]
  -- the algebra: `A·B = 1`, `A² = e^α`, `B² = e^{-α}`, `s² = 1 - c²`, `cos θ = 2c² - 1`
  have hAB : Real.exp (α / 2) * Real.exp (-(α / 2)) = 1 := by
    rw [← Real.exp_add, show α / 2 + -(α / 2) = 0 by ring, Real.exp_zero]
  have hA2 : Real.exp (α / 2) ^ 2 = Real.exp α := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hB2 : Real.exp (-(α / 2)) ^ 2 = Real.exp (-α) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hs2 : Real.sin (θ / 2) ^ 2 = 1 - Real.cos (θ / 2) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (θ / 2); linarith
  have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    exact h
  linear_combination (Real.exp (α / 2) + Real.exp (-(α / 2))) ^ 2 * hs2
    + (2 - 4 * Real.cos (θ / 2) ^ 2) * hAB + hA2 + hB2 + 2 * hcos

/-- **J2 — MRT (A.12).**  `‖e^{(α+iθ)/2} - e^{-(α+iθ)/2}‖ ≤ e^{√(α²+θ²)/2}`.  Squaring,
this is exactly the landed Lemma A.8 `halasz_cosh_ineq` at `(α, θ)`. -/
theorem norm_exp_half_sub_le (α θ : ℝ) :
    ‖Complex.exp (((α : ℂ) + (θ : ℂ) * Complex.I) / 2)
        - Complex.exp (-(((α : ℂ) + (θ : ℂ) * Complex.I) / 2))‖
      ≤ Real.exp (Real.sqrt (α ^ 2 + θ ^ 2) / 2) := by
  set w : ℂ := Complex.exp (((α : ℂ) + (θ : ℂ) * Complex.I) / 2)
      - Complex.exp (-(((α : ℂ) + (θ : ℂ) * Complex.I) / 2)) with hw
  have hsq : ‖w‖ ^ 2 = Real.exp α + Real.exp (-α) - 2 * Real.cos θ := norm_exp_half_sub_sq α θ
  have hcosh : Real.exp α + Real.exp (-α) - 2 * Real.cos θ
      ≤ Real.exp (Real.sqrt (α ^ 2 + θ ^ 2)) := halasz_cosh_ineq α θ
  have hRsq : Real.exp (Real.sqrt (α ^ 2 + θ ^ 2) / 2) ^ 2
      = Real.exp (Real.sqrt (α ^ 2 + θ ^ 2)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hle : ‖w‖ ^ 2 ≤ Real.exp (Real.sqrt (α ^ 2 + θ ^ 2) / 2) ^ 2 := by
    rw [hsq, hRsq]; exact hcosh
  calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
    _ ≤ Real.sqrt (Real.exp (Real.sqrt (α ^ 2 + θ ^ 2) / 2) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.exp (Real.sqrt (α ^ 2 + θ ^ 2) / 2) := Real.sqrt_sq (Real.exp_pos _).le

/-- **J2 (the `z`-form).**  `‖e^{z/2} - e^{-z/2}‖ ≤ e^{‖z‖/2}` for every `z : ℂ`: the
`√(α²+θ²)` of (A.12) is exactly `‖z‖` at `z = α + iθ`.  This is the form the block
factor of (A.11) consumes. -/
theorem norm_exp_half_sub_le' (z : ℂ) :
    ‖Complex.exp (z / 2) - Complex.exp (-(z / 2))‖ ≤ Real.exp (‖z‖ / 2) := by
  have hz : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
  have hnorm : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := Complex.norm_eq_sqrt_sq_add_sq z
  have h := norm_exp_half_sub_le z.re z.im
  rw [hz, ← hnorm] at h
  exact h

/-! ## §3  J3 — the block factor of (A.11) is `≤ 1`

MRT p. 26–27: with `z_j = ∑_{p ∈ block j} f(p)/p^{σ+it}` and `α_j = Re z_j`,
`θ_j = Im z_j`, the last line of (A.11) is
`∏_j |exp(½z_j) - exp(-½z_j)| · exp(-½ ∑_{p ∈ block j} p^{-σ})`, and "the expression on
the last line is always `≤ 1`": by the triangle inequality `α_j² + θ_j² = ‖z_j‖²
≤ (∑ p^{-σ})²`, so (A.12) closes it.  Both steps are unconditional — no Euler
exp-approximation enters here. -/

/-- **The block sum `z_j`** (MRT p. 26): `∑_{p ∈ B} f(p)/p^{σ+it}` over a finite block
`B` of primes.  At `σ = 1` and `B = jBlock P Q` this is `Decomp.primeBlockPoly`
(`blockSum_one_eq_primeBlockPoly`). -/
noncomputable def blockSum (f : ℕ → ℂ) (B : Finset ℕ) (σ t : ℝ) : ℂ :=
  ∑ p ∈ B, f p / (p : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)

/-- **The block mass** `∑_{p ∈ B} p^{-σ}` — the majorant of `‖z_j‖` and the exponent of
the compensating factor in (A.11)'s last line. -/
noncomputable def blockMass (B : Finset ℕ) (σ : ℝ) : ℝ := ∑ p ∈ B, (p : ℝ) ^ (-σ)

/-- **The STEP-0 pin, machine-checked.**  At `σ = 1` the block sum over the pinned closed
block `[P, Q]` *is* the corpus's `Decomp.primeBlockPoly`. -/
lemma blockSum_one_eq_primeBlockPoly (f : ℕ → ℂ) (P Q : ℕ) (t : ℝ) :
    blockSum f (jBlock P Q) 1 t = primeBlockPoly f P Q t := by
  simp only [blockSum, jBlock, primeBlockPoly, Complex.ofReal_one]

lemma blockMass_nonneg (B : Finset ℕ) (σ : ℝ) : 0 ≤ blockMass B σ :=
  Finset.sum_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)

/-- **J3 (the triangle inequality of (A.11)).**  For a `1`-bounded `f`,
`‖z_B‖ ≤ ∑_{p∈B} p^{-σ}` — MRT's `α_j² + θ_j² ≤ (∑ p^{-σ})²` in norm form. -/
theorem norm_blockSum_le {f : ℕ → ℂ} (hf : ∀ p, ‖f p‖ ≤ 1) {B : Finset ℕ}
    (hB : ∀ p ∈ B, 0 < p) (σ t : ℝ) :
    ‖blockSum f B σ t‖ ≤ blockMass B σ := by
  simp only [blockSum, blockMass]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (g := fun p : ℕ => (p : ℝ) ^ (-σ)) (fun p hp => ?_)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hB p hp
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hpos : (0 : ℝ) < (p : ℝ) ^ σ := Real.rpow_pos_of_pos hp0 σ
  rw [norm_div, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0, hre]
  calc ‖f p‖ / (p : ℝ) ^ σ = ‖f p‖ * ((p : ℝ) ^ σ)⁻¹ := div_eq_mul_inv _ _
    _ ≤ 1 * ((p : ℝ) ^ σ)⁻¹ := mul_le_mul_of_nonneg_right (hf p) (inv_nonneg.mpr hpos.le)
    _ = (p : ℝ) ^ (-σ) := by rw [one_mul, Real.rpow_neg hp0.le]

/-- **J3 — the block factor of (A.11) is `≤ 1`** (MRT p. 27, the sentence after Lemma
A.8).  For a `1`-bounded `f` and a finite block `B` of positive integers,
`|exp(½ z_B) - exp(-½ z_B)| · exp(-½ ∑_{p∈B} p^{-σ}) ≤ 1`.
Unconditional: (A.12) (`norm_exp_half_sub_le'`) at `z_B`, then `‖z_B‖ ≤ ∑ p^{-σ}`. -/
theorem block_factor_le_one {f : ℕ → ℂ} (hf : ∀ p, ‖f p‖ ≤ 1) {B : Finset ℕ}
    (hB : ∀ p ∈ B, 0 < p) (σ t : ℝ) :
    ‖Complex.exp (blockSum f B σ t / 2) - Complex.exp (-(blockSum f B σ t / 2))‖
        * Real.exp (-(blockMass B σ) / 2) ≤ 1 := by
  have h1 := norm_exp_half_sub_le' (blockSum f B σ t)
  have h2 := norm_blockSum_le hf hB σ t
  have h3 : Real.exp (‖blockSum f B σ t‖ / 2) ≤ Real.exp (blockMass B σ / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  calc ‖Complex.exp (blockSum f B σ t / 2) - Complex.exp (-(blockSum f B σ t / 2))‖
        * Real.exp (-(blockMass B σ) / 2)
      ≤ Real.exp (blockMass B σ / 2) * Real.exp (-(blockMass B σ) / 2) :=
        mul_le_mul_of_nonneg_right (h1.trans h3) (Real.exp_pos _).le
    _ = 1 := by
        rw [← Real.exp_add, show blockMass B σ / 2 + -(blockMass B σ) / 2 = 0 by ring,
          Real.exp_zero]

/-- The block factors of (A.11) are nonnegative — the companion of
`block_factor_le_one` for `Finset.prod_le_one`. -/
lemma block_factor_nonneg (f : ℕ → ℂ) (B : Finset ℕ) (σ t : ℝ) :
    0 ≤ ‖Complex.exp (blockSum f B σ t / 2) - Complex.exp (-(blockSum f B σ t / 2))‖
        * Real.exp (-(blockMass B σ) / 2) :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

/-! ## §3b  J3 (the `hEuler`-conditional form) — (A.11)'s middle step

MRT's (A.11) regroups `(the block-free Euler product) × ∏_j (block product - 1)` into
`(the full y-smooth product) × ∏_j (1 - 1/block product)`, and — under the Euler
exp-approximation `block product = exp(z_j)` — writes each corrected factor as
`e^{-z_j/2}(e^{z_j/2} - e^{-z_j/2})`.  Both steps are landed here *exactly* (no `≪`); the
exp-approximation itself is the named hypothesis (the file's Zeno residual). -/

/-- **(A.11)'s regrouping, exactly.**  If the full `y`-smooth Euler product factors as
`Efull = Efree · ∏_{j∈s} Eblk j` with each block factor nonzero, then
`Efree · ∏_j (Eblk j - 1) = Efull · ∏_j (1 - 1/Eblk j)`. -/
lemma euler_block_regroup {s : Finset ℕ} {Efree Efull : ℂ} {Eblk : ℕ → ℂ}
    (hfull : Efull = Efree * ∏ j ∈ s, Eblk j) (hne : ∀ j ∈ s, Eblk j ≠ 0) :
    Efree * ∏ j ∈ s, (Eblk j - 1) = Efull * ∏ j ∈ s, (1 - (Eblk j)⁻¹) := by
  rw [hfull, mul_assoc, ← Finset.prod_mul_distrib]
  refine congrArg (Efree * ·) (Finset.prod_congr rfl (fun j hj => ?_))
  have h := hne j hj
  field_simp

/-- **The symmetrised block factor.**  `1 - e^{-z} = e^{-z/2}(e^{z/2} - e^{-z/2})` — the
algebraic identity behind MRT's passage to the `exp(½z_j) - exp(-½z_j)` shape. -/
lemma one_sub_inv_exp_eq (z : ℂ) :
    1 - (Complex.exp z)⁻¹
      = Complex.exp (-(z / 2)) * (Complex.exp (z / 2) - Complex.exp (-(z / 2))) := by
  have h1 : Complex.exp (-(z / 2)) * Complex.exp (z / 2) = 1 := by
    rw [← Complex.exp_add, show -(z / 2) + z / 2 = 0 by ring, Complex.exp_zero]
  have h2 : Complex.exp (-(z / 2)) * Complex.exp (-(z / 2)) = (Complex.exp z)⁻¹ := by
    rw [← Complex.exp_add, ← Complex.exp_neg]; congr 1; ring
  rw [mul_sub, h1, h2]

/-- **J3 (the corrected block factor).**  `‖1 - e^{-z}‖ ≤ e^{(‖z‖ - Re z)/2}` — the
symmetrised factor of (A.11) bounded via (A.12).  Unconditional. -/
lemma norm_one_sub_inv_exp_le (z : ℂ) :
    ‖1 - (Complex.exp z)⁻¹‖ ≤ Real.exp ((‖z‖ - z.re) / 2) := by
  have hre : (-(z / 2)).re = -(z.re / 2) := by
    rw [show -(z / 2) = ((-(1 / 2) : ℝ) : ℂ) * z by push_cast; ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [one_sub_inv_exp_eq z, norm_mul, Complex.norm_exp, hre]
  calc Real.exp (-(z.re / 2))
        * ‖Complex.exp (z / 2) - Complex.exp (-(z / 2))‖
      ≤ Real.exp (-(z.re / 2)) * Real.exp (‖z‖ / 2) :=
        mul_le_mul_of_nonneg_left (norm_exp_half_sub_le' z) (Real.exp_pos _).le
    _ = Real.exp ((‖z‖ - z.re) / 2) := by rw [← Real.exp_add]; congr 1; ring

/-- **J3 — (A.11)'s middle step, `hEuler`-conditional.**  Given the Euler factorisation of
the alternating `𝒥`-sum (`hfact`) and of the full `y`-smooth product (`hfull`), both with
the block products presented in exp-form `exp (z j)` — MRT's exp-approximation, the named
hypothesis this file does not prove — the alternating sum obeys
`‖∑_𝒥 (-1)^{#𝒥} 𝒮_𝒥‖ ≤ ‖𝒮_∅‖ · ∏_j exp((‖z_j‖ - Re z_j)/2)`.
Combined with `norm_le_sqrt_mul_sqrt` (§4) this is (A.13)'s route; `jfactor_alt_sum_le`
is the same exit taken directly at MRT's displayed majorant. -/
theorem jfactor_A11_middle {s : Finset ℕ} {S : Finset ℕ → ℂ} {Efree Efull : ℂ} {z : ℕ → ℂ}
    (hfact : ∑ 𝒥 ∈ s.powerset, (-1 : ℂ) ^ 𝒥.card * S 𝒥
      = Efree * ∏ j ∈ s, (Complex.exp (z j) - 1))
    (hfull : Efull = Efree * ∏ j ∈ s, Complex.exp (z j)) :
    ‖∑ 𝒥 ∈ s.powerset, (-1 : ℂ) ^ 𝒥.card * S 𝒥‖
      ≤ ‖Efull‖ * ∏ j ∈ s, Real.exp ((‖z j‖ - (z j).re) / 2) := by
  rw [hfact, euler_block_regroup hfull (fun j _ => Complex.exp_ne_zero _), norm_mul,
    Complex.norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Finset.prod_le_prod (fun j _ => norm_nonneg _)
    (fun j _ => norm_one_sub_inv_exp_le (z j))

/-! ## §4  J4 — the (A.13) exit

MRT (A.13) (p. 27): once the block factors are `≤ 1`,
`∑_{𝒥 ⊆ {1,…,J}} (-1)^{#𝒥} 𝒮_𝒥(σ+it) ≪ |𝒮_∅(σ+it)|^{1/2} ∏_{p≤y}(1+p^{-σ})^{1/2}`.

The (A.11) factorisation itself is the hypothesis `hA11` (see the module docstring's
"Honest scope"); H-5 owns the discharge of the block product. -/

/-- **The smooth Euler mass** `∏_{p ≤ y} (1 + p^{-σ})` — the second half-power of the
(A.13) majorant.  Index set: the primes in `[2, y]` (the corpus's `Finset.Icc`
convention, cf. `jBlock`). -/
noncomputable def smoothMass (y : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (1 + (p : ℝ) ^ (-σ))

/-- **⟦THE ½ IS BORN HERE⟧.**  MRT's (A.13) trades the full Euler product for the pair of
half-powers `|𝒮_∅|^{1/2} ∏_{p≤y}(1+p^{-σ})^{1/2}`; the *only* input is a majorant
`‖E‖ ≤ W`, and the square root is then forced:
`‖E‖ = √(‖E‖·‖E‖) ≤ √(‖E‖·W) = √‖E‖·√W`.
This one line is the origin of the ball-route grade halving (`e^{-M/(2e)}` instead of
`e^{-M/e}`) ratified as S-3 on 2026-07-25.  **The §8.3/L3 arm does NOT consume this
file**: L3 keeps the un-halved `c = 1/e` ledger (`sigma_cutoff_pretentious_of_gen`), and
a citation of this lemma — or of the `_half` σ-cutoff instance — inside a §8.3 consumer
is a STOP (the S-3 route-scoping live guard, `docs/exploration/hsup-design.md`). -/
lemma norm_le_sqrt_mul_sqrt {E : ℂ} {W : ℝ} (h : ‖E‖ ≤ W) :
    ‖E‖ ≤ Real.sqrt ‖E‖ * Real.sqrt W := by
  rw [← Real.sqrt_mul (norm_nonneg E)]
  calc ‖E‖ = Real.sqrt (‖E‖ * ‖E‖) := (Real.sqrt_mul_self (norm_nonneg E)).symm
    _ ≤ Real.sqrt (‖E‖ * W) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h (norm_nonneg E))

lemma smoothMass_nonneg (y : ℕ) (σ : ℝ) : 0 ≤ smoothMass y σ := by
  refine Finset.prod_nonneg (fun p _ => ?_)
  have : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  linarith

/-- **J4 — the (A.13) exit.**  Given MRT's (A.11) factorisation `hA11` — the alternating
`𝒥`-sum bounded by `C · ‖𝒮_∅‖^{1/2} · W^{1/2}` times the product of the block
corrections — the block corrections drop out, leaving
`‖∑_{𝒥⊆s} (-1)^{#𝒥} 𝒮_𝒥‖ ≤ C · ‖𝒮_∅‖^{1/2} · W^{1/2}`.

**THE ½ LIVES HERE.**  `Real.sqrt ‖Sfull‖ * Real.sqrt W` is the half-power pair of
(A.13); it is the origin of the ball-route grade halving (`e^{-M/(2e)}`, S-3 as ratified
2026-07-25).  The §8.3/L3 arm does **not** consume this file: L3 keeps the un-halved
`c = 1/e` ledger via `sigma_cutoff_pretentious_of_gen`.  A citation of this lemma (or of
the `_half` σ-cutoff instance) inside a §8.3 consumer is a STOP.

Hypotheses, honestly: `s` is the block index set (MRT's `{1,…,J}`, i.e. `Finset.Icc 1 J`
in the corpus's `Decomp` indexing); `blk j` is the `j`-th block (MRT's `(P_j,Q_j]`, our
pinned `jBlock (P j) (Q j)`); `S 𝒥` is `𝒮_𝒥(σ+it)`; `Sfull` is `𝒮_∅(σ+it)`; `W` is the
smooth Euler mass `∏_{p≤y}(1+p^{-σ})` (see `jfactor_alt_sum_le_euler`). -/
theorem jfactor_alt_sum_le {f : ℕ → ℂ} (hf : ∀ p, ‖f p‖ ≤ 1) {s : Finset ℕ}
    {blk : ℕ → Finset ℕ} (hblk : ∀ j ∈ s, ∀ p ∈ blk j, 0 < p)
    {σ t C W : ℝ} {S : Finset ℕ → ℂ} {Sfull : ℂ} (hC : 0 ≤ C)
    (hA11 : ‖∑ 𝒥 ∈ s.powerset, (-1 : ℂ) ^ 𝒥.card * S 𝒥‖
      ≤ C * (Real.sqrt ‖Sfull‖ * Real.sqrt W)
          * ∏ j ∈ s, (‖Complex.exp (blockSum f (blk j) σ t / 2)
              - Complex.exp (-(blockSum f (blk j) σ t / 2))‖
                * Real.exp (-(blockMass (blk j) σ) / 2))) :
    ‖∑ 𝒥 ∈ s.powerset, (-1 : ℂ) ^ 𝒥.card * S 𝒥‖
      ≤ C * (Real.sqrt ‖Sfull‖ * Real.sqrt W) := by
  have hprod : ∏ j ∈ s, (‖Complex.exp (blockSum f (blk j) σ t / 2)
      - Complex.exp (-(blockSum f (blk j) σ t / 2))‖
        * Real.exp (-(blockMass (blk j) σ) / 2)) ≤ 1 :=
    Finset.prod_le_one (fun j _ => block_factor_nonneg f (blk j) σ t)
      (fun j hj => block_factor_le_one hf (hblk j hj) σ t)
  have hpre : 0 ≤ C * (Real.sqrt ‖Sfull‖ * Real.sqrt W) :=
    mul_nonneg hC (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  refine hA11.trans ?_
  calc C * (Real.sqrt ‖Sfull‖ * Real.sqrt W)
        * ∏ j ∈ s, (‖Complex.exp (blockSum f (blk j) σ t / 2)
            - Complex.exp (-(blockSum f (blk j) σ t / 2))‖
              * Real.exp (-(blockMass (blk j) σ) / 2))
      ≤ C * (Real.sqrt ‖Sfull‖ * Real.sqrt W) * 1 := by
        exact mul_le_mul_of_nonneg_left hprod hpre
    _ = C * (Real.sqrt ‖Sfull‖ * Real.sqrt W) := mul_one _

/-- **J4 (the (A.13) exit at the concrete Euler mass).**  `jfactor_alt_sum_le` with
`W = ∏_{p≤y}(1+p^{-σ})`, the shape MRT display:
`|∑_𝒥 (-1)^{#𝒥} 𝒮_𝒥(σ+it)| ≪ |𝒮_∅(σ+it)|^{1/2} ∏_{p≤y}(1+p^{-σ})^{1/2}`.
The blocks are the pinned closed blocks `jBlock (P j) (Q j)` (STEP 0). -/
theorem jfactor_alt_sum_le_euler {f : ℕ → ℂ} (hf : ∀ p, ‖f p‖ ≤ 1) {s : Finset ℕ}
    {Pseq Qseq : ℕ → ℕ} {σ t C : ℝ} {y : ℕ} {S : Finset ℕ → ℂ} {Sfull : ℂ} (hC : 0 ≤ C)
    (hA11 : ‖∑ 𝒥 ∈ s.powerset, (-1 : ℂ) ^ 𝒥.card * S 𝒥‖
      ≤ C * (Real.sqrt ‖Sfull‖ * Real.sqrt (smoothMass y σ))
          * ∏ j ∈ s, (‖Complex.exp (blockSum f (jBlock (Pseq j) (Qseq j)) σ t / 2)
              - Complex.exp (-(blockSum f (jBlock (Pseq j) (Qseq j)) σ t / 2))‖
                * Real.exp (-(blockMass (jBlock (Pseq j) (Qseq j)) σ) / 2))) :
    ‖∑ 𝒥 ∈ s.powerset, (-1 : ℂ) ^ 𝒥.card * S 𝒥‖
      ≤ C * (Real.sqrt ‖Sfull‖ * Real.sqrt (smoothMass y σ)) :=
  jfactor_alt_sum_le hf (blk := fun j => jBlock (Pseq j) (Qseq j))
    (fun _ _ => jBlock_pos) hC hA11

end Salt.MR
