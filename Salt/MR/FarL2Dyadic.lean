/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FarL2

/-!
# `FarL2Dyadic` — ⟦THE N-TERM REPAIR⟧: the dyadic-in-`n` mean value and the poly-log far arm

`FarL2`'s ⟦THE N-TERM REFUTATION⟧ names the obstruction precisely: the landed mean value
`MVCore2.dirichlet_poly_l2_mvt_final` charges `20·N` at the window LENGTH `N = ⌈X/y⌉₊ ≍ k/L⁴`,
and the `τ`-dyadic sum of the kernel's `1/τ²` weight turns that into `N·A/H²`, forcing
`H ≳ √k·L^{−3.24}` — worse than the standing `FarStar.Tstar`.

**THE REPAIR, in Lean.**  Split the window dyadically FIRST — a cut `P : ℕ → ℕ` with
`P 0 = 0`, `P` monotone, `J` blocks — apply the mean value PER BLOCK (where the Montgomery–
Vaughan constant is the block's own top `P (j+1)`, not the window's), and recombine by
Cauchy–Schwarz over the blocks at cost one factor `J`.  The `N`-term
`N·∑_n ‖aₙ‖²` is replaced by `J·∑_j P(j+1)·A_j` where `A_j` is the block's ℓ² mass — and at
the dyadic cut `P j ≍ 2^j y` with `‖λ_ℓ(n)‖ ≲ log n` each `P(j+1)·A_j ≍ (log X)²` while
`J ≍ L/log 2`, so the whole thing is `L⁴`-grade against `N·A ≍ k·L^{−8}` — **at the line
`σ = 1`.**  See ⟦THE LOW-LINE REFUTATION⟧ below for what happens at the line the chain
actually reads.

* **§1 — the block split.**  `blockCoeff` / `dpoly_eq_sum_blocks` — an `L2MVT.dpoly` at top
  `P J` is the sum over `j < J` of the block polynomials, each itself a `dpoly` at top
  `P (j+1)`.  Pure telescoping (`Finset.sum_Ioc_consecutive`).
* **§2 — THE DYADIC-IN-`n` MEAN VALUE.**  `dpoly_block_l2_mvt`:
  `∫_{−R}^{R} ‖dpoly (P J) a‖² ≤ J·∑_{j<J} (2R + 20·P(j+1))·A_j`.
  Cauchy–Schwarz over blocks (`sq_sum_le_card_mul_sum_sq`) + the landed mean value per block.
  The linear-in-`R` shape is preserved: slope `J·∑_j A_j`, intercept `20·J·∑_j P(j+1)·A_j`.
* **§3 — THE `τ`-LAYER CAKE.**  `far_weight_le_of_linear_growth`: for ANY nonnegative
  continuous `φ` with `∫_{−R}^{R} φ ≤ 2R·A + B` for every `R ≥ 0`,
  `∫_{|τ|>H} φ(τ)/τ² ≤ 8A/H + (4/3)·B/H²`.  Dyadic shells `H·2^i < |τ| ≤ H·2^{i+1}`,
  `MeasureTheory.integral_iUnion`, and two geometric series.  ONE named socket: the tail's
  own integrability (which is what `FarL2.crossKerFar_le_weighted_l2` already asks for).
* **§4 — THE PRICED TAIL.**  `winL2Tail_dyadic_le` — §2 and §3 composed at the window
  polynomial: `winL2Tail g X y σ H ≤ 8·J·A/H + (80/3)·J·Π/H²` with `A = winL2Mass` (the
  total ℓ² mass, NO `k`-power) and `Π = ∑_j P(j+1)·A_j` (the block price).
* **§5 — THE CLEARING THRESHOLD.**  `farL2_grade_clears_gate` (the
  `plog_floor_clears_gate` genre): the symbolic inequality that turns a poly-log `H` into the
  crown's currency `k·(log X)^{−1/(32e)}`.
* **§6 — THE COMPOSED FAR BOUND.**  `crossKerFar_polylog` — `crossKerFar_le_weighted_l2`
  (mass-free, landed) composed with §4, at any `H`, on the two carried integrability sockets.

## ⚠ ⟦THE LOW-LINE REFUTATION⟧ (design arithmetic, NOT kernel-checked; nothing below asserts it)

⟦THE N-TERM REPAIR⟧'s verified arithmetic (`FarL2`'s header) is read at the line `σ ≍ 1`,
where the block price is `∑_n ‖λ_ℓ(n)‖²/n^{2σ−1} = ∑_n (log n)²/n ≍ (log X)³/3 = L³` — a
convergent-by-a-hair, POLY-LOG quantity.  But the chain does not read `σ = 1`.  Its far
integrand is `‖W(c₀−β)‖·‖W(c₀+β)‖` with `β ∈ [0, η]`, `c₀ = 1 + 1/L`, `η = 1/log y`, and
`joint_cs_trunc_pinC`'s `hKfar` is a binder UNIFORM in `β`; so the price is read at the
LOWEST line `σ = c₀ − η`, where the exponent is

  `2σ − 1 = 1 − (2η − 2/L)`,

which is `< 1`.  The block price there is `≍ L²·k^{2(η−1/L)}/(2η − 2/L)`: it carries the
SQUARE of `FarStar` §3's `ℓ¹` excess `k^{η−1/L}`, and the `1/H²` denominator takes the square
root back out.  So §5's threshold at the honest line is

  `H ≳ k^{η−1/L}·L^{3/2}·√(log L)/√ε` — a `k`-power, NOT poly-log,

against `FarStar.Tstar = L⁴·k^{η}`.  Numerically (log-scale, `L = 10⁴`): the price's
`k`-power is `e^{541}`, its square root `e^{270}`, and `Tstar` is `e^{308}` — so the repair
sits a factor `≍ e·L^{5/2}` BELOW `Tstar` and is a genuine gain over both the refuted route
(`H ≳ √k`) and the standing pin, but it is a poly-log improvement of a `k`-power height, not
a poly-log height.  The `k`-power is intrinsic to the low line and is the same one `Tstar`
exists to pay: the AM–GM step of `crossKerFar_le_weighted_l2` symmetrises `‖W₋‖·‖W₊‖` into
`(‖W₋‖² + ‖W₊‖²)/2`, and a `τ`-Cauchy–Schwarz instead of AM–GM buys back only the square,
landing at the same `k^{η−1/L}`.

**What this file therefore claims.**  Every theorem below is symbolic in `winL2Mass` /
`winL2Price` and asserts NOTHING about their size; the `k`-power above is a statement about
what a consumer will find when it estimates them at the low line.  The genuine, unconditional
gains landed here are: the `N`-term is gone (`20·N·A → 20·J·Π`), the `A`-term is mass-free
and convergent at EVERY line in the band, and the whole far arm is now expressed at a FREE
height with `Tstar` nowhere in it.

## Traps observed

* **the `J`-count is `L`-grade.**  Everything here is stated with `J : ℕ` FREE; no lemma
  below assumes any relation between `J` and `k`.  The consumer picks `J ≍ log k/log 2`;
  nothing in this file can turn `J` into a `k`-power.
* **the five log scales.**  This file speaks NO logarithm of its own except inside `dpoly`'s
  own `Real.log n`.  `H` is a bare real; the poly-log pin is the consumer's word.
* **the block top, not the block length.**  `dirichlet_poly_l2_mvt_final`'s constant at a
  block `(P j, P (j+1)]` is `20·P (j+1)` — the TOP, because the Montgomery–Vaughan spacing
  `δ = 1/N` is read at the largest frequency present.  This is why the dyadic cut (top
  `≍ 2·`bottom) is the right one and an arithmetic-progression cut is not.
* **the sockets are honest.**  §3 asks `IntegrableOn (φ/τ²)` on the far region and §6 carries
  `FarL2.crossKerFar_le_weighted_l2`'s two; none is discharged here, and none is used to
  prove anything about the integrand's SIZE.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## §1 — the block split of a Dirichlet polynomial -/

/-- **THE BLOCK COEFFICIENT.**  `a` restricted to the `j`-th block `(P j, P (j+1)]` of the cut
`P`, extended by `0` — the shape `L2MVT.dpoly` at top `P (j+1)` demands. -/
def blockCoeff (a : ℕ → ℂ) (P : ℕ → ℕ) (j n : ℕ) : ℂ :=
  if P j < n ∧ n ≤ P (j + 1) then a n else 0

lemma blockCoeff_of_notMem {a : ℕ → ℂ} {P : ℕ → ℕ} {j n : ℕ}
    (h : n ∉ Finset.Ioc (P j) (P (j + 1))) : blockCoeff a P j n = 0 := by
  rw [Finset.mem_Ioc] at h
  unfold blockCoeff
  rw [if_neg h]

/-- The `j`-th block sits inside `dpoly`'s index set at top `P (j+1)`. -/
private lemma block_subset_Icc (P : ℕ → ℕ) (j : ℕ) :
    Finset.Ioc (P j) (P (j + 1)) ⊆ Finset.Icc 1 (P (j + 1)) := by
  intro n hn
  rw [Finset.mem_Ioc] at hn
  exact Finset.mem_Icc.mpr ⟨by omega, hn.2⟩

/-- The block polynomial IS the plain sum over the block. -/
lemma dpoly_block_eq (a : ℕ → ℂ) (P : ℕ → ℕ) (j : ℕ) (t : ℝ) :
    dpoly (P (j + 1)) (blockCoeff a P j) t
      = ∑ n ∈ Finset.Ioc (P j) (P (j + 1)),
          a n * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)) := by
  unfold dpoly
  rw [← Finset.sum_subset (block_subset_Icc P j)
    (fun n _ hn => by rw [blockCoeff_of_notMem hn]; ring)]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_Ioc] at hn
  unfold blockCoeff
  rw [if_pos hn]

/-- The telescoping of a monotone cut. -/
private lemma sum_Ioc_tele {M : Type*} [AddCommMonoid M] {P : ℕ → ℕ} (hmono : Monotone P)
    (f : ℕ → M) (J : ℕ) :
    ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (P j) (P (j + 1)), f n
      = ∑ n ∈ Finset.Ioc (P 0) (P J), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih,
        Finset.sum_Ioc_consecutive f (hmono (Nat.zero_le J)) (hmono (Nat.le_succ J))]

private lemma Ioc_zero_eq_Icc_one (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N := by
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

/-- **§1 EXIT — THE BLOCK SPLIT** (`dpoly_eq_sum_blocks`).  A Dirichlet polynomial at top
`P J` is the sum of its `J` block polynomials.  `P 0 = 0` and monotonicity are the only
hypotheses; the cut is otherwise free (the consumer picks the dyadic one). -/
theorem dpoly_eq_sum_blocks (a : ℕ → ℂ) {P : ℕ → ℕ} (hP0 : P 0 = 0) (hmono : Monotone P)
    (J : ℕ) (t : ℝ) :
    dpoly (P J) a t = ∑ j ∈ Finset.range J, dpoly (P (j + 1)) (blockCoeff a P j) t := by
  have hrw : ∀ j : ℕ, dpoly (P (j + 1)) (blockCoeff a P j) t
      = ∑ n ∈ Finset.Ioc (P j) (P (j + 1)),
          a n * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)) :=
    fun j => dpoly_block_eq a P j t
  simp only [hrw]
  rw [sum_Ioc_tele hmono
    (fun n => a n * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ))) J, hP0,
    Ioc_zero_eq_Icc_one]
  rfl

/-! ## §2 — THE DYADIC-IN-`n` MEAN VALUE -/

/-- **THE BLOCK ℓ² MASS.**  `∑_{P j < n ≤ P (j+1)} ‖aₙ‖²`. -/
def dpolyBlockMass (a : ℕ → ℂ) (P : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (P j) (P (j + 1)), ‖a n‖ ^ 2

lemma dpolyBlockMass_nonneg (a : ℕ → ℂ) (P : ℕ → ℕ) (j : ℕ) : 0 ≤ dpolyBlockMass a P j :=
  Finset.sum_nonneg (fun _ _ => by positivity)

/-- `dpoly`'s ℓ² charge at the block coefficient IS the block mass. -/
lemma blockCoeff_l2_eq (a : ℕ → ℂ) (P : ℕ → ℕ) (j : ℕ) :
    (∑ n ∈ Finset.Icc 1 (P (j + 1)), ‖blockCoeff a P j n‖ ^ 2) = dpolyBlockMass a P j := by
  unfold dpolyBlockMass
  rw [← Finset.sum_subset (block_subset_Icc P j)
    (fun n _ hn => by rw [blockCoeff_of_notMem hn]; simp)]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_Ioc] at hn
  unfold blockCoeff
  rw [if_pos hn]

/-- The pointwise Cauchy–Schwarz over the blocks — the ONE factor `J` the repair pays. -/
private lemma sq_norm_dpoly_le_blocks (a : ℕ → ℂ) {P : ℕ → ℕ} (hP0 : P 0 = 0)
    (hmono : Monotone P) (J : ℕ) (t : ℝ) :
    ‖dpoly (P J) a t‖ ^ 2
      ≤ (J : ℝ) * ∑ j ∈ Finset.range J, ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖ ^ 2 := by
  have hsplit := dpoly_eq_sum_blocks a hP0 hmono J t
  have h1 : ‖dpoly (P J) a t‖
      ≤ ∑ j ∈ Finset.range J, ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖ := by
    rw [hsplit]; exact norm_sum_le _ _
  have h2 : (∑ j ∈ Finset.range J, ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖) ^ 2
      ≤ (Finset.range J).card
          * ∑ j ∈ Finset.range J, ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_range] at h2
  have h0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range J, ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith [norm_nonneg (dpoly (P J) a t)]

/-- **§2 EXIT — THE DYADIC-IN-`n` MEAN VALUE** (`dpoly_block_l2_mvt`).  ⟦THE N-TERM REPAIR⟧:

  `∫_{−R}^{R} ‖dpoly (P J) a‖² ≤ J·∑_{j<J} (2R + 20·P(j+1))·A_j`,   `A_j` the block ℓ² mass.

The `20·N` of `dirichlet_poly_l2_mvt_final` at the WINDOW top is replaced by
`J·∑_j 20·P(j+1)·A_j`, which for a dyadic cut against a mass decaying like `1/n` is
`J·(number of blocks)·(log)²` rather than `N·A`.  No hypothesis relates `J` to anything. -/
theorem dpoly_block_l2_mvt (a : ℕ → ℂ) {P : ℕ → ℕ} (hP0 : P 0 = 0) (hmono : Monotone P)
    (J : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ t in (-R)..R, ‖dpoly (P J) a t‖ ^ 2)
      ≤ (J : ℝ) * ∑ j ∈ Finset.range J,
          (2 * R + 20 * (P (j + 1) : ℝ)) * dpolyBlockMass a P j := by
  have hRR : -R ≤ R := by linarith
  -- the two integrands are continuous
  have hcL : Continuous (fun t : ℝ => ‖dpoly (P J) a t‖ ^ 2) := by
    exact ((continuous_dpoly (P J) a).norm).pow 2
  have hcB : ∀ j : ℕ, Continuous (fun t : ℝ => ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖ ^ 2) :=
    fun j => ((continuous_dpoly (P (j + 1)) (blockCoeff a P j)).norm).pow 2
  have hcR : Continuous (fun t : ℝ =>
      (J : ℝ) * ∑ j ∈ Finset.range J, ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖ ^ 2) := by
    exact continuous_const.mul (continuous_finsetSum _ (fun j _ => hcB j))
  -- step 1: the pointwise Cauchy–Schwarz, integrated
  have hstep1 : (∫ t in (-R)..R, ‖dpoly (P J) a t‖ ^ 2)
      ≤ ∫ t in (-R)..R,
          (J : ℝ) * ∑ j ∈ Finset.range J, ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖ ^ 2 :=
    intervalIntegral.integral_mono_on hRR (hcL.intervalIntegrable _ _) (hcR.intervalIntegrable _ _)
      (fun t _ => sq_norm_dpoly_le_blocks a hP0 hmono J t)
  -- step 2: the constant and the finite sum come out
  have hstep2 : (∫ t in (-R)..R,
        (J : ℝ) * ∑ j ∈ Finset.range J, ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖ ^ 2)
      = (J : ℝ) * ∑ j ∈ Finset.range J,
          ∫ t in (-R)..R, ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖ ^ 2 := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_finsetSum (fun j _ => (hcB j).intervalIntegrable _ _)
  -- step 3: the landed mean value, per block
  have hstep3 : ∀ j : ℕ,
      (∫ t in (-R)..R, ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖ ^ 2)
        ≤ (2 * R + 20 * (P (j + 1) : ℝ)) * dpolyBlockMass a P j := by
    intro j
    have := dirichlet_poly_l2_mvt_final (P (j + 1)) (blockCoeff a P j) R
    rwa [blockCoeff_l2_eq a P j] at this
  have hstep4 : (J : ℝ) * ∑ j ∈ Finset.range J,
        ∫ t in (-R)..R, ‖dpoly (P (j + 1)) (blockCoeff a P j) t‖ ^ 2
      ≤ (J : ℝ) * ∑ j ∈ Finset.range J,
          (2 * R + 20 * (P (j + 1) : ℝ)) * dpolyBlockMass a P j := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hstep3 j))
      (Nat.cast_nonneg J)
  linarith [hstep1, hstep2 ▸ hstep1, hstep4]

/-! ## §3 — THE `τ`-LAYER CAKE

The second half of ⟦THE N-TERM REPAIR⟧: a linear-in-`R` mean value `∫_{−R}^{R} φ ≤ 2RA + B`
is converted into a `1/τ²`-weighted TAIL bound past height `H`, by summing over the dyadic
shells `H·2^i < |τ| ≤ H·2^{i+1}`.  Completely general in `φ`; the only analytic input is the
growth hypothesis, and the only socket is the tail's own integrability. -/

/-- The `i`-th dyadic shell of the far region `{|τ| > H}`. -/
private def farShell (H : ℝ) (i : ℕ) : Set ℝ :=
  {τ : ℝ | H * 2 ^ i < |τ| ∧ |τ| ≤ H * 2 ^ (i + 1)}

private lemma measurableSet_farShell (H : ℝ) (i : ℕ) : MeasurableSet (farShell H i) :=
  (measurableSet_farAbs (H * 2 ^ i)).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

private lemma farShell_disjoint {H : ℝ} (hH : 0 < H) {i j : ℕ} (hij : i < j) :
    Disjoint (farShell H i) (farShell H j) := by
  rw [Set.disjoint_left]
  intro τ hi hj
  obtain ⟨-, hi2⟩ := hi
  obtain ⟨hj1, -⟩ := hj
  have hmono : (2 : ℝ) ^ (i + 1) ≤ 2 ^ j :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have : H * 2 ^ (i + 1) ≤ H * 2 ^ j := mul_le_mul_of_nonneg_left hmono hH.le
  linarith

private lemma pairwise_disjoint_farShell {H : ℝ} (hH : 0 < H) :
    Pairwise (Function.onFun Disjoint (farShell H)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact farShell_disjoint hH h
  · exact (farShell_disjoint hH h).symm

private lemma iUnion_farShell {H : ℝ} (hH : 0 < H) :
    (⋃ i : ℕ, farShell H i) = {τ : ℝ | H < |τ|} := by
  classical
  ext τ
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, farShell]
  constructor
  · rintro ⟨i, h1, -⟩
    have h2 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    nlinarith
  · intro hτ
    have hex : ∃ i : ℕ, |τ| ≤ H * 2 ^ (i + 1) := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (|τ| / H) (by norm_num : (1 : ℝ) < 2)
      refine ⟨n, ?_⟩
      rw [div_lt_iff₀ hH] at hn
      have hstep : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith [hH.le]
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simpa using hτ
    · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hmin := Nat.find_min hex (m := m) (by omega)
      rw [hm]
      exact not_le.mp hmin

/-- The shell estimate: on `H·2^i < |τ| ≤ H·2^{i+1}` the weight `1/τ²` is at most
`1/(H·2^i)²`, and the mean value at `R = H·2^{i+1}` pays for the mass. -/
private lemma farShell_integral_le {φ : ℝ → ℝ} {A B H : ℝ} (i : ℕ)
    (hφ0 : ∀ τ, 0 ≤ φ τ) (hφc : Continuous φ)
    (hgrow : ∀ R : ℝ, 0 ≤ R → (∫ τ in (-R)..R, φ τ) ≤ 2 * R * A + B)
    (hH : 0 < H)
    (hInt : IntegrableOn (fun τ : ℝ => φ τ / τ ^ 2) (farShell H i)) :
    (∫ τ in farShell H i, φ τ / τ ^ 2)
      ≤ 4 * A / H * (1 / 2 : ℝ) ^ i + B / H ^ 2 * (1 / 4 : ℝ) ^ i := by
  set r : ℝ := H * 2 ^ i with hrdef
  set R : ℝ := H * 2 ^ (i + 1) with hRdef
  have h2i : (0 : ℝ) < 2 ^ i := by positivity
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hR0 : 0 < R := by rw [hRdef]; positivity
  have hRr : R = 2 * r := by rw [hRdef, hrdef, pow_succ]; ring
  -- the shell sits inside the symmetric interval of radius `R`
  have hsub : farShell H i ⊆ Set.Icc (-R) R := by
    intro τ hτ
    obtain ⟨-, h2⟩ := hτ
    rw [abs_le] at h2
    exact Set.mem_Icc.mpr ⟨h2.1, h2.2⟩
  have hφIcc : IntegrableOn φ (Set.Icc (-R) R) := hφc.continuousOn.integrableOn_Icc
  have hφsh : IntegrableOn φ (farShell H i) := hφIcc.mono_set hsub
  -- the weight is constant-dominated on the shell
  have h1 : (∫ τ in farShell H i, φ τ / τ ^ 2)
      ≤ ∫ τ in farShell H i, (1 / r ^ 2) * φ τ := by
    refine setIntegral_mono_on hInt (hφsh.const_mul _) (measurableSet_farShell H i)
      (fun τ hτ => ?_)
    obtain ⟨h1τ, -⟩ := hτ
    have hτ2 : r ^ 2 ≤ τ ^ 2 := by
      have : r ^ 2 ≤ |τ| ^ 2 := by nlinarith
      rwa [sq_abs] at this
    have : φ τ / τ ^ 2 ≤ φ τ / r ^ 2 :=
      div_le_div_of_nonneg_left (hφ0 τ) (by positivity) hτ2
    rw [one_div, inv_mul_eq_div]
    exact this
  have h2 : (∫ τ in farShell H i, (1 / r ^ 2) * φ τ)
      = (1 / r ^ 2) * ∫ τ in farShell H i, φ τ := integral_const_mul _ _
  have h3 : (∫ τ in farShell H i, φ τ) ≤ ∫ τ in Set.Icc (-R) R, φ τ :=
    setIntegral_mono_set hφIcc (Filter.Eventually.of_forall (fun τ => hφ0 τ))
      (HasSubset.Subset.eventuallyLE hsub)
  have h4 : (∫ τ in Set.Icc (-R) R, φ τ) = ∫ τ in (-R)..R, φ τ := by
    rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R), integral_Icc_eq_integral_Ioc]
  have h5 : (∫ τ in (-R)..R, φ τ) ≤ 2 * R * A + B := hgrow R hR0.le
  have hchain : (∫ τ in farShell H i, φ τ / τ ^ 2) ≤ (1 / r ^ 2) * (2 * R * A + B) := by
    have hpos : (0 : ℝ) < 1 / r ^ 2 := by positivity
    calc (∫ τ in farShell H i, φ τ / τ ^ 2)
        ≤ (1 / r ^ 2) * ∫ τ in farShell H i, φ τ := by rw [← h2]; exact h1
      _ ≤ (1 / r ^ 2) * (2 * R * A + B) := by
          refine mul_le_mul_of_nonneg_left ?_ hpos.le
          linarith [h3, h4 ▸ h3]
  refine hchain.trans (le_of_eq ?_)
  have h4i : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by
    rw [show (4 : ℝ) = 2 * 2 from by norm_num, mul_pow]
  rw [hRr, hrdef, div_pow, div_pow, h4i]
  field_simp
  ring

/-- **§3 EXIT — THE `τ`-LAYER CAKE** (`far_weight_le_of_linear_growth`).  For every
nonnegative continuous `φ` obeying the linear mean value `∫_{−R}^{R} φ ≤ 2RA + B` on every
symmetric range,

  `∫_{|τ| > H} φ(τ)/τ² ≤ 8·(A/H) + (4/3)·(B/H²)`.

The `A`-term is FREE (it is the `1/H` the far arm always had); the `B`-term is the one ⟦THE
N-TERM REFUTATION⟧ prices — and §2 has already replaced its `20N·A` by the block price.

`hInt` is a NAMED socket: exactly the integrability `FarL2.crossKerFar_le_weighted_l2`
already asks its consumers for, on the same set. -/
theorem far_weight_le_of_linear_growth {φ : ℝ → ℝ} {A B H : ℝ}
    (hφ0 : ∀ τ, 0 ≤ φ τ) (hφc : Continuous φ)
    (hgrow : ∀ R : ℝ, 0 ≤ R → (∫ τ in (-R)..R, φ τ) ≤ 2 * R * A + B)
    (hH : 0 < H)
    (hInt : IntegrableOn (fun τ : ℝ => φ τ / τ ^ 2) {τ : ℝ | H < |τ|}) :
    (∫ τ in {τ : ℝ | H < |τ|}, φ τ / τ ^ 2) ≤ 8 * (A / H) + (4 / 3) * (B / H ^ 2) := by
  classical
  have hUn := iUnion_farShell hH
  have hIntU : IntegrableOn (fun τ : ℝ => φ τ / τ ^ 2) (⋃ i : ℕ, farShell H i) := by
    rw [hUn]; exact hInt
  have hHS := hasSum_integral_iUnion (f := fun τ : ℝ => φ τ / τ ^ 2)
    (measurableSet_farShell H) (pairwise_disjoint_farShell hH) hIntU
  have hsummL : Summable (fun i : ℕ => ∫ τ in farShell H i, φ τ / τ ^ 2) := hHS.summable
  have hgeo2 : Summable (fun i : ℕ => 4 * A / H * (1 / 2 : ℝ) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hgeo4 : Summable (fun i : ℕ => B / H ^ 2 * (1 / 4 : ℝ) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hshell : ∀ i : ℕ, (∫ τ in farShell H i, φ τ / τ ^ 2)
      ≤ 4 * A / H * (1 / 2 : ℝ) ^ i + B / H ^ 2 * (1 / 4 : ℝ) ^ i := by
    intro i
    refine farShell_integral_le i hφ0 hφc hgrow hH (hInt.mono_set ?_)
    rw [← hUn]
    exact Set.subset_iUnion _ i
  have hle := hsummL.tsum_le_tsum hshell (hgeo2.add hgeo4)
  have hval : (∑' i : ℕ, (4 * A / H * (1 / 2 : ℝ) ^ i + B / H ^ 2 * (1 / 4 : ℝ) ^ i))
      = 8 * (A / H) + (4 / 3) * (B / H ^ 2) := by
    rw [hgeo2.tsum_add hgeo4, tsum_mul_left, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num),
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
    ring
  rw [← hUn, hHS.tsum_eq.symm]
  rw [← hval]
  exact hle

/-! ## §4 — THE PRICED TAIL: `winL2Tail` at a free height -/

/-- The total ℓ² mass is the sum of the block masses (the cut is a partition). -/
lemma sum_dpolyBlockMass_eq (a : ℕ → ℂ) {P : ℕ → ℕ} (hP0 : P 0 = 0) (hmono : Monotone P)
    (J : ℕ) :
    (∑ j ∈ Finset.range J, dpolyBlockMass a P j) = ∑ n ∈ Finset.Icc 1 (P J), ‖a n‖ ^ 2 := by
  unfold dpolyBlockMass
  rw [sum_Ioc_tele hmono (fun n => ‖a n‖ ^ 2) J, hP0, Ioc_zero_eq_Icc_one]

/-- **THE BLOCK PRICE `Π`.**  `∑_{j<J} P(j+1)·A_j` — the object that replaces
⟦THE N-TERM⟧'s `N·A`.  At the dyadic cut `P j ≍ 2^j y` against the window's own mass decay
this is `L`-many terms each of size `(log X)²`, whereas `N·A ≍ k·L^{−8}`. -/
def winL2Price (g : ℕ → ℂ) (X y σ : ℝ) (P : ℕ → ℕ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, (P (j + 1) : ℝ) * dpolyBlockMass (winL2Coeff g X y σ) P j

lemma winL2Price_nonneg (g : ℕ → ℂ) (X y σ : ℝ) (P : ℕ → ℕ) (J : ℕ) :
    0 ≤ winL2Price g X y σ P J :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (dpolyBlockMass_nonneg _ _ _))

/-- The window polynomial's `τ`-integral is continuous — the §3 input. -/
lemma continuous_windowSum_sq (g : ℕ → ℂ) (X y σ : ℝ) :
    Continuous (fun τ : ℝ => ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2) := by
  have hfun : (fun τ : ℝ => ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2)
      = fun τ : ℝ => ‖dpoly ⌈X / y⌉₊ (winL2Coeff g X y σ) (-τ)‖ ^ 2 := by
    funext τ; rw [windowSum_eq_dpoly]
  rw [hfun]
  exact (((continuous_dpoly _ _).comp continuous_neg).norm).pow 2

/-- **§4a — THE DYADIC-IN-`n` MEAN VALUE AT THE WINDOW** (`windowSum_l2_block_mvt`).
`windowSum_l2_mvt` with ⟦THE N-TERM⟧ repaired: the intercept is `20·J·Π` (the block price),
not `20·N·A` (the window length against the total mass).  The cut `P` is free apart from
`P 0 = 0`, monotonicity, and ending at the window top. -/
theorem windowSum_l2_block_mvt (g : ℕ → ℂ) (X y σ : ℝ) {P : ℕ → ℕ} (hP0 : P 0 = 0)
    (hmono : Monotone P) (J : ℕ) (hPJ : P J = ⌈X / y⌉₊) {R : ℝ} (hR : 0 ≤ R) :
    (∫ τ in (-R)..R, ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2)
      ≤ 2 * R * ((J : ℝ) * winL2Mass g X y σ)
        + 20 * ((J : ℝ) * winL2Price g X y σ P J) := by
  have hrw : (∫ τ in (-R)..R, ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2)
      = ∫ τ in (-R)..R, ‖dpoly (P J) (winL2Coeff g X y σ) τ‖ ^ 2 := by
    calc (∫ τ in (-R)..R, ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2)
        = ∫ τ in (-R)..R, ‖dpoly ⌈X / y⌉₊ (winL2Coeff g X y σ) (-τ)‖ ^ 2 := by
          refine intervalIntegral.integral_congr (fun τ _ => ?_)
          rw [windowSum_eq_dpoly]
      _ = ∫ τ in (-R)..(R : ℝ), ‖dpoly ⌈X / y⌉₊ (winL2Coeff g X y σ) τ‖ ^ 2 := by
          rw [intervalIntegral.integral_comp_neg
            (fun τ => ‖dpoly ⌈X / y⌉₊ (winL2Coeff g X y σ) τ‖ ^ 2), neg_neg]
      _ = ∫ τ in (-R)..R, ‖dpoly (P J) (winL2Coeff g X y σ) τ‖ ^ 2 := by rw [hPJ]
  rw [hrw]
  refine (dpoly_block_l2_mvt (winL2Coeff g X y σ) hP0 hmono J hR).trans (le_of_eq ?_)
  have hmass : (∑ j ∈ Finset.range J, dpolyBlockMass (winL2Coeff g X y σ) P j)
      = winL2Mass g X y σ := by
    rw [sum_dpolyBlockMass_eq (winL2Coeff g X y σ) hP0 hmono J, hPJ, winL2Coeff_l2_eq]
  have hexp : (∑ j ∈ Finset.range J, (2 * R + 20 * (P (j + 1) : ℝ))
        * dpolyBlockMass (winL2Coeff g X y σ) P j)
      = 2 * R * (∑ j ∈ Finset.range J, dpolyBlockMass (winL2Coeff g X y σ) P j)
        + 20 * winL2Price g X y σ P J := by
    unfold winL2Price
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hexp, hmass]
  ring

/-- **THE GRADED FAR TAIL.**  The `1/τ²`-weighted window tail's price past height `H` at the
cut `P` with `J` blocks: `8·J·A/H + (80/3)·J·Π/H²`, `A = winL2Mass`, `Π = winL2Price`. -/
def farL2Grade (g : ℕ → ℂ) (X y σ H : ℝ) (P : ℕ → ℕ) (J : ℕ) : ℝ :=
  8 * ((J : ℝ) * winL2Mass g X y σ / H)
    + (80 / 3) * ((J : ℝ) * winL2Price g X y σ P J / H ^ 2)

lemma farL2Grade_nonneg (g : ℕ → ℂ) (X y σ : ℝ) {H : ℝ} (hH : 0 < H) (P : ℕ → ℕ) (J : ℕ) :
    0 ≤ farL2Grade g X y σ H P J := by
  unfold farL2Grade
  have h1 := winL2Mass_nonneg g X y σ
  have h2 := winL2Price_nonneg g X y σ P J
  have hJ : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  positivity

/-- **§4 EXIT — ⟦THE N-TERM REPAIR⟧, LANDED** (`winL2Tail_dyadic_le`).

  `winL2Tail g X y σ H ≤ 8·J·A/H + (80/3)·J·Π/H²`

with `A = winL2Mass` (the total ℓ² mass — NO `k`-power, `FarL2` §11) and `Π = winL2Price`
(the block price).  §2 (the dyadic-in-`n` mean value) composed with §3 (the `τ`-layer cake).

This is the statement ⟦THE N-TERM REFUTATION⟧ says the scope's route needs: the `1/H²` term
now carries the block price instead of `N·A`, so a POLY-LOG `H` suffices wherever the block
price is poly-log.  The `J` is the block count and is `L`-grade at the dyadic cut; no lemma
here relates it to `k`.

`hInt` is the SAME named socket `FarL2.crossKerFar_le_weighted_l2` already carries. -/
theorem winL2Tail_dyadic_le (g : ℕ → ℂ) (X y σ : ℝ) {P : ℕ → ℕ} (hP0 : P 0 = 0)
    (hmono : Monotone P) (J : ℕ) (hPJ : P J = ⌈X / y⌉₊) {H : ℝ} (hH : 0 < H)
    (hInt : IntegrableOn
      (fun τ : ℝ => ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2 / τ ^ 2)
      {τ : ℝ | H < |τ|}) :
    winL2Tail g X y σ H ≤ farL2Grade g X y σ H P J := by
  have hmain := far_weight_le_of_linear_growth
    (φ := fun τ : ℝ => ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2)
    (A := (J : ℝ) * winL2Mass g X y σ)
    (B := 20 * ((J : ℝ) * winL2Price g X y σ P J))
    (fun τ => by positivity) (continuous_windowSum_sq g X y σ)
    (fun R hR => windowSum_l2_block_mvt g X y σ hP0 hmono J hPJ hR) hH hInt
  unfold winL2Tail farL2Grade
  refine hmain.trans (le_of_eq ?_)
  ring

/-! ## §5 — THE CLEARING THRESHOLD -/

/-- **THE POLY-LOG CLEARING THRESHOLD.**  The height at which the graded far tail drops below
a target budget `ε`, given grades `Ca` for `J·A` and `Cp` for `J·Π`:

  `Hthr = 16·Ca/ε + √(54·Cp/ε)`.

Both summands are individually sufficient for their own half of the budget (`8·Ca/H ≤ ε/2`
needs `H ≥ 16Ca/ε`; `(80/3)·Cp/H² ≤ ε/2` needs `H² ≥ (160/3)·Cp/ε`, and `54 ≥ 160/3`), so the
sum clears both.  **The grade of `Hthr` is entirely in `Ca`, `Cp`** — this lemma chooses
nothing.  `Ca` (the total ℓ² mass) is poly-log at every line of the band; `Cp` (the block
price) is poly-log at `σ ≍ 1` but carries `k^{2(η−1/L)}` at the band's LOW line `c₀ − η`, so
the honest threshold is `k^{η−1/L}`-grade rather than poly-log — see ⟦THE LOW-LINE
REFUTATION⟧ in the header.  Against the refuted route's `Hthr ≳ √k` this is still the whole
gain the repair was for. -/
def farL2Threshold (Ca Cp ε : ℝ) : ℝ := 16 * Ca / ε + Real.sqrt (54 * Cp / ε)

/-- **§5 EXIT — THE CLEARING GATE** (`farL2_grade_clears_gate`, the
`FarL2.plog_floor_clears_gate` genre).  At any height past `farL2Threshold`, the graded far
tail is inside the budget `ε`.  Purely symbolic: `Ca`, `Cp`, `ε` are the consumer's grades,
and no logarithm of any scale appears. -/
theorem farL2_grade_clears_gate (g : ℕ → ℂ) (X y σ : ℝ) (P : ℕ → ℕ) (J : ℕ)
    {Ca Cp ε H : ℝ} (hε : 0 < ε) (hCa : (J : ℝ) * winL2Mass g X y σ ≤ Ca) (hCa0 : 0 ≤ Ca)
    (hCp : (J : ℝ) * winL2Price g X y σ P J ≤ Cp) (hCp0 : 0 ≤ Cp)
    (hH : farL2Threshold Ca Cp ε ≤ H) (hH0 : 0 < H) :
    farL2Grade g X y σ H P J ≤ ε := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt (54 * Cp / ε) := Real.sqrt_nonneg _
  have hlin0 : (0 : ℝ) ≤ 16 * Ca / ε := by positivity
  have h1 : 16 * Ca / ε ≤ H := by
    have hthr := hH; unfold farL2Threshold at hthr; linarith
  have h2 : Real.sqrt (54 * Cp / ε) ≤ H := by
    have hthr := hH; unfold farL2Threshold at hthr; linarith
  -- the `A`-half
  have h1' : 16 * Ca ≤ H * ε := (div_le_iff₀ hε).mp h1
  have hA : 8 * ((J : ℝ) * winL2Mass g X y σ / H) ≤ ε / 2 := by
    have hkey : 8 * ((J : ℝ) * winL2Mass g X y σ / H)
        = 8 * ((J : ℝ) * winL2Mass g X y σ) / H := by ring
    rw [hkey, div_le_iff₀ hH0]
    linarith
  -- the `Π`-half
  have hP2 : 54 * Cp / ε ≤ H ^ 2 := by
    have hs : (0 : ℝ) ≤ 54 * Cp / ε := by positivity
    have hsq := Real.sq_sqrt hs
    nlinarith [Real.sqrt_nonneg (54 * Cp / ε)]
  have hP2' : 54 * Cp ≤ H ^ 2 * ε := (div_le_iff₀ hε).mp hP2
  have hB : (80 / 3) * ((J : ℝ) * winL2Price g X y σ P J / H ^ 2) ≤ ε / 2 := by
    have hH2 : (0 : ℝ) < H ^ 2 := by positivity
    have hkey : (80 / 3 : ℝ) * ((J : ℝ) * winL2Price g X y σ P J / H ^ 2)
        = (80 / 3 : ℝ) * ((J : ℝ) * winL2Price g X y σ P J) / H ^ 2 := by ring
    rw [hkey, div_le_iff₀ hH2]
    linarith
  unfold farL2Grade
  linarith

/-! ## §6 — THE COMPOSED FAR BOUND -/

/-- **§6 EXIT — THE FAR CROSS-INTEGRAL AT A FREE (POLY-LOG) HEIGHT** (`crossKerFar_polylog`).
`FarL2.crossKerFar_le_weighted_l2` (mass-free, landed) composed with §4:

  `crossKerFar g X h y c₀ t₀ α β H ≤ ((X+h)^{c+1}/h)·(grade(c₀−β) + grade(c₀+β))`,
  `c = c₀ − α − β`,

with each grade `8·J·A/H + (80/3)·J·Π/H²`.  The two integrability sockets are the landed
lemma's own, carried verbatim and NOT discharged; they are also exactly what §4 needs, so no
new socket is created by the composition. -/
theorem crossKerFar_polylog {g : ℕ → ℂ} {X h y c₀ t₀ α β H : ℝ} {P : ℕ → ℕ} {J : ℕ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c₀ - α - β) (hH : 0 < H)
    (hP0 : P 0 = 0) (hmono : Monotone P) (hPJ : P J = ⌈X / y⌉₊)
    (hIm : IntegrableOn
      (fun τ : ℝ => ‖windowSum g X y (((c₀ - β : ℝ) : ℂ) + (τ : ℝ) * I)‖ ^ 2 / τ ^ 2)
      {τ : ℝ | H < |τ|})
    (hIp : IntegrableOn
      (fun τ : ℝ => ‖windowSum g X y (((c₀ + β : ℝ) : ℂ) + (τ : ℝ) * I)‖ ^ 2 / τ ^ 2)
      {τ : ℝ | H < |τ|}) :
    crossKerFar g X h y c₀ t₀ α β H
      ≤ (X + h) ^ (c₀ - α - β + 1) / h
          * (farL2Grade g X y (c₀ - β) H P J + farL2Grade g X y (c₀ + β) H P J) := by
  have hXh : (0 : ℝ) < X + h := by linarith
  have hAmp : (0 : ℝ) ≤ (X + h) ^ (c₀ - α - β + 1) / h := by
    have := Real.rpow_pos_of_pos hXh (c₀ - α - β + 1); positivity
  refine (crossKerFar_le_weighted_l2 hX hh hc hH hIm hIp).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hAmp
  have h1 := winL2Tail_dyadic_le g X y (c₀ - β) hP0 hmono J hPJ hH hIm
  have h2 := winL2Tail_dyadic_le g X y (c₀ + β) hP0 hmono J hPJ hH hIp
  linarith

/-! ## §7 — THE `σ`-UNIFORM FAR BINDER (the re-pinned truncation twins' `hKfar`)

`GradeWindowC.joint_cs_trunc_pinC` asks for a `Kfar` UNIFORM over `α, β ∈ [0, η]`; §6's
bound is stated at the two moving lines `c₀ ∓ β`.  The bridge is monotonicity: every ℓ²
quantity here is antitone in `σ` (the coefficients carry `1/n^σ` at `n ≥ 1`), so the worst
line is the lowest one, `σ = c₀ − η`. -/

/-- The window coefficient's norm is antitone in the line `σ` (all indices are `≥ 1`). -/
lemma winL2Coeff_norm_antitone (g : ℕ → ℂ) (X y : ℝ) {σ σ' : ℝ} (hσ : σ ≤ σ') (n : ℕ) :
    ‖winL2Coeff g X y σ' n‖ ≤ ‖winL2Coeff g X y σ n‖ := by
  unfold winL2Coeff
  by_cases hn : n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊
  · rw [if_pos hn, if_pos hn]
    have hn1 : 1 ≤ n := by rw [Finset.mem_Ioo] at hn; omega
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hp : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by linarith) σ
    have hp' : (0 : ℝ) < (n : ℝ) ^ σ' := Real.rpow_pos_of_pos (by linarith) σ'
    have hle : (n : ℝ) ^ σ ≤ (n : ℝ) ^ σ' := Real.rpow_le_rpow_of_exponent_le hnR hσ
    rw [norm_div, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hp.le, Real.norm_of_nonneg hp'.le]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hp hle
  · rw [if_neg hn, if_neg hn]

/-- The total ℓ² mass is antitone in `σ`. -/
lemma winL2Mass_antitone (g : ℕ → ℂ) (X y : ℝ) {σ σ' : ℝ} (hσ : σ ≤ σ') :
    winL2Mass g X y σ' ≤ winL2Mass g X y σ := by
  unfold winL2Mass
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hn1 : 1 ≤ n := by rw [Finset.mem_Ioo] at hn; omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hp : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by linarith) σ
  have hle : (n : ℝ) ^ σ ≤ (n : ℝ) ^ σ' := Real.rpow_le_rpow_of_exponent_le hnR hσ
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

/-- The block price is antitone in `σ`. -/
lemma winL2Price_antitone (g : ℕ → ℂ) (X y : ℝ) {σ σ' : ℝ} (hσ : σ ≤ σ') (P : ℕ → ℕ)
    (J : ℕ) : winL2Price g X y σ' P J ≤ winL2Price g X y σ P J := by
  unfold winL2Price dpolyBlockMass
  refine Finset.sum_le_sum (fun j _ => ?_)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => ?_)) (Nat.cast_nonneg _)
  have := winL2Coeff_norm_antitone g X y hσ n
  have h0 := norm_nonneg (winL2Coeff g X y σ' n)
  nlinarith

/-- The graded far tail is antitone in `σ`. -/
lemma farL2Grade_antitone (g : ℕ → ℂ) (X y : ℝ) {σ σ' : ℝ} (hσ : σ ≤ σ') {H : ℝ} (hH : 0 < H)
    (P : ℕ → ℕ) (J : ℕ) : farL2Grade g X y σ' H P J ≤ farL2Grade g X y σ H P J := by
  unfold farL2Grade
  have hJ : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  have hm := winL2Mass_antitone g X y hσ
  have hp := winL2Price_antitone g X y hσ P J
  have hH2 : (0 : ℝ) < H ^ 2 := by positivity
  have hHinv : (0 : ℝ) ≤ 1 / H := one_div_nonneg.mpr hH.le
  have hH2inv : (0 : ℝ) ≤ 1 / H ^ 2 := one_div_nonneg.mpr hH2.le
  have e1 : (J : ℝ) * winL2Mass g X y σ' / H ≤ (J : ℝ) * winL2Mass g X y σ / H := by
    calc (J : ℝ) * winL2Mass g X y σ' / H = ((J : ℝ) * winL2Mass g X y σ') * (1 / H) := by
          ring
      _ ≤ ((J : ℝ) * winL2Mass g X y σ) * (1 / H) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hJ) hHinv
      _ = (J : ℝ) * winL2Mass g X y σ / H := by ring
  have e2 : (J : ℝ) * winL2Price g X y σ' P J / H ^ 2
      ≤ (J : ℝ) * winL2Price g X y σ P J / H ^ 2 := by
    calc (J : ℝ) * winL2Price g X y σ' P J / H ^ 2
        = ((J : ℝ) * winL2Price g X y σ' P J) * (1 / H ^ 2) := by ring
      _ ≤ ((J : ℝ) * winL2Price g X y σ P J) * (1 / H ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hJ) hH2inv
      _ = (J : ℝ) * winL2Price g X y σ P J / H ^ 2 := by ring
  linarith

/-- **§7 EXIT — THE `hKfar` BINDER AT A FREE (POLY-LOG) HEIGHT**
(`crossKerFar_polylog_uniform`).  Exactly the shape
`GradeWindowC.joint_cs_trunc_pinC` / `rhs_grade_at_scale_windowC` consume, with
`FarStar.far_kernel_bound_star`'s `T := Tstar` replaced by a FREE `H` and its two ℓ¹ window
masses replaced by the single ℓ²-graded tail read at the worst line `c₀ − η`.

The integrability socket is stated once, for the whole line band `[c₀ − η, c₀ + η]` — the
`α, β`-uniform version of `FarL2.crossKerFar_le_weighted_l2`'s two, and it is CARRIED, not
discharged. -/
theorem crossKerFar_polylog_uniform {g : ℕ → ℂ} {X h y c₀ t₀ η H : ℝ} {P : ℕ → ℕ} {J : ℕ}
    (hX : 1 ≤ X) (hh : 0 < h) (hη0 : 0 ≤ η) (hc : 0 < c₀ - 2 * η) (hH : 0 < H)
    (hP0 : P 0 = 0) (hmono : Monotone P) (hPJ : P J = ⌈X / y⌉₊)
    (hInt : ∀ σ : ℝ, c₀ - η ≤ σ → σ ≤ c₀ + η →
      IntegrableOn (fun τ : ℝ => ‖windowSum g X y ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2 / τ ^ 2)
        {τ : ℝ | H < |τ|}) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar g X h y c₀ t₀ α β H
        ≤ (X + h) ^ (c₀ + 1) / h * (2 * farL2Grade g X y (c₀ - η) H P J) := by
  intro α hα β hβ
  obtain ⟨hα0, hαη⟩ := hα
  obtain ⟨hβ0, hβη⟩ := hβ
  have hXh1 : (1 : ℝ) ≤ X + h := by linarith
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hcαβ : 0 < c₀ - α - β := by linarith
  have hIm := hInt (c₀ - β) (by linarith) (by linarith)
  have hIp := hInt (c₀ + β) (by linarith) (by linarith)
  refine (crossKerFar_polylog hX hh hcαβ hH hP0 hmono hPJ hIm hIp).trans ?_
  have hamp : (X + h) ^ (c₀ - α - β + 1) / h ≤ (X + h) ^ (c₀ + 1) / h := by
    have hle := Real.rpow_le_rpow_of_exponent_le hXh1 (by linarith : c₀ - α - β + 1 ≤ c₀ + 1)
    have hhinv : (0 : ℝ) ≤ 1 / h := one_div_nonneg.mpr hh.le
    calc (X + h) ^ (c₀ - α - β + 1) / h = (X + h) ^ (c₀ - α - β + 1) * (1 / h) := by ring
      _ ≤ (X + h) ^ (c₀ + 1) * (1 / h) := mul_le_mul_of_nonneg_right hle hhinv
      _ = (X + h) ^ (c₀ + 1) / h := by ring
  have hg1 : farL2Grade g X y (c₀ - β) H P J ≤ farL2Grade g X y (c₀ - η) H P J :=
    farL2Grade_antitone g X y (by linarith) hH P J
  have hg2 : farL2Grade g X y (c₀ + β) H P J ≤ farL2Grade g X y (c₀ - η) H P J :=
    farL2Grade_antitone g X y (by linarith) hH P J
  have hgr0 : 0 ≤ farL2Grade g X y (c₀ - β) H P J + farL2Grade g X y (c₀ + β) H P J := by
    have := farL2Grade_nonneg g X y (c₀ - β) hH P J
    have := farL2Grade_nonneg g X y (c₀ + β) hH P J
    linarith
  have hamp0 : (0 : ℝ) ≤ (X + h) ^ (c₀ - α - β + 1) / h := by
    have := Real.rpow_pos_of_pos hXh0 (c₀ - α - β + 1); positivity
  exact mul_le_mul hamp (by linarith) hgr0 (by
    have := Real.rpow_pos_of_pos hXh0 (c₀ + 1); positivity)

/-! ## §8 — THE RE-PINNED TRUNCATION TWIN (STEP 3)

`GradeWindowC.joint_supF_pin_windowC` and `joint_cs_trunc_pinC` are already stated at a FREE
truncation height `T`; what `FarL2`'s R1 page could not supply was an INHABITANT of their
`hKfar` binder at a poly-log `T` (`FarStar.far_kernel_bound_star` lives only at `Tstar`).
§7 is that inhabitant, so the twins below are non-vacuous at any `H > 0`. -/

private lemma fl2_log64 : (4 : ℝ) ≤ Real.log 64 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hle : Real.exp 4 ≤ 64 := by
    have hsq : Real.exp 1 * Real.exp 1 ≤ 8 := by nlinarith
    have hp2 : (0 : ℝ) < Real.exp 1 * Real.exp 1 := by positivity
    rw [h4, h2]
    nlinarith
  rw [← Real.log_exp 4]
  exact Real.log_le_log (Real.exp_pos 4) hle

/-- The pin's gates, in the form §7 consumes (`1 ≤ k`, `0 < η ≤ 1/16`, `0 < c₀ − 2η`). -/
private lemma fl2_pin_gates {k L y η c₀ : ℝ} (hk : Real.exp 64 ≤ k) (hL : L = Real.log k)
    (hy : y = L ^ 4) (hη : η = 1 / Real.log y) (hc₀ : c₀ = 1 + 1 / L) :
    1 ≤ k ∧ 64 ≤ L ∧ 0 < η ∧ η ≤ 1 / 16 ∧ 0 < c₀ - 2 * η := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hk1 : (1 : ℝ) ≤ k := by
    have : (1 : ℝ) ≤ Real.exp 64 := Real.one_le_exp (by norm_num)
    linarith
  have hL64 : (64 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogL : (4 : ℝ) ≤ Real.log L :=
    le_trans fl2_log64 (Real.log_le_log (by norm_num) hL64)
  have hlogy : Real.log y = 4 * Real.log L := by
    rw [hy, Real.log_pow]; norm_num
  have hlogy16 : (16 : ℝ) ≤ Real.log y := by rw [hlogy]; linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη16 : η ≤ 1 / 16 := by
    rw [hη]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  refine ⟨hk1, hL64, hη0, hη16, ?_⟩
  have h1L : (0 : ℝ) < 1 / L := by positivity
  rw [hc₀]; linarith

/-- **§8 EXIT — THE TRUNCATED JOINT FACTORING AT THE POLY-LOG PIN**
(`joint_cs_trunc_polylog`).  `GradeWindowC.joint_cs_trunc_pinC` at `T := H` with its `hKfar`
binder DISCHARGED by §7 — the twin `FarL2`'s R1 page deliberately did not write, now
non-vacuous.  Everything else (the window floor `hMwin`, the far sup `hFar`, the joint
integrability) is threaded verbatim.  The far kernel's price is the ℓ²-graded
`(k+h)^{c₀+1}/h · 2·grade(c₀−η)` — NO ℓ¹ window mass, hence no `k^{1/(4 log L)}`. -/
theorem joint_cs_trunc_polylog {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀' M k L c₀ y η h H Ffar : ℝ} {P : ℕ → ℕ} {J : ℕ}
    (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀eq : c₀ = 1 + 1 / L) (hh0 : 0 < h) (hH : 0 < H)
    (hP0 : P 0 = 0) (hmono : Monotone P) (hPJ : P J = ⌈k / y⌉₊)
    (hMwin : ∀ t : ℝ, |t - t₀'| ≤ H →
      M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k)
    (hFfar0 : 0 ≤ Ffar)
    (hFar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar)
    (hIntFar : ∀ σ : ℝ, c₀ - η ≤ σ → σ ≤ c₀ + η →
      IntegrableOn (fun τ : ℝ =>
        ‖windowSum (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k y
          ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2 / τ ^ 2) {τ : ℝ | H < |τ|})
    (hInt : JointIntegrableAtC c (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
      t₀' M k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' k h c₀ y η‖
      ≤ (1 / Real.pi) * (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
            rhsFboundC c M L (β + 1 / L)
              * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β)
        + (1 / Real.pi) * (η ^ 2 * (Ffar
            * ((k + h) ^ (c₀ + 1) / h
                * (2 * farL2Grade (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
                      k y (c₀ - η) H P J)))) := by
  obtain ⟨hk1, hL64, hη0, hη16, hcgate⟩ := fl2_pin_gates hk hL hy hη hc₀eq
  have hKfar := crossKerFar_polylog_uniform
    (g := fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) (X := k) (h := h) (y := y)
    (c₀ := c₀) (t₀ := t₀') (η := η) (H := H) (P := P) (J := J)
    hk1 hh0 hη0.le hcgate hH hP0 hmono hPJ hIntFar
  exact joint_cs_trunc_pinC hg hc0 hce hk hL hy hη hc₀eq hh0 hMwin hFfar0 hFar hKfar hInt

/-! ## §9 — THE DILATED-SCALE TWIN AT THE POLY-LOG RADIUS (STEP 4) -/

/-- **THE ℓ²-GRADED `Kfar` AT A FREE HEIGHT** — `FarStar.farKfarStar`'s replacement.  The
amplitude `(k+h)^{c₀+1}/h` at the pin's own width `h = k/√L`, against `2·` the graded far
tail read at the worst line `c₀ − η`.  No ℓ¹ window mass, hence NO `k^{1/(4 log L)}`. -/
def farKfarPolylog (d : ℕ → ℂ) (k H : ℝ) (P : ℕ → ℕ) (J : ℕ) : ℝ :=
  (k + k / Real.sqrt (Real.log k)) ^ (1 + 1 / Real.log k + 1) / (k / Real.sqrt (Real.log k))
    * (2 * farL2Grade d k (Real.log k ^ 4)
        (1 + 1 / Real.log k - 1 / Real.log (Real.log k ^ 4)) H P J)

/-- **§9 EXIT — THE DILATED-SCALE GRADE AT THE POLY-LOG PIN**
(`dilated_scale_grade_polylog`).  `SPartStation.dilated_scale_grade` with `FarStar.Tstar`
swapped for a FREE height `H`: the gate is `|t₁| + H ≤ Rad`, the window floor is transported
by `pretDistSq_floor_dilate` exactly as before, and the far arm rides ADDITIVELY at the
ℓ²-graded `farKfarPolylog` instead of `farCStar·k·(log X)^{−1/(32e)}`.

**What the swap costs.**  `Tstar` enters `dilated_scale_grade` in exactly two places — the
gate/window pair (`hgate`, `hMwin`) and the far pair (`far_kernel_bound_star`, `hfar_star`).
The first is a clean transplant (nothing else in the body reads the height); the second is
where the pricing lives, and it is CARRIED here rather than discharged: turning
`farKfarPolylog` into the crown's currency needs the datum-level ℓ² mass estimate
(`∑_n ‖λ_ℓ(n)‖²/n^{2σ}` per dyadic block), which this file does not land.  §5's
`farL2_grade_clears_gate` is the gate that estimate feeds. -/
theorem dilated_scale_grade_polylog {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c Cb t₀ t₁ X Xd M₀ Rad H : ℝ} {k : ℕ} {P : ℕ → ℕ} {J : ℕ}
    (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1) (hc1 : 2 * c < 1)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk64 : Real.exp 64 ≤ (k : ℝ))
    (hXd2 : 2 ≤ Xd) (hXdX : Xd ≤ X) (hkXd : Xd ≤ (k : ℝ))
    (hH : 0 < H)
    (hgate : |t₁| + H ≤ Rad)
    (hM₀ : ∀ v : ℝ, |v| ≤ Rad →
      M₀ ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hP0 : P 0 = 0) (hmono : Monotone P)
    (hPJ : P J = ⌈(k : ℝ) / Real.log (k : ℝ) ^ 4⌉₊)
    (hIntFar : ∀ σ : ℝ,
      1 + 1 / Real.log (k : ℝ) - 1 / Real.log (Real.log (k : ℝ) ^ 4) ≤ σ →
      σ ≤ 1 + 1 / Real.log (k : ℝ) + 1 / Real.log (Real.log (k : ℝ) ^ 4) →
      IntegrableOn (fun τ : ℝ =>
        ‖windowSum (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (k : ℝ)
          (Real.log (k : ℝ) ^ 4) ((σ : ℂ) + (τ : ℝ) * I)‖ ^ 2 / τ ^ 2)
        {τ : ℝ | H < |τ|}) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
        (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
        (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
      ≤ gradeAbsConstC c Cb * (k : ℝ) * Real.exp (-c * (M₀ - dilGap X Xd))
        + (1 / Real.pi) * ((1 / Real.log (Real.log (k : ℝ) ^ 4)) ^ 2
            * (farFbound (Real.log (k : ℝ))
                * farKfarPolylog (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
                    (k : ℝ) H P J)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 64) hk64
  have hLk64 : (64 : ℝ) ≤ Real.log (k : ℝ) := by
    rw [← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk64
  have hLk0 : (0 : ℝ) < Real.log (k : ℝ) := by linarith
  have hk3 : Real.exp 3 ≤ (k : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hk64
  obtain ⟨hk1, -, hη0, hη16, hcgate⟩ := fl2_pin_gates (k := (k : ℝ))
    (L := Real.log (k : ℝ)) (y := Real.log (k : ℝ) ^ 4)
    (η := 1 / Real.log (Real.log (k : ℝ) ^ 4)) (c₀ := 1 + 1 / Real.log (k : ℝ))
    hk64 rfl rfl rfl rfl
  have hgtw : ∀ p, p.Prime →
      ‖(fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist (t₀ + t₁) hp.one_lt.le, mul_one]
    exact hg p hp
  have hEll : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := ellLin_norm_le_one g hg
  set M : ℝ := max 0 (M₀ - dilGap X Xd) with hMdef
  have hM0 : (0 : ℝ) ≤ M := le_max_left _ _
  have hMlb : M₀ - dilGap X Xd ≤ M := le_max_right _ _
  have hh0 : (0 : ℝ) < (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by
    have : (0 : ℝ) < Real.sqrt (Real.log (k : ℝ)) := Real.sqrt_pos.mpr hLk0
    positivity
  -- THE WINDOW FLOOR at the dilated scale, at the poly-log window `H`
  have hMwin : ∀ t : ℝ, |t - (t₀ + t₁)| ≤ H →
      M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)))
        (costwist (t - (t₀ + t₁))) (k : ℝ) := by
    intro t ht
    have hshift := twisted_datum_dist_eq g (t₀ + t₁) (t - (t₀ + t₁)) (k : ℝ)
    rw [show t - (t₀ + t₁) + (t₀ + t₁) = t from by ring] at hshift
    rw [hshift]
    refine max_le (pretDistSq_nonneg _ _ _ hEll (fun n => le_of_eq (costwist_norm t n))) ?_
    have habs : |t - t₀| ≤ Rad := by
      have h1 : |t - t₀| ≤ |t - (t₀ + t₁)| + |t₁| := by
        have : t - t₀ = (t - (t₀ + t₁)) + t₁ := by ring
        rw [this]
        exact abs_add_le _ _
      linarith
    have hfl := hM₀ (t - t₀) habs
    rw [seamCoeff_trivial_dist_eq, show t - t₀ + t₀ = t from by ring] at hfl
    exact pretDistSq_floor_dilate hEll (fun n => le_of_eq (costwist_norm t n))
      hXd2 hXdX hkXd hfl
  -- the far arm at the ℓ² grade
  have hFfar0 : (0 : ℝ) ≤ farFbound (Real.log (k : ℝ)) := farFbound_nonneg hLk0.le
  have hFar := far_supF_bound hg (t₀' := t₀ + t₁) hk3 (rfl : Real.log (k : ℝ) = _)
    (rfl : Real.log (k : ℝ) ^ 4 = _) (rfl : 1 / Real.log (Real.log (k : ℝ) ^ 4) = _)
    (rfl : 1 + 1 / Real.log (k : ℝ) = _)
  have hKfar := crossKerFar_polylog_uniform
    (g := fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (X := (k : ℝ))
    (h := (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (y := Real.log (k : ℝ) ^ 4)
    (c₀ := 1 + 1 / Real.log (k : ℝ)) (t₀ := t₀ + t₁)
    (η := 1 / Real.log (Real.log (k : ℝ) ^ 4)) (H := H) (P := P) (J := J)
    hk1 hh0 hη0.le hcgate hH hP0 hmono hPJ hIntFar
  have hInt := jointIntegrableAtC_pin_free hg c (t₀ + t₁) M hk64
  have hmain := rhs_grade_at_scale_windowC hg hc0 hce hc1 hCb0 hCbound hk64
    (rfl : Real.log (k : ℝ) = _) (rfl : Real.log (k : ℝ) ^ 4 = _)
    (rfl : 1 / Real.log (Real.log (k : ℝ) ^ 4) = _) (rfl : 1 + 1 / Real.log (k : ℝ) = _)
    (rfl : (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) = _) hM0 hMwin hFfar0 hFar hKfar hInt
  -- the exponent: the `max` only strengthens
  have hexp : Real.exp (-c * M) ≤ Real.exp (-c * (M₀ - dilGap X Xd)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hC0 : (0 : ℝ) ≤ gradeAbsConstC c Cb * (k : ℝ) :=
    mul_nonneg (gradeAbsConstC_nonneg hc1 hCb0) hk0.le
  have hstep : gradeAbsConstC c Cb * (k : ℝ) * Real.exp (-c * M)
      ≤ gradeAbsConstC c Cb * (k : ℝ) * Real.exp (-c * (M₀ - dilGap X Xd)) :=
    mul_le_mul_of_nonneg_left hexp hC0
  unfold farKfarPolylog
  linarith

end Salt.MR
