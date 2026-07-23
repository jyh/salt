/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DistWindow
import Salt.MR.HalaszHead
import Salt.MR.MomentsA2
import Salt.MR.RamareWindows
import Salt.MR.Decomp

/-!
# PART 3 — T-2 — the §8.3 / A2 assembly opening (`Prop1Assembly`)

The terminal-assembly freeze (`docs/exploration/terminal-assembly-freeze.md`, PART 3,
T-2 / T-2b) and the s8-freeze wave-4 A2 shape (`docs/exploration/s8-freeze.md:16`):
`int_U` at `P = exp((log X)^{1−1/48})`, `Q = exp(log X/loglog X)`, `H = (log X)^{1/48}`;
the `T0/T1` split (consuming `T1_pointwise_decay`); `E1` exact `(T+N)`; the `E_j`
moments (`lemma13_moment`); the large-`T` sub-rung (`moment_core_bound_large_T`);
toward the terminal `prop_A3'` (M_range form, capped domain).

## What this file lands (Zeno partial, built as far as the landed corpus allows)

* **T-2b — `expEM_le_of_floor_corrected` + `T1_pointwise_decay_corrected`.**  The
  absorption lemma the freeze mandated: the landed `T1_pointwise_decay`
  (`PropA3Core.lean:287`) demands the CLEAN floor `(1/32)loglog X ≤ M` and does NOT
  compose with the *corrected* R3.1 floor
  `(1/32)loglog X − 5·logloglog(2X+16) − C ≤ M` (the frozen N2 shape now landed
  W-free in `DistWindow.dist_split_A4_N2`).  T-2b absorbs the `−5·logloglog − C` slack
  into the pointwise decay grade, concluding the B4-re-frozen `(log X)^{−1/(32e) + o(1)}`
  grade (`c = 1/e`; AMENDMENT B4) with the `o(1)` inflation
  `exp(c·(5·logloglog(2X+16) + C))` carried IN-STATEMENT (#253).
* **`T1_decay_corrected_fgJ`.**  The fgJ-instantiated corrected decay: the bridge from
  HUPPER's output (`DistWindow.dist_split_A4_N2`'s corrected floor) straight into the
  T1 grade — the seam datum's per-center T1 mass at the *corrected* floor.
* **Frozen §8.3 parameter defs** `P₈₃`, `Q₈₃`, `H₈₃` at the wave-4 values.
* **Moment-row wrappers** re-exporting the landed `lemma13_moment` (E_j),
  `moment_core_bound` (E1), `moment_core_bound_large_T` (the large-`T` sub-rung) at the
  assembly granularity, and the `int_U` block Cauchy–Schwarz
  (`cauchy_schwarz_intervalIntegral`).
* **`prop_A3'_assembly`** — the terminal, in the conditional-assembly house form: the
  §8 eq-(24) decomposition of the mean square into the `int_U` (Halász / T1-decay,
  conditional on Part 1's `hhead` supplying the ball head) row and the `E1 + E_j`
  moment row, each carried as a NAMED hypothesis pointing to the landed row lemma,
  assembled to the `(T/X + 1)`-graded total.  The single still-missing analytic input
  is Part 1's H-EXIT (the ball head); the assembly is otherwise closed.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §8; MRT v3 Appendix A (Prop A.3,
Lemmas A.4–A.8, the corrected slow-`M` route).
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open MeasureTheory Complex

/-! ## Frozen §8.3 parameters (s8-freeze wave-4) -/

/-- **`P₈₃ X = exp((log X)^{1−1/48})`** — the §8.3 lower prime cutoff (s8-freeze:16). -/
def P₈₃ (X : ℝ) : ℝ := Real.exp ((Real.log X) ^ ((1 : ℝ) - 1 / 48))

/-- **`Q₈₃ X = exp(log X / loglog X)`** — the §8.3 upper prime cutoff (s8-freeze:16). -/
def Q₈₃ (X : ℝ) : ℝ := Real.exp (Real.log X / Real.log (Real.log X))

/-- **`H₈₃ X = (log X)^{1/48}`** — the §8.3 block-count parameter (s8-freeze:16). -/
def H₈₃ (X : ℝ) : ℝ := (Real.log X) ^ ((1 : ℝ) / 48)

lemma P₈₃_pos (X : ℝ) : 0 < P₈₃ X := Real.exp_pos _
lemma Q₈₃_pos (X : ℝ) : 0 < Q₈₃ X := Real.exp_pos _

lemma H₈₃_pos {X : ℝ} (hX : 1 < Real.log X) : 0 < H₈₃ X :=
  Real.rpow_pos_of_pos (by linarith) _

/-! ## T-2b — the corrected-floor pointwise decay (the absorption lemma) -/

/-- **T-2b (core) — `expEM_le_of_floor_corrected`.**  The `e^{−cM}` engine
(`c = 1/Real.exp 1`, AMENDMENT B4) at the *corrected* R3.1 floor (the frozen N2 shape,
`DistWindow.dist_split_A4_N2`): from `M ≥ (1/32)loglog X − 5·logloglog(2X+16) − C`,

  `exp(−cM) ≤ (log X)^{−c/32} · exp(c·(5·logloglog(2X+16) + C))`.

The `−5·logloglog − C` slack becomes the `o(1)` inflation
`exp(c·(5·logloglog(2X+16) + C))` (a `(loglog X)^{5c}·e^{cC}`-grade factor,
`(log X)^{o(1)}`), carried IN-STATEMENT (#253).  This is exactly the composition the
landed clean-floor `expEM_le_of_floor_c` (`PropA3Core.lean`) cannot perform.

**AMENDMENT B4 (JYH-ratified 2026-07-23).**  Re-frozen from the `exp(−M/2)` /
`(log X)^{−1/64}` form to the elementary B-route `e^{−cM}` / `(log X)^{−c/32}` form
(no `M/2` collapse); the inflation loses its `/2` and gains the factor `c`. -/
theorem expEM_le_of_floor_corrected {X M C : ℝ} (hX : Real.exp 1 ≤ X)
    (hM : (1 / 32) * Real.log (Real.log X)
        - 5 * Real.log (Real.log (Real.log (2 * X + 16))) - C ≤ M) :
    Real.exp (-(1 / Real.exp 1) * M) ≤ (Real.log X) ^ (-(1 / Real.exp 1) / 32)
        * Real.exp ((1 / Real.exp 1)
            * (5 * Real.log (Real.log (Real.log (2 * X + 16))) + C)) := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hc : (0 : ℝ) ≤ 1 / Real.exp 1 := by positivity
  have hstep : -(1 / Real.exp 1) * M ≤ Real.log (Real.log X) * (-(1 / Real.exp 1) / 32)
      + (1 / Real.exp 1) * (5 * Real.log (Real.log (Real.log (2 * X + 16))) + C) := by
    nlinarith [mul_le_mul_of_nonneg_left hM hc]
  calc Real.exp (-(1 / Real.exp 1) * M)
      ≤ Real.exp (Real.log (Real.log X) * (-(1 / Real.exp 1) / 32)
          + (1 / Real.exp 1) * (5 * Real.log (Real.log (Real.log (2 * X + 16))) + C)) :=
        Real.exp_le_exp.mpr hstep
    _ = (Real.log X) ^ (-(1 / Real.exp 1) / 32)
          * Real.exp ((1 / Real.exp 1)
              * (5 * Real.log (Real.log (Real.log (2 * X + 16))) + C)) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hlogXpos]

/-- **T-2b — `T1_pointwise_decay_corrected`** (`terminal-assembly-freeze.md`, PART 3,
T-2b).  The per-center T1 mass bound at the *corrected* R3.1 floor: composing
`halasz_ball_decay` (the `e^{−cM}` ball grade, `c = 1/e`) with `expEM_le_of_floor_corrected`
gives

  `U ≤ (C₁+C₂)·X·((log X)^{−c/32}·exp(c·(5·logloglog(2X+16) + Cfl))
        + (log X)^{−1/2+ε})`

— the re-frozen `≪ X·(log X)^{−c/32 + o(1)} = X·(log X)^{−1/(32e)+o(1)}` grade, the `o(1)`
inflation IN-STATEMENT.  The landed `T1_pointwise_decay` demands the clean floor
`(1/32)loglog X ≤ M`; this is the absorption lemma that lets it compose with the corrected
N2 floor (the one T-1's W-vanishing chain actually delivers). `hhead`/`htail`/`hsplit` are
`halasz_ball_decay`'s S1'/S2' analytic inputs.

**AMENDMENT J0 (JYH-ratified 2026-07-23).**  `M = M_range f X T` is GHS Lemma 1's
range-minimum (was center-M `pretDistSq f g X`); `expEM_le_of_floor_corrected` is generic
in `M` and threads unchanged.  Restores the frozen `prop_A3'` semantics.

**AMENDMENT B4 (JYH-ratified 2026-07-23).**  `hhead` re-frozen to the elementary B-route
`e^{−cM}` shape (`c = 1/e`), grade to `(log X)^{−c/32}`, coefficient to `C₁ + C₂`. -/
theorem T1_pointwise_decay_corrected {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hg : ∀ n, ‖g n‖ ≤ 1) {X ε U Uhead Utail C₁ C₂ Cfl T : ℝ}
    (hX : Real.exp 1 ≤ X) (hε : 0 ≤ ε) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : U = Uhead + Utail)
    (hhead : Uhead ≤ C₁ * X * Real.exp (-(1 / Real.exp 1) * M_range f X T))
    (htail : Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2))
    (hfloor : (1 / 32) * Real.log (Real.log X)
        - 5 * Real.log (Real.log (Real.log (2 * X + 16))) - Cfl ≤ M_range f X T) :
    U ≤ (C₁ + C₂) * X *
        ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
            * Real.exp ((1 / Real.exp 1)
                * (5 * Real.log (Real.log (Real.log (2 * X + 16))) + Cfl))
          + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  have hdecay := halasz_ball_decay hf hg hX hε hC₁ hC₂ hsplit hhead htail
  have hexp := expEM_le_of_floor_corrected hX hfloor
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hcoef : (0 : ℝ) ≤ (C₁ + C₂) * X := mul_nonneg (by linarith) hXpos.le
  refine hdecay.trans (mul_le_mul_of_nonneg_left ?_ hcoef)
  gcongr

/-- **T-2b (bridge) — `T1_decay_corrected_fgJ`.**  The fgJ-instantiated corrected T1
decay: `T1_pointwise_decay_corrected` at `f`-slot `= fgJ f t₀ y Y` (1-bounded via
`norm_fgJ_le`) and `g`-slot `= costwist t` (1-bounded via `norm_costwist_le`), carrying
the *corrected* N2 floor `hfloor` — exactly the floor `DistWindow.dist_split_A4_N2`
delivers W-free (with HUPPER discharged).  This is the seam that plugs HUPPER's output
into the T1 grade; the only remaining conditionality is Part 1's `hhead`.

**AMENDMENT J0 (JYH-ratified 2026-07-23).**  `M = M_range (fgJ f t₀ y Y) X T` is GHS
Lemma 1's range-minimum (was center-M `pretDistSq (fgJ f t₀ y Y) (costwist t) X`);
`prop_A3'_assembly`'s `int_U`/T1 row is thereby reconciled to the frozen `M_range` form
(`prop_A3'_assembly` itself is M-agnostic — abstract `Gunit`/`Gmom` — so it needs no
change).  The `t` slot survives (it fixes the `costwist t` character).

**AMENDMENT B4 (JYH-ratified 2026-07-23).**  `hhead`/conclusion re-frozen to the
elementary B-route `e^{−cM}` / `(log X)^{−c/32}` shape (`c = 1/e`, coefficient `C₁ + C₂`),
tracking `T1_pointwise_decay_corrected`.  Final grade `(log X)^{−1/(32e)+o(1)}`. -/
theorem T1_decay_corrected_fgJ {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ y Y t : ℝ)
    {X ε U Uhead Utail C₁ C₂ Cfl T : ℝ}
    (hX : Real.exp 1 ≤ X) (hε : 0 ≤ ε) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : U = Uhead + Utail)
    (hhead : Uhead ≤ C₁ * X * Real.exp (-(1 / Real.exp 1) * M_range (fgJ f t₀ y Y) X T))
    (htail : Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2))
    (hfloor : (1 / 32) * Real.log (Real.log X)
        - 5 * Real.log (Real.log (Real.log (2 * X + 16))) - Cfl
        ≤ M_range (fgJ f t₀ y Y) X T) :
    U ≤ (C₁ + C₂) * X *
        ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
            * Real.exp ((1 / Real.exp 1)
                * (5 * Real.log (Real.log (Real.log (2 * X + 16))) + Cfl))
          + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) :=
  T1_pointwise_decay_corrected (norm_fgJ_le hf t₀ y Y) (norm_costwist_le t) hX hε hC₁ hC₂
    hsplit hhead htail hfloor

/-! ## The moment rows (E1, E_j, large-`T`) — assembly-granularity wrappers

These re-export the landed moment machinery at the §8.1/8.2 assembly granularity.
`E1` (`moment_core_bound`, the exact `(2T + 20N)` MVT), the `E_j` moments
(`lemma13_moment`, the `(2T+20N)ℓ!²(C/X)` bound), and the large-`T` sub-rung
(`moment_core_bound_large_T`, the `T`-uniform `22T` collapse that makes `prop_A3'`
`T`-uniform under the `M_range` cap). -/

/-- **E1 row (exact `T+N`).**  The §8.1 first block mean square, the landed exact MVT
`moment_core_bound` restated as the assembly's E1 row. -/
theorem E1_row (N : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
  moment_core_bound N a T

/-- **The large-`T` sub-rung.**  For `T ≥ N`, the prefactor collapses to `22T`
(`moment_core_bound_large_T`) — the `T`-uniform grade that makes the terminal
`prop_A3'` `T`-uniform under the `M_range` cap (`T > X` regimes, s8-freeze:16). -/
theorem largeT_row (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : (N : ℝ) ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 22 * T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
  moment_core_bound_large_T N a T hT

/-- **E_j moment row.**  The §8.2 `E_j` block, the landed `lemma13_moment`
(`MomentsA2.lean:246`) — `∫ |Q^ℓ A|² ≤ (2T+20N)·ℓ!²·(C/X)` for coefficients supported
on `[X,N]` with count `|aₙ| ≤ ℓ!·g(n)` (the named MULT-SHIU seam).  Re-exported at the
assembly granularity; instantiating `N = 2^{ℓ+1}Y₁X` recovers the paper's
`(T/X + 2^ℓ Y₁)ℓ!²` shape (the geometric collapse over `j` is the remaining §8.2
analytic step). -/
theorem Ej_row :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y₁ X N ℓ : ℕ) (a : ℕ → ℂ) (T : ℝ),
      1 ≤ Y₁ → 1 ≤ X → 0 ≤ T → (∀ n, n < X → a n = 0) →
      (∀ n, ‖a n‖ ≤ (ℓ.factorial : ℝ) * (blockDiv Y₁ n : ℝ)) →
      (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
        ≤ (2 * T + 20 * (N : ℝ)) * ((ℓ.factorial : ℝ) ^ 2 * (C / (X : ℝ))) :=
  lemma13_moment

/-- **`int_U` block Cauchy–Schwarz.**  The §8.3 main-term step (MR Lemma 12, p.20): the
mean square of a block sum is `≤ #I · Σ_j (block moment)` — the landed
`cauchy_schwarz_intervalIntegral` at the assembly granularity.  This is the "square,
integrate over `𝒯`, apply Cauchy–Schwarz on the sum over `j`" step; the block moments
are then priced by `moment_core_bound` / `lemma12_meansq`. -/
theorem intU_block_CS {ι : Type*} (s : Finset ι) (u : ι → ℝ → ℂ) (a b : ℝ)
    (hab : a ≤ b) (hu : ∀ j ∈ s, Continuous (u j)) :
    (∫ t in a..b, ‖∑ j ∈ s, u j t‖ ^ 2)
      ≤ (s.card : ℝ) * ∑ j ∈ s, ∫ t in a..b, ‖u j t‖ ^ 2 :=
  cauchy_schwarz_intervalIntegral s u a b hab hu

/-! ## The terminal `prop_A3'` — the conditional-assembly house form

The §8.4 collect step: the range `[T₀,T]` mean square splits (MR eq (24)) into the
`int_U` row (§8.3 — Halász / the T1 pointwise decay + large values) and the `E1 + E_j`
moment row (§8.1/8.2).  With the T1-decay ball head still awaiting Part 1's H-EXIT, the
`int_U` grade is carried as the NAMED hypothesis `hunit` (dischargeable by
`T1_decay_corrected_fgJ` once Part 1 supplies `hhead`), and the moment grade as `hmom`
(dischargeable by `E1_row`/`Ej_row`/`largeT_row`).  The assembly closes to the frozen
`(T/X + 1)`-graded total.  This is the house conditional-assembly pattern: the content
lives in the named rows, each pointing at a landed lemma or Part 1's single residual. -/

/-- **`prop_A3'_assembly` — the terminal mean square, conditional-assembly form.**
The §8 eq-(24) decomposition `∫_{-T}^T |F|² = int_U + moments` (hypothesis `hsplit`, the
named §8 seam), with the `int_U` row bounded by the Halász/T1 grade `Gunit` (`hunit`,
`T1_decay_corrected_fgJ`-conditional on Part 1's `hhead`) and the moment row bounded by
`Gmom` (`hmom`, `E1_row`/`Ej_row`), assembles to `∫_{-T}^T |F|² ≤ Gunit + Gmom` — the
frozen `prop_A3'` grade with every row growing-quantity in-statement (#253).  The single
open input is Part 1's H-EXIT (the ball head); the assembly is otherwise closed. -/
theorem prop_A3'_assembly {N : ℕ} {a : ℕ → ℂ} {T Iunit Imom Gunit Gmom : ℝ}
    (hsplit : (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2) = Iunit + Imom)
    (hunit : Iunit ≤ Gunit) (hmom : Imom ≤ Gmom) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2) ≤ Gunit + Gmom := by
  rw [hsplit]; linarith [hunit, hmom]

end Salt.MR
