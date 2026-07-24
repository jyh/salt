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
import Salt.MR.AnnHead

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

/-! ## MOMENT-WIRE — the annular moment row (Imom concrete, hmom discharged)

The closing socket of the annular T-chain.  `AnnHead.prop_A3_T1_row_annular` holds the
`int_U` head/tail side concrete (`annHead` + the S2′ tail ledger) but keeps the moment
side as the abstract binder pair `(Imom, Gmom)` with `hmom : Imom ≤ Gmom`.  This section
discharges that binder at the CONCRETE landed moment engines, completing the socket
census (head/tail were already concrete via `T1_decay_annular_tailed`).

**The B-pin (the moment side crossed onto the `Re = 1 + σ` line).**  The head `annHead`
lives on the shifted line `Re = 1 + σ` (`σ = 1/log X`).  The landed moment lemmas
(`moment_core_bound`/`E1_row`, `lemma13_moment`/`Ej_row`) are stated on the classical
`Re = 1` line (`spoly N a`, coefficient `aₙ/n^{1+it}`).  The pin: the moment lemmas are
*line-agnostic through the coefficient* — instantiating the coefficient at the rescaled
`aₙ·n^{-σ}` reaches `Re = 1 + σ` (`Σ aₙ·n^{-σ}/n^{1+it} = Σ aₙ/n^{1+σ+it}`), and the
masses only shrink (`‖aₙ·n^{-σ}‖ = ‖aₙ‖·n^{-σ} ≤ ‖aₙ‖` for `σ ≥ 0`, `n ≥ 1`), so every
`L²`-mass bound and every MULT-SHIU coefficient hypothesis (support, `‖aₙ‖ ≤ ℓ!·g(n)`
count) is PRESERVED.  No landed moment lemma is re-proven.  This puts the moment side on
the SAME line as the head, so the residual seam `hsplit` no longer carries a line
mismatch (see the row's docstring).

The stones (crude sum-of-blocks; NOT the sharp §8.2 `(T/X + 2^ℓ Y₁)ℓ!²` geometric-`j`
collapse — that is the flagged C-tier follow-up):

* `moment_core_bound_shifted` — the E1 MVT bound at the shifted coefficient (the B-pin
  for the diagonal block; `moment_core_bound` at `aₙ·n^{-σ}` + the `n^{-σ} ≤ 1` shrink).
* `shifted_support`/`shifted_count` — the rescaling preserves MULT-SHIU (feeds `Ej_row`
  at the shifted coefficient with the SAME `(2T+20N)ℓ!²(C/X)` grade, the grade being
  coefficient-mass-independent).
* `prop_A3_T1_row_moment` — the row: `prop_A3_T1_row_annular` with `Imom` concrete (the
  E1 shifted integral + the crude `Σ_j` of shifted `Ej` block integrals) and `hmom`
  DISCHARGED.  `hsplit` stays the abstract §8 seam. -/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open MeasureTheory Complex

/-- **The rescale factor is `≤ 1`.**  For `σ ≥ 0` and every `n : ℕ`, `n^{-σ} ≤ 1`
(the mass-shrink behind the B-pin): `n = 0` gives `0^{-σ} ≤ 1` (`zero_rpow_le_one`),
`n ≥ 1` gives `n^{-σ} ≤ 1` for a nonpositive exponent. -/
lemma rpow_natCast_neg_le_one (n : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) : (n : ℝ) ^ (-σ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simpa using Real.zero_rpow_le_one (-σ)
  · exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast h) (neg_nonpos.mpr hσ)

/-- **M1 — the E1 moment bound at the shifted line (`moment_core_bound_shifted`).**  The
keystone `moment_core_bound` instantiated at the rescaled coefficient `aₙ·n^{-σ}` (the
`Re = 1 + σ` line, the B-pin), with the `n^{-σ} ≤ 1` shrink folding the shifted `L²`
mass `Σ ‖aₙ·n^{-σ}‖²/n²` back into the plain `Σ ‖aₙ‖²/n²`.  So the shifted-line E1 block
obeys the SAME `(2T+20N)·Σ‖aₙ‖²/n²` grade the `Re = 1` block does — the masses only
shrink under the line shift.  (`0 ≤ σ`, `0 ≤ T` are the only inputs.) -/
theorem moment_core_bound_shifted (N : ℕ) (a : ℕ → ℂ) (T σ : ℝ)
    (hT : 0 ≤ T) (hσ : 0 ≤ σ) :
    (∫ t in (-T)..T, ‖spoly N (fun n => a n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  refine (moment_core_bound N (fun n => a n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) T).trans ?_
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) N; linarith
  refine mul_le_mul_of_nonneg_left ?_ hpre
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnorm : ‖a n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ = ‖a n‖ * (n : ℝ) ^ (-σ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hle1 : (n : ℝ) ^ (-σ) ≤ 1 := rpow_natCast_neg_le_one n σ hσ
  have hge0 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  rw [hnorm]
  have hr2 : ((n : ℝ) ^ (-σ)) ^ 2 ≤ 1 := by nlinarith [hle1, hge0]
  have hnum : (‖a n‖ * (n : ℝ) ^ (-σ)) ^ 2 ≤ ‖a n‖ ^ 2 := by
    rw [mul_pow]
    calc ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2 ≤ ‖a n‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hr2 (sq_nonneg _)
      _ = ‖a n‖ ^ 2 := mul_one _
  exact div_le_div_of_nonneg_right hnum (by positivity)

/-- **The shift preserves the MULT-SHIU support** (`shifted_support`).  If `aₙ = 0` for
`n < X`, so is the rescaled `aₙ·n^{-σ}` — the `Ej_row` support hypothesis threads through
the B-pin unchanged. -/
lemma shifted_support {a : ℕ → ℂ} {σ : ℝ} {X : ℕ} (h : ∀ n, n < X → a n = 0) :
    ∀ n, n < X → a n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) = 0 :=
  fun n hn => by rw [h n hn, zero_mul]

/-- **The shift preserves the MULT-SHIU count** (`shifted_count`).  For `σ ≥ 0`,
`‖aₙ·n^{-σ}‖ = ‖aₙ‖·n^{-σ} ≤ ‖aₙ‖ ≤ ℓ!·g(n)` — the `Ej_row` count hypothesis threads
through the B-pin unchanged (the mass only shrinks). -/
lemma shifted_count {a : ℕ → ℂ} {σ : ℝ} (hσ : 0 ≤ σ) {Y₁ ℓ : ℕ}
    (h : ∀ n, ‖a n‖ ≤ (ℓ.factorial : ℝ) * (blockDiv Y₁ n : ℝ)) :
    ∀ n, ‖a n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ≤ (ℓ.factorial : ℝ) * (blockDiv Y₁ n : ℝ) := by
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hle1 : (n : ℝ) ^ (-σ) ≤ 1 := rpow_natCast_neg_le_one n σ hσ
  calc ‖a n‖ * (n : ℝ) ^ (-σ) ≤ ‖a n‖ * 1 :=
        mul_le_mul_of_nonneg_left hle1 (norm_nonneg _)
    _ = ‖a n‖ := mul_one _
    _ ≤ (ℓ.factorial : ℝ) * (blockDiv Y₁ n : ℝ) := h n

/-- **MOMENT-WIRE — the annular moment row (`prop_A3_T1_row_moment`).**
`AnnHead.prop_A3_T1_row_annular` with its moment binder `(Imom, Gmom, hmom)` DISCHARGED
at the concrete landed engines.  `Imom` is made the honest crude moment side on the
shifted line `Re = 1 + σ` (`σ = 1/log X`, matching the head):

  `Imom = (∫_{-T}^T ‖spolyₛₕ N₁ a₁‖²)  +  Σ_{j∈J} ∫_{-T}^T ‖spolyₛₕ (Nfun j) (afun j)‖²`

— the E1 diagonal block plus the crude `Σ_j` of the `Eⱼ` moment blocks (all coefficients
rescaled by `n^{-σ}`, `spolyₛₕ` denoting `spoly` at that coefficient).  `Gmom` is the
matching crude grade

  `Gmom = (2T+20N₁)·Σ‖a₁ₙ‖²/n²  +  Σ_{j∈J} (2T+20 Nⱼ)·(ℓⱼ!²·(Cej/Xe))`,

and `hmom : Imom ≤ Gmom` is discharged blockwise: the E1 block by `moment_core_bound_shifted`
(M1) and each `Eⱼ` block by `Ej_row` at the shifted coefficient (the MULT-SHIU seam
threading through via `shifted_support`/`shifted_count`; `Cej` is `Ej_row`'s absolute
Shiu constant, hoisted into the `∃`).  The blocks are held on the SAME `Re = 1 + σ` line
as the head, so the row lives entirely on the shifted line.

**The remaining seam `hsplit`** stays the abstract §8 eq-(24) seam — the DESIGN-TIER
join `Itot = (head + tail) + Imom`.  With the B-pin it no longer carries a *line*
mismatch (head and moment both on `Re = 1 + σ`); it carries only the *domain* seam
(the true mean square's `[-T,T]` vs the head's `M_range` annulus and the moment
sub-domains `𝒯ⱼ`) and the *object* seam (`spoly` / the `A(s)` Dirichlet polynomial vs the
head's `LSeries (ellLin …)`).  Building that join — the `𝒰/𝒯ⱼ` setIntegral partition and
the eq-(16) Ramaré decomposition — is out of MOMENT-WIRE's scope (design-tier), so it is
carried as the hypothesis exactly as `prop_A3_T1_row_annular` carries it.

**Socket census after this stone.**  Head: CONCRETE (`annHead`).  Tail: CONCRETE (the S2′
ledger object).  Moment: CONCRETE (`Imom` above, `hmom` discharged).  Remaining ABSTRACT:
`hfloor` (the R3.1 branch floor, the standing MULT-SHIU/branch analytic supply) and
`hsplit` (the §8 seam), both carried as hypotheses.  The crude `Gmom` is not the sharp
§8.2 geometric collapse — that sharpening (`(T/X + 2^ℓ Y₁)ℓ!²`) is the flagged C-tier
follow-up. -/
theorem prop_A3_T1_row_moment {ι : Type*} (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (t₀ t : ℝ)
    (N₁ : ℕ) (a₁ : ℕ → ℂ)
    (J : Finset ι) (Nfun ℓfun : ι → ℕ) (afun : ι → ℕ → ℂ) (Y₁ Xe : ℕ)
    (hY₁ : 1 ≤ Y₁) (hXe : 1 ≤ Xe)
    (hsupp : ∀ j ∈ J, ∀ n, n < Xe → afun j n = 0)
    (hcoeff : ∀ j ∈ J, ∀ n, ‖afun j n‖ ≤ ((ℓfun j).factorial : ℝ) * (blockDiv Y₁ n : ℝ)) :
    ∃ C₁ Cej X₀ : ℝ, 0 ≤ C₁ ∧ 0 < Cej ∧ ∀ (X ε Utail C₂ T Itot : ℝ),
      X₀ ≤ X → 0 ≤ T → T ≤ Real.log X → 0 ≤ ε → 0 ≤ C₂ →
      Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      Itot = (annHead g t₀ X T (1 / Real.log X) + Utail)
          + ((∫ s in (-T)..T,
                ‖spoly N₁ (fun n => a₁ n * (((n : ℝ) ^ (-(1 / Real.log X)) : ℝ) : ℂ)) s‖ ^ 2)
            + ∑ j ∈ J, ∫ s in (-T)..T,
                ‖spoly (Nfun j)
                  (fun n => afun j n * (((n : ℝ) ^ (-(1 / Real.log X)) : ℝ) : ℂ)) s‖ ^ 2) →
      Itot ≤ (C₁ + C₂) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε))
          + ((2 * T + 20 * (N₁ : ℝ)) * ∑ n ∈ Finset.Icc 1 N₁, ‖a₁ n‖ ^ 2 / (n : ℝ) ^ 2
            + ∑ j ∈ J, (2 * T + 20 * ((Nfun j : ℕ) : ℝ))
                * (((ℓfun j).factorial : ℝ) ^ 2 * (Cej / (Xe : ℝ)))) := by
  obtain ⟨C₁, X₀, hC₁, hrow⟩ := prop_A3_T1_row_annular g hg t₀ t
  obtain ⟨Cej, hCej_pos, hEj⟩ := Ej_row
  refine ⟨C₁, Cej, max X₀ (Real.exp 1), hC₁, hCej_pos, ?_⟩
  intro X ε Utail C₂ T Itot hX hT hTL hε hC₂ htail hfloor hsplit
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe' : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe'
  have hL1 : (1 : ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hXe'
  have hσ0 : (0 : ℝ) ≤ 1 / Real.log X := by positivity
  -- discharge `hmom : Imom_concrete ≤ Gmom_concrete` blockwise (E1 via M1, each Eⱼ via Ej_row)
  have hmom :
      ((∫ s in (-T)..T,
            ‖spoly N₁ (fun n => a₁ n * (((n : ℝ) ^ (-(1 / Real.log X)) : ℝ) : ℂ)) s‖ ^ 2)
        + ∑ j ∈ J, ∫ s in (-T)..T,
            ‖spoly (Nfun j)
              (fun n => afun j n * (((n : ℝ) ^ (-(1 / Real.log X)) : ℝ) : ℂ)) s‖ ^ 2)
      ≤ ((2 * T + 20 * (N₁ : ℝ)) * ∑ n ∈ Finset.Icc 1 N₁, ‖a₁ n‖ ^ 2 / (n : ℝ) ^ 2
        + ∑ j ∈ J, (2 * T + 20 * ((Nfun j : ℕ) : ℝ))
            * (((ℓfun j).factorial : ℝ) ^ 2 * (Cej / (Xe : ℝ)))) := by
    refine add_le_add (moment_core_bound_shifted N₁ a₁ T (1 / Real.log X) hT hσ0) ?_
    refine Finset.sum_le_sum (fun j hj => ?_)
    exact hEj Y₁ Xe (Nfun j) (ℓfun j)
      (fun n => afun j n * (((n : ℝ) ^ (-(1 / Real.log X)) : ℝ) : ℂ)) T
      hY₁ hXe hT (shifted_support (hsupp j hj)) (shifted_count hσ0 (hcoeff j hj))
  exact hrow X ε Utail C₂ T Itot _ _ hX0 hT hTL hε hC₂ htail hfloor hsplit hmom

end Salt.MR
