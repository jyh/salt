/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LambdaMass

/-!
# WINDOW-BRIDGE — the `hbridge` window-mass product (A-5)

The `HCENTER` ladder's A-5 (`docs/exploration/hsup-design.md`, ⟦AMENDMENT V2⟧ repair #1)
at the HONEST target: the product of the two `Λ`-window masses `crossKer` carries, on the
parameter-pinned home (`c₀ = 1 + 1/L`, `L = log X`) the `sigma_wiring` abstraction cannot
provide.

## The objects

`crossKer g X h y c₀ t₀ α β` (`JointHead.lean:76`) integrates
`‖P(s−β)‖·‖P(s+β)‖·‖hatKernel X h (c₀−α−β) (t−t₀)‖`.  Each window leg is bounded in `t` by
its coefficient mass (`norm_windowSum_le_mass`, used verbatim inside
`crossKer_integrand_integrable`), so the two objects this file multiplies are

  `S₋ := ∑_{n ∈ Ioo ⌊y⌋ ⌈X/y⌉} ‖lambdaLin (restrictAbove y g) n‖ / n^{c₀−β}`  (low leg),
  `S₊ := ∑_{n ∈ Ioo ⌊y⌋ ⌈X/y⌉} ‖lambdaLin (restrictAbove y g) n‖ / n^{c₀+β}`  (high leg).

**A finding, recorded.**  The `α` does **not** enter the window legs: `crossKer`'s two
`windowSum` factors sit at `c₀∓β`, and `α` appears only in the kernel's Poisson line
`c₀−α−β` (i.e. inside gate (c)'s `Kα = B(c₀−α−β)·(π/(c₀−α−β)²)·√((c₀−β)(c₀+β))`, not in the
mass page).  This agrees with the `JointHead` residual record's own gate (a)
(`JointHead.lean:604-610`) and makes the product page **α-uniform** — strictly stronger
than the per-`(α,β)` target the ladder anticipated: there is no `X^α·y^{−α}` factor for the
consumer to absorb against the kernel.  `window_bridge_shifted` is nevertheless supplied
for a low leg placed on the kernel line `c₀−α−β`, and it does carry the predicted
`X^{α+β}·y^{−(α+2β)}`; `window_bridge` is its `α = 0` face and is the one `crossKer` needs.

## The product page (the exponent bookkeeping)

`σ := β + 1/L`.  The high leg is at `c₀+β = 1+σ` exactly, and A-5a's damped stone
(`lambdaLin_window_damped_min`) gives `S₊ ≤ A·y^{−σ}·min(L', 2+1/σ)`, `A = log 4 + 4`,
`L' = log⌈X/y⌉ + A`.

The low leg is at `c₀−β = 1 − (β − 1/L)`; its *natural* shift is `δ = β − 1/L`, which is
NEGATIVE for `β < 1/L` and vanishes at `β = 1/L` — the corner that forces a case split and,
worse, leaves the low `min` graded at `1/δ` rather than at `1/σ` (so the two sharp Mertens
factors of the V2 target do not both appear).  **The page avoids both by over-shifting**:
the mass is antitone in the line (`window_mass_antitone_exp`), so the low leg may be read at
the SAME `σ`,

  `S₋ = S(c₀−β) ≤ S(1−σ) ≤ A·(X/y)^σ·min(L', 1+2/σ)`   (legal since `1−σ ≤ c₀−β`, gap `2/L`),

and the whole page becomes case-free with both `min`s graded at `σ`.  The cost is exactly
one factor `e`:

  `(X/y)^σ·y^{−σ} = X^σ·y^{−2σ} = X^{β}·X^{1/L}·y^{−2β}·y^{−2/L} ≤ e·X^β·y^{−2β}`

(`X^{1/log X} = e`; `y^{−2/L} ≤ 1` at `y ≥ 1`).  The `min` side collapses with `σ ≤ 1`:
`1+2/σ ≤ 3/σ` and `2+1/σ ≤ 3/σ`, while `σ ≥ 1/L` makes `min(L,1/σ) = 1/σ`, so

  `min(L',1+2/σ)·min(L',2+1/σ) ≤ 9·min(L,1/σ)²`.

**THE EXIT** (`window_bridge`):

  `S₋·S₊ ≤ 9·e·(log 4 + 4)² · X^β · y^{−2β} · min(L, 1/σ)²`,

i.e. the V2 amendment's honest target `C·X^β·y^{−2β}·min(L,1/σ)²` with the constant
explicit (`C = 9e(log 4+4)² ≈ 710`).  The four box corners of the recorded gate (b) are all
inside this one page: `β = 0` gives `σ = 1/L`, `min = L`, and the bound `≍ L²`; `β = η`
gives `σ ≍ η`, `min ≍ 1/η`; `y = √X` (empty window) makes both sums `0`; the ratio to the
target is `≤ 9e A²` uniformly — no corner is checked separately.

**What is NOT claimed.**  The refuted `(X/y)^{2β}` shape of the `JointHead` residual record
(`JointHead.lean:613`) is not stated anywhere here (freeze ruling 3: TRUE but UNCOMPOSABLE).

## The `hbridge` adapter — residual

`sigma_wiring`'s `hbridge` (`JointHead.lean:277`) is an *integral*-level binder
(`∫β supF·crossKer ≤ Kα·∫σ Fbound/σ`).  Reaching it from this file's mass product still
needs the S-ladder's remaining links, exactly as the `JointHead` residual record lists them:
gate (c)'s chaining (`mixed_weight_cs` ∘ `lorentz_compare` ∘ `k4_plan_le_diag_sharp` ∘
`norm_hatKernel_le`) to descend `crossKer α β` onto `S₋·S₊`; the `σ = β+1/L` ⇄ `[1/L, 2η]`
reparametrization (needs `1/L ≤ η` and `Fbound ≥ 0` on `[η+1/L, 2η]`); and a CONCRETE
`Fbound` from SupF (SF-2/SF-3, on HOLD).  What this file removes from that list is the
record's item 1: the parameter relations `c₀ = 1+1/L`, `L = log X` are now *hypotheses of a
landed lemma*, and gate (b) is discharged against them with an absolute constant.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## The window mass: nonnegativity and antitonicity in the line -/

/-- The `Λ`-window mass at any line is nonnegative. -/
theorem window_mass_nonneg (g : ℕ → ℂ) (X y c : ℝ) :
    0 ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ c :=
  Finset.sum_nonneg (fun n _ => by positivity)

/-- **The mass is antitone in the line.**  Every window member is `≥ 1`, so `n^c` is
monotone in `c` and the summand is antitone.  This is what lets the low leg be *read at an
over-shifted line* (the page's case-free device). -/
theorem window_mass_antitone_exp (g : ℕ → ℂ) {X y c c' : ℝ} (hcc : c ≤ c') :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ c')
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ c := by
  refine Finset.sum_le_sum (fun n hn => ?_)
  obtain ⟨hn1, _, _⟩ := mem_lambda_window (X := X) (y := y) hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hpos : (0 : ℝ) < (n : ℝ) ^ c := Real.rpow_pos_of_pos (by linarith) c
  exact div_le_div_of_nonneg_left (norm_nonneg _) hpos
    (Real.rpow_le_rpow_of_exponent_le h1 hcc)

/-! ## The two legs at a general line -/

/-- **The LOW leg at an over-shifted line.**  For any line `c ≥ 1 − δ` (`0 < δ ≤ 1`), the
A-5a shifted stone applies after one antitone step. -/
theorem window_mass_low_le (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X y c δ : ℝ} (hy : 1 ≤ y) (hXy : 1 ≤ X / y) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : 1 - δ ≤ c) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ c)
      ≤ (Real.log 4 + 4) * (X / y) ^ δ
          * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / δ) :=
  le_trans (window_mass_antitone_exp g hc)
    (lambdaLin_window_shifted_min g hg hy hXy hδ0 hδ1 rfl)

/-- **The HIGH leg at an over-damped line.**  For any line `c ≥ 1 + σ` (`0 < σ`), the A-5a
damped stone applies after one antitone step. -/
theorem window_mass_high_le (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X y c σ : ℝ} (hy : 1 ≤ y) (hσ : 0 < σ) (hc : 1 + σ ≤ c) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ c)
      ≤ (Real.log 4 + 4) * y ^ (-σ)
          * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ) :=
  le_trans (window_mass_antitone_exp g hc)
    (lambdaLin_window_damped_min g hg hy hσ rfl)

/-! ## The raw product (two independent shifts, both `min`s kept) -/

/-- **A-5, the raw product page.**  Two window masses on any pair of lines — a low line
`clo ≥ 1−δ` and a high line `chi ≥ 1+σ`:

  `S(clo)·S(chi) ≤ (log 4+4)²·((X/y)^δ·y^{−σ})·min(L',1+2/δ)·min(L',2+1/σ)`.

No parameter pin is used; `window_bridge` specializes `δ := σ := β+1/L` at `c₀ = 1+1/L`. -/
theorem window_mass_product (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X y clo chi δ σ : ℝ} (hy : 1 ≤ y) (hXy : 1 ≤ X / y)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hσ0 : 0 < σ)
    (hlow : 1 - δ ≤ clo) (hhigh : 1 + σ ≤ chi) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ clo)
      * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ chi)
      ≤ (Real.log 4 + 4) ^ 2 * ((X / y) ^ δ * y ^ (-σ))
          * (min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / δ)
              * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hXy0 : (0 : ℝ) < X / y := by linarith
  have hA0 : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  have hlo := window_mass_low_le g hg hy hXy hδ0 hδ1 hlow
  have hhi := window_mass_high_le g hg (X := X) hy hσ0 hhigh
  have hmin0 : (0 : ℝ) ≤ min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / δ) :=
    le_min window_grade_pos.le (by positivity)
  have hRlow : (0 : ℝ) ≤ (Real.log 4 + 4) * (X / y) ^ δ
      * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / δ) :=
    mul_nonneg (mul_nonneg hA0 (Real.rpow_nonneg hXy0.le _)) hmin0
  calc (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ clo)
        * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ chi)
      ≤ ((Real.log 4 + 4) * (X / y) ^ δ
            * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / δ))
          * ((Real.log 4 + 4) * y ^ (-σ)
            * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ)) :=
        mul_le_mul hlo hhi (window_mass_nonneg g X y chi) hRlow
    _ = (Real.log 4 + 4) ^ 2 * ((X / y) ^ δ * y ^ (-σ))
          * (min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / δ)
              * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ)) := by ring

/-! ## The exponent page -/

/-- `X^{1/log X} = e` (the whole content of the over-shift's price). -/
theorem rpow_one_div_log_self {X : ℝ} (hX : 0 < X) (hlog : Real.log X ≠ 0) :
    X ^ (1 / Real.log X) = Real.exp 1 := by
  rw [Real.rpow_def_of_pos hX]
  congr 1
  field_simp

/-- **The exponent identity of the page.**  At `σ = β + 1/L`, `L = log X`:

  `(X/y)^{α+σ}·y^{−σ} ≤ e·X^{α+β}·y^{−(α+2β)}`.

The `X^{1/L} = e` is the over-shift's price; the leftover `y^{−2/L} ≤ 1` is discarded. -/
theorem window_exp_page {X y L α β σ : ℝ} (hL : L = Real.log X) (hL0 : 0 < L)
    (hy : 1 ≤ y) (hX0 : 0 < X) (hσ : σ = β + 1 / L) :
    (X / y) ^ (α + σ) * y ^ (-σ) ≤ Real.exp 1 * (X ^ (α + β) * y ^ (-(α + 2 * β))) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hXexp : X ^ (1 / L) = Real.exp 1 := by
    rw [hL]; exact rpow_one_div_log_self hX0 (by rw [← hL]; exact hLne)
  have h1 : (X / y) ^ (α + σ) = X ^ (α + σ) * y ^ (-(α + σ)) := by
    rw [Real.div_rpow hX0.le hy0.le, Real.rpow_neg hy0.le, div_eq_mul_inv]
  have h2 : X ^ (α + σ) = X ^ (α + β) * Real.exp 1 := by
    rw [hσ, show α + (β + 1 / L) = α + β + 1 / L from by ring, Real.rpow_add hX0, hXexp]
  have h3 : y ^ (-(α + σ)) * y ^ (-σ) = y ^ (-(α + 2 * β)) * y ^ (-(2 / L)) := by
    rw [← Real.rpow_add hy0, ← Real.rpow_add hy0, hσ]
    congr 1
    ring
  have h4 : y ^ (-(2 / L)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy (by
      have : (0 : ℝ) < 2 / L := by positivity
      linarith)
  calc (X / y) ^ (α + σ) * y ^ (-σ)
      = (X ^ (α + β) * Real.exp 1) * (y ^ (-(α + σ)) * y ^ (-σ)) := by rw [h1, h2]; ring
    _ = (X ^ (α + β) * Real.exp 1) * (y ^ (-(α + 2 * β)) * y ^ (-(2 / L))) := by rw [h3]
    _ ≤ (X ^ (α + β) * Real.exp 1) * (y ^ (-(α + 2 * β)) * 1) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hy0.le _)) ?_
        exact mul_nonneg (Real.rpow_nonneg hX0.le _) (Real.exp_pos 1).le
    _ = Real.exp 1 * (X ^ (α + β) * y ^ (-(α + 2 * β))) := by ring

/-! ## THE EXIT — the pinned product bound -/

/-- **A-5 (the `α`-carrying face) — `window_bridge_shifted`.**  The window-mass product
with the LOW leg placed on the kernel's line `c₀−α−β` (`α ∈ [0,η]`), at the pinned home
`c₀ = 1+1/L`, `L = log X`, `σ = β+1/L`:

  `S(c₀−α−β)·S(c₀+β) ≤ 9e(log 4+4)²·X^{α+β}·y^{−(α+2β)}·min(L,1/σ)²`.

The `X^{α}·y^{−α}` factor is the one the consumer pairs against the kernel's `X^{−α}`
(gate (c)); `window_bridge` is the `α = 0` face, and is the one `crossKer` actually needs
(its window legs are `α`-free — see the module docstring). -/
theorem window_bridge_shifted (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X y c₀ L α β σ : ℝ}
    (hL : L = Real.log X) (hL3 : 3 ≤ L) (hy : 1 ≤ y) (hyX : y ≤ X)
    (hc₀ : c₀ = 1 + 1 / L) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαβ : α + β ≤ 1 / 2)
    (hσ : σ = β + 1 / L) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - α - β))
      * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β))
      ≤ 9 * Real.exp 1 * (Real.log 4 + 4) ^ 2
          * (X ^ (α + β) * y ^ (-(α + 2 * β))) * min L (1 / σ) ^ 2 := by
  -- the arithmetic of the box
  have hy0 : (0 : ℝ) < y := by linarith
  have hX1 : (1 : ℝ) ≤ X := le_trans hy hyX
  have hX0 : (0 : ℝ) < X := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hLinv3 : 1 / L ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hL0 (by norm_num : (0 : ℝ) < 3)]; linarith
  have hβ12 : β ≤ 1 / 2 := by linarith
  have hσ0 : (0 : ℝ) < σ := by rw [hσ]; linarith
  have hσ1 : σ ≤ 1 := by rw [hσ]; linarith
  have hδ0 : (0 : ℝ) < α + σ := by linarith
  have hδ1 : α + σ ≤ 1 := by rw [hσ]; linarith
  have hXy : (1 : ℝ) ≤ X / y := (one_le_div hy0).mpr hyX
  have hXy0 : (0 : ℝ) < X / y := by linarith
  have hA0 : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  -- the two lines
  have hlowline : 1 - (α + σ) ≤ c₀ - α - β := by rw [hc₀, hσ]; linarith
  have hhighline : 1 + σ ≤ c₀ + β := by rw [hc₀, hσ]; linarith
  -- STEP 1 — the raw product
  have hprod := window_mass_product g hg (clo := c₀ - α - β) (chi := c₀ + β)
    (δ := α + σ) (σ := σ) hy hXy hδ0 hδ1 hσ0 hlowline hhighline
  -- STEP 2 — the exponent page
  have hE := window_exp_page (X := X) (y := y) (L := L) (α := α) (β := β) (σ := σ)
    hL hL0 hy hX0 hσ
  have hE0 : (0 : ℝ) ≤ (X / y) ^ (α + σ) * y ^ (-σ) :=
    mul_nonneg (Real.rpow_nonneg hXy0.le _) (Real.rpow_nonneg hy0.le _)
  -- STEP 3 — the `min` side
  have hinv1 : (1 : ℝ) ≤ 1 / σ := by rw [le_div_iff₀ hσ0]; linarith
  have hminL : min L (1 / σ) = 1 / σ := by
    refine min_eq_right ?_
    rw [div_le_iff₀ hσ0]
    have hLσ : L * σ = L * β + 1 := by rw [hσ]; field_simp
    nlinarith
  have hσ3 : 2 + 1 / σ ≤ 3 / σ := by
    rw [show (3 : ℝ) / σ = 3 * (1 / σ) from by ring]; linarith
  have hδ3 : 1 + 2 / (α + σ) ≤ 3 / σ := by
    have hdiv : 2 / (α + σ) ≤ 2 / σ :=
      div_le_div_of_nonneg_left (by norm_num) hσ0 (by linarith)
    rw [show (3 : ℝ) / σ = 3 * (1 / σ) from by ring,
      show (2 : ℝ) / σ = 2 * (1 / σ) from by ring] at *
    linarith
  have h3σ0 : (0 : ℝ) ≤ 3 / σ := by positivity
  have hM : min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / (α + σ))
        * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ)
      ≤ 9 * min L (1 / σ) ^ 2 := by
    have hb1 : min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / (α + σ)) ≤ 3 / σ :=
      le_trans (min_le_right _ _) hδ3
    have hb2 : min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ) ≤ 3 / σ :=
      le_trans (min_le_right _ _) hσ3
    have hn2 : (0 : ℝ) ≤ min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ) :=
      le_min window_grade_pos.le (by positivity)
    calc min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / (α + σ))
          * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ)
        ≤ (3 / σ) * (3 / σ) := mul_le_mul hb1 hb2 hn2 h3σ0
      _ = 9 * (1 / σ) ^ 2 := by ring
      _ = 9 * min L (1 / σ) ^ 2 := by rw [hminL]
  have hM0 : (0 : ℝ) ≤ min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / (α + σ))
      * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ) :=
    mul_nonneg (le_min window_grade_pos.le (by positivity))
      (le_min window_grade_pos.le (by positivity))
  -- STEP 4 — the composition
  have hRHS0 : (0 : ℝ) ≤ (Real.log 4 + 4) ^ 2
      * (Real.exp 1 * (X ^ (α + β) * y ^ (-(α + 2 * β)))) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (Real.exp_pos 1).le
      (mul_nonneg (Real.rpow_nonneg hX0.le _) (Real.rpow_nonneg hy0.le _)))
  refine le_trans hprod (le_trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hE (sq_nonneg (Real.log 4 + 4))) hM hM0 hRHS0) ?_)
  rw [hminL]
  ring_nf
  rfl

/-- **A-5 — THE EXIT `window_bridge`.**  The `hbridge` window-mass product at the pinned
home, on the exact pair of lines `crossKer` carries (`c₀∓β`, `α`-free):

  `S₋·S₊ ≤ 9e(log 4+4)²·X^β·y^{−2β}·min(L,1/σ)²`,  `σ = β + 1/L`, `c₀ = 1+1/L`, `L = log X`.

This is the V2 amendment's honest target with an explicit absolute constant.  Gates: the
datum `g` 1-bounded at primes; `3 ≤ L = log X`; `1 ≤ y ≤ X`; `0 ≤ β ≤ 1/2` (satisfied by
`β ≤ η = 1/log y` at `y ≥ 10`, since `1/log 10 < 0.44`).  Note `y ≤ √X` is NOT needed —
the over-shifted page is uniform on the whole box, and the empty-window corner `y = √X`
is covered by the same inequality (both masses vanish). -/
theorem window_bridge (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X y c₀ L β σ : ℝ}
    (hL : L = Real.log X) (hL3 : 3 ≤ L) (hy : 1 ≤ y) (hyX : y ≤ X)
    (hc₀ : c₀ = 1 + 1 / L) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 2) (hσ : σ = β + 1 / L) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
      * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β))
      ≤ 9 * Real.exp 1 * (Real.log 4 + 4) ^ 2
          * (X ^ β * y ^ (-(2 * β))) * min L (1 / σ) ^ 2 := by
  have h := window_bridge_shifted g hg (α := 0) hL hL3 hy hyX hc₀ le_rfl hβ0
    (by linarith) hσ
  simpa using h

end Salt.MR
