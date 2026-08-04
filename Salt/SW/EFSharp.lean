/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.Defs
import Salt.SW.Growth
import Salt.SW.ZeroCount
import Salt.SW.TBalFinal

/-!
# THE FULCRUM CAMPAIGN, node N1 — the sharp `ψ(y,χ)` explicit formula, wave 1

Target genre (Heath-Brown 1983, p.208; `docs/sources/hb1983-notes.md` §4, crosswalk row N1):

    ψ(y,χ) = − y^{β₀}/β₀ − ∑′_{|ρ| ≤ T} y^ρ/ρ + O(y T^{−1}(log qy)²) + O(y^{1/4} log y),

i.e. the *sharp* Chebyshev carrier against an **enumerated truncated zero sum**, replacing the
corpus's `hzf` ("every zero in the box is the one exceptional zero") architecture
(`Salt/SW/ShiftVariants.lean`, `psi1_contour_shift` / `psi1_contour_shift_exceptional`) by a
statement that *counts* the zeros instead of assuming them away.

**Truncation-height ruling (N0-AUDIT, `docs/blueprints/flags.md`, ⟦N0 CLEAR⟧).** The campaign
truncates the explicit formula at `T = (log q)⁴` (the audit forced `T ≥ (log q)^{3.9}`; the
disc height `T = q²` is independently NOT viable — the band top collapses to `q^{−0.059}`).
`efHeight` below is the kernel record of that ruling, in the guarded shape `(log q + 2)⁴`
(which is `≥ 16` for every `q ≥ 1`, so the `T ≥ 2` side conditions are free).

## What this wave lands

**(1) The sharp-from-smoothed bridge** (§2–§3) — the piece that lets the corpus's *smoothed*
`ψ₁` contour machinery (absolutely convergent Mellin kernel `x^{s+1}/(s(s+1))`; the sharp-cutoff
Perron step is exactly what `Salt/SW/Kernel.lean` cannot do) deliver a *sharp* `ψ`:

    ‖ψ(y,χ) − h^{−1}·(ψ₁(y+h,χ) − ψ₁(y,χ))‖ ≤ (h+1)·log(y+h)      (`psiChiR_sub_riesz_diff_le`)

for every `h > 0`, with **no** hypothesis on `χ`, on zeros, or on `q`. At the campaign's step
`h = y/T` this is (`psi_sharp_riesz_at_height`)

    ‖ψ(y,χ) − (T/y)·(ψ₁(y + y/T, χ) − ψ₁(y,χ))‖ ≤ (y/T)·log(qy) + log(qy),

which is **inside** HB's p.208 budget `O(yT^{−1}(log qy)²)` — the differencing costs one power
of `log`, not two, so the B-degree invariant of the ⟦N8/N9⟧ port mandate (degree ≤ 2 in
`log qy`) is respected with a full power of `log` still in hand. The constant is `1` in both
places; no constant is minted beyond `C_EF = 1`.

**(2) The zero-enumeration supply** (§4) — the Dirichlet-`L` analogue of the landed ζ half-box
count (`Salt/SW/BoxCount.lean`), which is what an enumerated `∑_{|γ| ≤ T}` must be batched
against, one unit window at a time:

    #{ρ : L(ρ,χ) = 0, |ρ − (2+it₀)| ≤ 37/20}  ≤  (7/log(39/37))·log(q(|t₀|+2))

(`LFunction_halfbox_zero_count`), the ball containing the half-box
`{1/2 ≤ Re ρ ≤ 1, |Im ρ − t₀| ≤ 1}` (`halfbox_subset_closedBall`). Route: the landed Jensen
keystone `LFunction_zero_count_le` at `r = 37/20`, `R = 39/20`, fed by the *wide* growth sphere
`LFunction_growth_sphere_wide` proved here (the landed `LFunction_growth_sphere` is at
`R = 7/4`, whose ball reaches only `Re ≥ 1/4` and misses the `Re = 1/2` corners of the window).

**(3) The residue de-smoothing and the capstone** (§3b). The smoothed contour shift's residue
at a zero `ρ` is the Riesz one, `x^{ρ+1}/(ρ(ρ+1))`; the sharp explicit formula's term is
`y^ρ/ρ`. Since the first is an antiderivative of the second, the bridge's first difference
converts one into the other at mean-value cost (`cpow_riesz_residue_desmooth`, summed in
`efRieszSum_diff_sub_efZeroSum_le`):

    ‖h^{−1}(𝓡(y+h) − 𝓡(y)) − ∑_{ρ ∈ Z} y^ρ/ρ‖ ≤ #Z·h·y^{σ−1}    (σ = max Re ρ),

which at `h = y/T` is `#Z·y^σ/T` — a full `1/T` below the zero sum itself. Composing this with
the bridge gives the node's capstone, `psi_explicit_sharp_of_riesz_residues`:

    ‖ψ₁(y,χ) + 𝓡(y)‖ ≤ E₁,  ‖ψ₁(y+h,χ) + 𝓡(y+h)‖ ≤ E₂
      ⟹ ‖ψ(y,χ) + ∑_{ρ ∈ Z} y^ρ/ρ‖ ≤ (h+1)log(y+h) + (E₁+E₂)/h + #Z·h·y^{σ−1},

i.e. **the sharp explicit formula with an enumerated zero sum, reduced to the enumerated
contour shift for the smoothed carrier** (A1 below) — and nothing else.

## The remaining assembly (named exactly, for N1 wave 2)

The full `psi_explicit_sharp` still owes, in order:

* **A1 — the enumerated residue sum for `ψ₁`** (the capstone's only unmet hypothesis).
  `psi1_contour_shift` (`ShiftVariants.lean:235` area) generalized from `hzf`/one exceptional
  zero to a *finite enumerated* zero set inside the box, with residue `efRieszSum Z x`. A
  surgical generalization of a landed ~1000-line proof, not new analysis: the Goursat/edge/tail
  estimates are unchanged; only the residue extraction (`kernel_residue`) is applied once per
  enumerated zero. The de-smoothing and the sharp/smoothed bridge are already discharged.
* **A2 — the zero-set enumeration itself.** The `Finset Z` of zeros of `L(·,χ)` in the box
  `{0 ≤ Re ρ ≤ 1, |Im ρ| ≤ T}` with multiplicity, glued from the per-window `divisor` data;
  §4 supplies the per-window *count*, and the left half `Re ρ < 1/2` needs the
  functional-equation reflection `ρ ↦ 1 − ρ̄` (mathlib `completedLFunction` — NOT landed here).
* **A3 — `∑′_{|ρ| ≤ T} |ρ|^{−1} ≪ (log qT)²`.** Batch A2's enumeration by unit windows and feed
  §4's count; the harmonic sum over `⌈T⌉` windows supplies the second `log`. (Needed only for
  the `Re ρ ≤ 4/5` discard of HB p.208, not for the capstone.)
* **A4 — the `y^{β₀}/β₀` isolation and the `y^{1/4} log y` prime-power tail**, then the
  assembly `A1 ∘ (capstone) ∘ A2 ∘ A3`.

Nothing here is stated as a hypothesis-carrying shell: every result in this file is
unconditional at the stated hypotheses (the capstone's `h₁`/`h₂` are the *conclusions* of A1,
carried as hypotheses precisely so that `ShiftVariants.lean` needs no edit today).
-/

namespace Salt.SW

open Complex Metric MeromorphicOn DirichletCharacter Set Filter ArithmeticFunction
open Salt.LS
open scoped Topology

/-! ## 1. The sharp carrier at a real argument, and the ruled truncation height -/

/-- **The sharp `χ`-Chebyshev carrier at a real argument**, `ψ(y,χ) = ∑_{n ≤ y} Λ(n)·χ(n)`.
The `ℕ`-argument carrier is `Salt.LS.psiChi`; this is its real-argument packaging (the shape
the explicit formula is stated in). -/
noncomputable def psiChiR {q : ℕ} (y : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  psiChi ⌊y⌋₊ χ

lemma psiChiR_def {q : ℕ} (y : ℝ) (χ : DirichletCharacter ℂ q) :
    psiChiR y χ = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (vonMangoldt n : ℂ) * χ (n : ZMod q) := rfl

/-- **The N0 truncation height**, `T = (log q + 2)⁴` — the kernel record of the ⟦N0 CLEAR⟧
ruling (`docs/blueprints/flags.md`): the fulcrum campaign truncates the explicit formula at
polylog height `(log q)⁴`, *not* at the disc height `q²`. The `+2` guard makes `T ≥ 16`
unconditionally, discharging every `T ≥ 2` side condition. -/
noncomputable def efHeight (q : ℕ) : ℝ := (Real.log q + 2) ^ 4

/-- The ruled height is `≥ 16` for every modulus `q ≥ 1` (`log q ≥ 0`). -/
lemma sixteen_le_efHeight {q : ℕ} (hq : 1 ≤ q) : (16 : ℝ) ≤ efHeight q := by
  have hlog : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  rw [efHeight]
  calc (16 : ℝ) = 2 ^ 4 := by norm_num
    _ ≤ (Real.log q + 2) ^ 4 := by
        apply pow_le_pow_left₀ (by norm_num) (by linarith)

lemma efHeight_pos {q : ℕ} (hq : 1 ≤ q) : (0 : ℝ) < efHeight q := by
  linarith [sixteen_le_efHeight hq]

/-! ## 2. The Λ-mass of the new range

The first difference of the Riesz carrier picks up the `Λ`-mass of the newly admitted integers;
this section bounds that mass by `(y − x + 1)·log y`, the *only* arithmetic input the bridge
needs (`Λ(n) ≤ log n`, mathlib's `vonMangoldt_le_log`). -/

/-- The newly-admitted index set sits inside `Ioc`. -/
lemma sdiff_Icc_subset_Ioc (a b : ℕ) :
    Finset.Icc 1 b \ Finset.Icc 1 a ⊆ Finset.Ioc a b := by
  intro n hn
  rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc] at hn
  obtain ⟨⟨h1, h2⟩, hna⟩ := hn
  rw [Finset.mem_Ioc]
  refine ⟨?_, h2⟩
  by_contra h
  exact hna ⟨h1, not_lt.mp h⟩

/-- Every newly-admitted index exceeds `x` (the floor step). -/
lemma lt_of_mem_sdiff_Icc {x y : ℝ} {n : ℕ}
    (hn : n ∈ Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊) : x < (n : ℝ) := by
  rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc] at hn
  obtain ⟨⟨h1, _⟩, hna⟩ := hn
  have hfl : ⌊x⌋₊ < n := by
    by_contra h
    exact hna ⟨h1, not_lt.mp h⟩
  have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hfl
  have h1' : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  linarith

/-- **The Λ-mass of the newly-admitted range.** For `1 ≤ x ≤ y`,
`∑_{⌊x⌋ < n ≤ ⌊y⌋} Λ(n) ≤ (y − x + 1)·log y`. Each term is `≤ log n ≤ log y`
(`vonMangoldt_le_log`), and the range has at most `y − x + 1` members. -/
lemma vonMangoldt_mass_sdiff_le {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n ≤ (y - x + 1) * Real.log y := by
  have hy1 : (1 : ℝ) ≤ y := le_trans hx hxy
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
  -- pointwise: `Λ n ≤ log y`
  have hpt : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n ≤ Real.log y := by
    intro n hn
    rw [Finset.mem_sdiff, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, -⟩ := hn
    have hny : (n : ℝ) ≤ y := le_trans (by exact_mod_cast h2) (Nat.floor_le (by linarith))
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    exact le_trans vonMangoldt_le_log (Real.log_le_log (by linarith) hny)
  -- cardinality: at most `y − x + 1`
  have hcard : ((Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊).card : ℝ) ≤ y - x + 1 := by
    have hsub := Finset.card_le_card (sdiff_Icc_subset_Ioc ⌊x⌋₊ ⌊y⌋₊)
    rw [Nat.card_Ioc] at hsub
    have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
    have hcast : ((⌊y⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) = (⌊y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := Nat.cast_sub hfl
    have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
    have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    calc ((Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊).card : ℝ) ≤ ((⌊y⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast hsub
      _ = (⌊y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := hcast
      _ ≤ y - x + 1 := by linarith
  calc ∑ n ∈ Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n
      ≤ (Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊).card • Real.log y :=
        Finset.sum_le_card_nsmul _ _ _ hpt
    _ = ((Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊).card : ℝ) * Real.log y := by
        rw [nsmul_eq_mul]
    _ ≤ (y - x + 1) * Real.log y := by
        exact mul_le_mul_of_nonneg_right hcard hlogy

/-! ## 3. THE BRIDGE — the sharp carrier from the smoothed one by first differencing

The corpus's contour machinery is stated for the *Riesz* carrier `ψ₁` (`Salt/SW/Defs.lean`),
because the smoothed Mellin kernel `x^{s+1}/(s(s+1))` converges absolutely — the sharp-cutoff
Perron step is the one the corpus cannot take (`Salt/SW/Kernel.lean`). The first difference
`h^{−1}(ψ₁(y+h) − ψ₁(y))` recovers the sharp `ψ(y)` up to the `Λ`-mass of `(y, y+h]`, which
§2 bounds. This is the ℂ-character analogue of the landed real AP sandwich
(`psi1AP_sandwich`), stated as a norm bound because `χ` is complex-valued (no order). -/

/-- **The first-difference identity for the ℂ character Riesz carrier.** For `x ≤ y`,

    ψ₁(y,χ) − ψ₁(x,χ) = (y − x)·ψ(x,χ) + ∑_{⌊x⌋ < n ≤ ⌊y⌋} Λ(n)·χ(n)·(y − n).

Exact, no hypotheses beyond `x ≤ y`: the common range contributes `(y − x)` times the sharp
carrier, and the newly-admitted range carries the Riesz weight `y − n`. -/
theorem psi1Chi_sub_eq {q : ℕ} {x y : ℝ} (hxy : x ≤ y) (χ : DirichletCharacter ℂ q) :
    psi1Chi y χ - psi1Chi x χ
      = ((y : ℂ) - (x : ℂ)) * psiChiR x χ
        + ∑ n ∈ Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊,
            (vonMangoldt n : ℂ) * χ (n : ZMod q) * ((y : ℂ) - n) := by
  classical
  have hsub : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.Icc 1 ⌊y⌋₊ := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 (Nat.floor_mono hxy)⟩
  set F : ℕ → ℂ := fun n => (vonMangoldt n : ℂ) * χ (n : ZMod q) with hF
  have hyE : psi1Chi y χ = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, F n * ((y : ℂ) - n) := by
    rw [psi1Chi]
  have hxE : psi1Chi x χ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n * ((x : ℂ) - n) := by
    rw [psi1Chi]
  have hsplit := Finset.sum_sdiff (f := fun n => F n * ((y : ℂ) - n)) hsub
  have hmain : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n * ((y : ℂ) - n)
      - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n * ((x : ℂ) - n)
      = ((y : ℂ) - (x : ℂ)) * psiChiR x χ := by
    rw [psiChiR_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by rw [hF]; ring)
  have hgoal : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊,
      (vonMangoldt n : ℂ) * χ (n : ZMod q) * ((y : ℂ) - n)
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊x⌋₊, F n * ((y : ℂ) - n) :=
    Finset.sum_congr rfl (fun n _ => by rw [hF])
  rw [hyE, hxE, hgoal, ← hsplit]
  linear_combination hmain

/-- **THE BRIDGE (N1 wave 1's main deliverable).** For `1 ≤ y` and `h > 0`, the first
difference of the Riesz carrier reproduces the sharp carrier to within the `Λ`-mass of the
step:

    ‖ψ(y,χ) − h^{−1}(ψ₁(y+h,χ) − ψ₁(y,χ))‖ ≤ (h + 1)·log(y + h).

Unconditional: no primitivity, no zero hypothesis, no constraint on `q`. This is the piece
that converts the corpus's smoothed contour architecture into the sharp explicit formula's
left-hand side; at the campaign step `h = y/T` (below) the cost is `(y/T)·log(qy) + log(qy)`,
inside HB p.208's `O(yT^{−1}(log qy)²)`. -/
theorem psiChiR_sub_riesz_diff_le {q : ℕ} {y h : ℝ} (hy : 1 ≤ y) (hh : 0 < h)
    (χ : DirichletCharacter ℂ q) :
    ‖psiChiR y χ - (psi1Chi (y + h) χ - psi1Chi y χ) / (h : ℂ)‖
      ≤ (h + 1) * Real.log (y + h) := by
  classical
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hyh : y ≤ y + h := by linarith
  have hyh1 : (1 : ℝ) ≤ y + h := by linarith
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set S : Finset ℕ := Finset.Icc 1 ⌊y + h⌋₊ \ Finset.Icc 1 ⌊y⌋₊ with hS
  set R : ℂ := ∑ n ∈ S, (vonMangoldt n : ℂ) * χ (n : ZMod q) * (((y + h : ℝ) : ℂ) - n) with hR
  have hid : psi1Chi (y + h) χ - psi1Chi y χ = (h : ℂ) * psiChiR y χ + R := by
    have := psi1Chi_sub_eq (x := y) (y := y + h) hyh χ
    rw [← hS, ← hR] at this
    rw [this]; push_cast; ring
  -- the algebra: the difference is `−R/h`
  have hkey : psiChiR y χ - (psi1Chi (y + h) χ - psi1Chi y χ) / (h : ℂ) = -(R / (h : ℂ)) := by
    rw [hid]; field_simp; ring
  -- the term bound: `‖Λ(n)χ(n)(y+h−n)‖ ≤ Λ(n)·h` on the newly-admitted range
  have hterm : ∀ n ∈ S,
      ‖(vonMangoldt n : ℂ) * χ (n : ZMod q) * (((y + h : ℝ) : ℂ) - n)‖ ≤ vonMangoldt n * h := by
    intro n hn
    have hgt : y < (n : ℝ) := lt_of_mem_sdiff_Icc (by rw [hS] at hn; exact hn)
    have hle : (n : ℝ) ≤ y + h := by
      rw [hS, Finset.mem_sdiff, Finset.mem_Icc] at hn
      exact le_trans (by exact_mod_cast hn.1.2) (Nat.floor_le (by linarith))
    have hcast : ((y + h : ℝ) : ℂ) - (n : ℂ) = ((y + h - n : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ y + h - n)]
    have hχ1 : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one _
    have hΛ : (0 : ℝ) ≤ vonMangoldt n := vonMangoldt_nonneg
    calc vonMangoldt n * ‖χ (n : ZMod q)‖ * (y + h - n)
        ≤ vonMangoldt n * 1 * h := by
          apply mul_le_mul _ (by linarith) (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_left hχ1 hΛ
      _ = vonMangoldt n * h := by ring
  have hRnorm : ‖R‖ ≤ h * ((h + 1) * Real.log (y + h)) := by
    have h1 : ‖R‖ ≤ ∑ n ∈ S, vonMangoldt n * h := le_trans (norm_sum_le _ _)
      (Finset.sum_le_sum hterm)
    have h2 : ∑ n ∈ S, vonMangoldt n * h = (∑ n ∈ S, vonMangoldt n) * h := by
      rw [Finset.sum_mul]
    have h3 : ∑ n ∈ S, vonMangoldt n ≤ (h + 1) * Real.log (y + h) := by
      have := vonMangoldt_mass_sdiff_le (x := y) (y := y + h) hy hyh
      rw [hS]
      calc ∑ n ∈ Finset.Icc 1 ⌊y + h⌋₊ \ Finset.Icc 1 ⌊y⌋₊, vonMangoldt n
          ≤ (y + h - y + 1) * Real.log (y + h) := this
        _ = (h + 1) * Real.log (y + h) := by ring
    rw [h2] at h1
    calc ‖R‖ ≤ (∑ n ∈ S, vonMangoldt n) * h := h1
      _ ≤ ((h + 1) * Real.log (y + h)) * h := by
          exact mul_le_mul_of_nonneg_right h3 hh.le
      _ = h * ((h + 1) * Real.log (y + h)) := by ring
  rw [hkey, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh,
    div_le_iff₀ hh]
  linarith [hRnorm]

/-- **THE COMPOSITION SOCKET.** Whatever main term `A(x)` a contour shift produces for the
*smoothed* carrier at the two points `y` and `y+h` — with errors `E₁`, `E₂` — the *sharp*
carrier inherits the first difference of that main term, at total error
`(h+1)·log(y+h) + (E₁+E₂)/h`:

    ‖ψ₁(y,χ) − A₁‖ ≤ E₁,  ‖ψ₁(y+h,χ) − A₂‖ ≤ E₂
      ⟹  ‖ψ(y,χ) − (A₂ − A₁)/h‖ ≤ (h+1)·log(y+h) + (E₁+E₂)/h.

This is the socket wave 2 plugs the enumerated contour shift into (`A(x)` = the enumerated
residue sum `−∑_{ρ ∈ Z} x^{ρ+1}/(ρ(ρ+1))`, `E` = the landed `psi1_contour_shift` bound); it is
stated abstractly so that nothing in `Salt/SW/ShiftVariants.lean` needs modifying. -/
theorem psi_sharp_of_riesz_bounds {q : ℕ} {y h : ℝ} (hy : 1 ≤ y) (hh : 0 < h)
    (χ : DirichletCharacter ℂ q) {A₁ A₂ : ℂ} {E₁ E₂ : ℝ}
    (h₁ : ‖psi1Chi y χ - A₁‖ ≤ E₁) (h₂ : ‖psi1Chi (y + h) χ - A₂‖ ≤ E₂) :
    ‖psiChiR y χ - (A₂ - A₁) / (h : ℂ)‖ ≤ (h + 1) * Real.log (y + h) + (E₁ + E₂) / h := by
  have hbase := psiChiR_sub_riesz_diff_le hy hh χ
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hsplit : psiChiR y χ - (A₂ - A₁) / (h : ℂ)
      = (psiChiR y χ - (psi1Chi (y + h) χ - psi1Chi y χ) / (h : ℂ))
        + ((psi1Chi (y + h) χ - A₂) - (psi1Chi y χ - A₁)) / (h : ℂ) := by
    field_simp
    ring
  have hdiff : ‖((psi1Chi (y + h) χ - A₂) - (psi1Chi y χ - A₁)) / (h : ℂ)‖ ≤ (E₁ + E₂) / h := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh,
      div_le_div_iff_of_pos_right hh]
    calc ‖(psi1Chi (y + h) χ - A₂) - (psi1Chi y χ - A₁)‖
        ≤ ‖psi1Chi (y + h) χ - A₂‖ + ‖psi1Chi y χ - A₁‖ := norm_sub_le _ _
      _ ≤ E₂ + E₁ := add_le_add h₂ h₁
      _ = E₁ + E₂ := by ring
  calc ‖psiChiR y χ - (A₂ - A₁) / (h : ℂ)‖
      ≤ ‖psiChiR y χ - (psi1Chi (y + h) χ - psi1Chi y χ) / (h : ℂ)‖
        + ‖((psi1Chi (y + h) χ - A₂) - (psi1Chi y χ - A₁)) / (h : ℂ)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ (h + 1) * Real.log (y + h) + (E₁ + E₂) / h := add_le_add hbase hdiff

/-- **The campaign form of the bridge**, at the differencing step `h = y/T` HB's p.208 error
budget prices. For `q ≥ 2`, `y ≥ 2`, `T ≥ 2`:

    ‖ψ(y,χ) − (y/T)^{−1}·(ψ₁(y + y/T, χ) − ψ₁(y,χ))‖ ≤ (y/T)·log(qy) + log(qy).

The right-hand side is HB's `O(yT^{−1}(log qy)²) + O(log qy)` genre with **one** power of the
log spent, so the ⟦N8/N9⟧ B-degree-≤-2 port invariant survives the de-smoothing with a full
power of `log qy` still unspent for the contour side. Minted constant: `C_EF = 1`. -/
theorem psi_sharp_riesz_at_height {q : ℕ} {y T : ℝ} (hq : 2 ≤ q) (hy : 2 ≤ y) (hT : 2 ≤ T)
    (χ : DirichletCharacter ℂ q) :
    ‖psiChiR y χ - (psi1Chi (y + y / T) χ - psi1Chi y χ) / ((y / T : ℝ) : ℂ)‖
      ≤ (y / T) * Real.log ((q : ℝ) * y) + Real.log ((q : ℝ) * y) := by
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hh : (0 : ℝ) < y / T := by positivity
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hbase := psiChiR_sub_riesz_diff_le (q := q) (y := y) (h := y / T) hy1 hh χ
  -- `y + y/T ≤ q·y` (since `1 + 1/T ≤ 3/2 ≤ q`), so the log comparison is free
  have hstep : y + y / T ≤ (q : ℝ) * y := by
    have h1 : y / T ≤ y / 2 := by
      apply div_le_div_of_nonneg_left (by linarith) (by norm_num) hT
    nlinarith [hqR, hy1]
  have hlog : Real.log (y + y / T) ≤ Real.log ((q : ℝ) * y) :=
    Real.log_le_log (by positivity) hstep
  have hcoef : (0 : ℝ) ≤ y / T + 1 := by positivity
  calc ‖psiChiR y χ - (psi1Chi (y + y / T) χ - psi1Chi y χ) / ((y / T : ℝ) : ℂ)‖
      ≤ (y / T + 1) * Real.log (y + y / T) := hbase
    _ ≤ (y / T + 1) * Real.log ((q : ℝ) * y) := mul_le_mul_of_nonneg_left hlog hcoef
    _ = (y / T) * Real.log ((q : ℝ) * y) + Real.log ((q : ℝ) * y) := by ring

/-! ## 3b. The residue de-smoothing — one zero at a time

The bridge delivers the *first difference* of whatever main term the smoothed contour shift
produces. The smoothed residue at a zero `ρ` is `x^{ρ+1}/(ρ(ρ+1))` (the Riesz kernel's), while
the sharp explicit formula's term is `y^ρ/ρ`. They are related by `φ'(x) = x^ρ/ρ` for
`φ(x) = x^{ρ+1}/(ρ(ρ+1))`, so the difference quotient converges to the sharp term with the
mean-value error priced here. -/

/-- **The residue de-smoothing, per zero.** For `0 < Re ρ ≤ 1`, `y ≥ 1` and `h > 0`,

    ‖(y+h)^{ρ+1}/(ρ(ρ+1)) − y^{ρ+1}/(ρ(ρ+1)) − h·y^ρ/ρ‖ ≤ h²·y^{Re ρ − 1},

i.e. after dividing by `h`: the first difference of the *Riesz* residue equals the *sharp*
explicit-formula term `y^ρ/ρ` up to `h·y^{Re ρ − 1}`. At the campaign step `h = y/T` this is
`y^{Re ρ}/T` per zero — a `1/T` saving against the term itself, which is exactly what makes the
de-smoothing free inside HB's `O(yT^{−1}(log qy)²)`.

Route: the mean value inequality for `ψ(u) = u^{ρ+1}/(ρ(ρ+1)) − u·(y^ρ/ρ)` on `[y, y+h]`
(`ψ' = (u^ρ − y^ρ)/ρ`), with `‖u^ρ − y^ρ‖ ≤ ‖ρ‖·y^{Re ρ−1}·(u−y)` from the landed segment
bound `norm_ofReal_cpow_seg_le`. Mirrors `cpow_unit_tangent_bound` at a general step. -/
theorem cpow_riesz_residue_desmooth {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re ≤ 1) {y h : ℝ}
    (hy : 1 ≤ y) (hh : 0 < h) :
    ‖((y + h : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) - ((y : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))
        - (h : ℂ) * (((y : ℝ) : ℂ) ^ ρ / ρ)‖
      ≤ h ^ 2 * y ^ (ρ.re - 1) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hρne : ρ ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρ1ne : ρ + 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  set c : ℂ := ((y : ℝ) : ℂ) ^ ρ / ρ with hc
  set S : Set ℝ := Set.Icc y (y + h) with hSdef
  have hconv : Convex ℝ S := convex_Icc _ _
  set ψ : ℝ → ℂ := fun u => (u : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) - (u : ℂ) * c with hψ
  have hofReal : ∀ u : ℝ, HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := by
    intro u; simpa using (hasDerivAt_id u).ofReal_comp
  have hderiv : ∀ u ∈ S, HasDerivWithinAt ψ ((u : ℂ) ^ ρ / ρ - c) S u := by
    intro u hu
    rw [hSdef, Set.mem_Icc] at hu
    have hu0 : u ≠ 0 := by have : (0 : ℝ) < u := lt_of_lt_of_le hy0 hu.1; linarith
    have h1 : HasDerivAt (fun v : ℝ => (v : ℂ) ^ (ρ + 1)) ((ρ + 1) * (u : ℂ) ^ (ρ + 1 - 1)) u :=
      hasDerivAt_ofReal_cpow_const hu0 hρ1ne
    have h2 : HasDerivAt (fun v : ℝ => (v : ℂ) * c) c u := by
      simpa using (hofReal u).mul_const c
    have h3 : HasDerivAt ψ ((ρ + 1) * (u : ℂ) ^ (ρ + 1 - 1) / (ρ * (ρ + 1)) - c) u :=
      (h1.div_const _).sub h2
    have heq : (ρ + 1) * (u : ℂ) ^ (ρ + 1 - 1) / (ρ * (ρ + 1)) = (u : ℂ) ^ ρ / ρ := by
      rw [show ρ + 1 - 1 = ρ from by ring]
      field_simp
    rw [heq] at h3
    exact h3.hasDerivWithinAt
  have hbound : ∀ u ∈ S, ‖(u : ℂ) ^ ρ / ρ - c‖ ≤ h * y ^ (ρ.re - 1) := by
    intro u hu
    rw [hSdef, Set.mem_Icc] at hu
    have huy : y ≤ u := hu.1
    have hseg : ‖(u : ℂ) ^ ρ - ((y : ℝ) : ℂ) ^ ρ‖ ≤ (‖ρ‖ * y ^ (ρ.re - 1)) * (u - y) := by
      refine norm_ofReal_cpow_seg_le hρne hy0 huy ?_
      intro w hw1 _
      have hw0 : (0 : ℝ) < w := lt_of_lt_of_le hy0 hw1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw0, Complex.sub_re, Complex.one_re]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hy0 hw1 (by linarith)) (norm_nonneg ρ)
    have hρnorm : (0 : ℝ) < ‖ρ‖ := norm_pos_iff.mpr hρne
    have hdiff : (u : ℂ) ^ ρ / ρ - c = ((u : ℂ) ^ ρ - ((y : ℝ) : ℂ) ^ ρ) / ρ := by
      rw [hc]; ring
    rw [hdiff, norm_div, div_le_iff₀ hρnorm]
    calc ‖(u : ℂ) ^ ρ - ((y : ℝ) : ℂ) ^ ρ‖ ≤ (‖ρ‖ * y ^ (ρ.re - 1)) * (u - y) := hseg
      _ ≤ (‖ρ‖ * y ^ (ρ.re - 1)) * h := by
          refine mul_le_mul_of_nonneg_left (by linarith [hu.2]) ?_
          exact mul_nonneg (norm_nonneg ρ) (Real.rpow_nonneg hy0.le _)
      _ = h * y ^ (ρ.re - 1) * ‖ρ‖ := by ring
  have hyS : y ∈ S := by rw [hSdef, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
  have hyhS : y + h ∈ S := by rw [hSdef, Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hyS hyhS
  have hψdiff : ψ (y + h) - ψ y
      = ((y + h : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) - ((y : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))
        - (h : ℂ) * (((y : ℝ) : ℂ) ^ ρ / ρ) := by
    simp only [hψ, hc]; push_cast; ring
  rw [← hψdiff]
  refine le_trans hmvt (le_of_eq ?_)
  rw [Real.norm_eq_abs, show y + h - y = h from by ring, abs_of_pos hh]
  ring

/-- **The enumerated sharp zero sum** `∑_{ρ ∈ Z} y^ρ/ρ` — the explicit formula's zero term,
over an explicitly enumerated finite zero set (this is what replaces the corpus's `hzf`
"no zeros here" hypothesis). -/
noncomputable def efZeroSum (Z : Finset ℂ) (y : ℝ) : ℂ := ∑ ρ ∈ Z, ((y : ℝ) : ℂ) ^ ρ / ρ

/-- **The enumerated Riesz residue sum** `∑_{ρ ∈ Z} x^{ρ+1}/(ρ(ρ+1))` — the residue an
enumerated contour shift of the *smoothed* carrier `ψ₁` produces (the shape of
`psi1_contour_shift_exceptional`'s single-zero residue, summed). -/
noncomputable def efRieszSum (Z : Finset ℂ) (x : ℝ) : ℂ :=
  ∑ ρ ∈ Z, ((x : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))

/-- **The residue de-smoothing, summed over an enumerated zero set.** If every enumerated zero
has `0 < Re ρ ≤ σ ≤ 1`, then the first difference of the Riesz residue sum is the sharp zero
sum up to `#Z·h·y^{σ−1}`:

    ‖h^{−1}(𝓡(y+h) − 𝓡(y)) − ∑_{ρ ∈ Z} y^ρ/ρ‖ ≤ #Z · h · y^{σ−1}.

At the campaign step `h = y/T` the right-hand side is `#Z·y^σ/T`, i.e. a full `1/T` below the
zero sum's own size — the de-smoothing is free inside HB p.208's budget. Together with
`psi_sharp_of_riesz_bounds` this reduces `psi_explicit_sharp` to A1 + A2 (module docstring). -/
theorem efRieszSum_diff_sub_efZeroSum_le {Z : Finset ℂ} {σ : ℝ} (hσ : σ ≤ 1)
    (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ σ) {y h : ℝ} (hy : 1 ≤ y) (hh : 0 < h) :
    ‖(efRieszSum Z (y + h) - efRieszSum Z y) / (h : ℂ) - efZeroSum Z y‖
      ≤ (Z.card : ℝ) * (h * y ^ (σ - 1)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set D : ℂ → ℂ := fun ρ => ((y + h : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))
    - ((y : ℝ) : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) - (h : ℂ) * (((y : ℝ) : ℂ) ^ ρ / ρ) with hD
  have hDsum : ∑ ρ ∈ Z, D ρ
      = (efRieszSum Z (y + h) - efRieszSum Z y) - (h : ℂ) * efZeroSum Z y := by
    simp only [hD, efRieszSum, efZeroSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hid : (efRieszSum Z (y + h) - efRieszSum Z y) / (h : ℂ) - efZeroSum Z y
      = (∑ ρ ∈ Z, D ρ) / (h : ℂ) := by
    rw [hDsum]; field_simp
  have hterm : ∀ ρ ∈ Z, ‖D ρ‖ ≤ h ^ 2 * y ^ (σ - 1) := by
    intro ρ hρ
    obtain ⟨hρ0, hρσ⟩ := hZ ρ hρ
    have hbase := cpow_riesz_residue_desmooth hρ0 (le_trans hρσ hσ) hy hh
    have hmono : y ^ (ρ.re - 1) ≤ y ^ (σ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hy (by linarith)
    calc ‖D ρ‖ ≤ h ^ 2 * y ^ (ρ.re - 1) := hbase
      _ ≤ h ^ 2 * y ^ (σ - 1) := by
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have hsum : ‖∑ ρ ∈ Z, D ρ‖ ≤ (Z.card : ℝ) * (h ^ 2 * y ^ (σ - 1)) := by
    calc ‖∑ ρ ∈ Z, D ρ‖ ≤ ∑ ρ ∈ Z, ‖D ρ‖ := norm_sum_le _ _
      _ ≤ ∑ _ρ ∈ Z, h ^ 2 * y ^ (σ - 1) := Finset.sum_le_sum hterm
      _ = (Z.card : ℝ) * (h ^ 2 * y ^ (σ - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, div_le_iff₀ hh]
  calc ‖∑ ρ ∈ Z, D ρ‖ ≤ (Z.card : ℝ) * (h ^ 2 * y ^ (σ - 1)) := hsum
    _ = (Z.card : ℝ) * (h * y ^ (σ - 1)) * h := by ring

/-- **THE NODE'S CAPSTONE — the sharp explicit formula from enumerated smoothed residues.**
Given the enumerated contour shift for the *smoothed* carrier at the two points `y`, `y+h`
(hypotheses `h₁`, `h₂`: the shape `psi1_contour_shift_exceptional` produces, with its single
residue `x^{β₁+1}/(β₁(β₁+1))` replaced by the enumerated `efRieszSum`), the **sharp** explicit
formula holds with the **enumerated** zero sum:

    ‖ψ(y,χ) + ∑_{ρ ∈ Z} y^ρ/ρ‖ ≤ (h+1)·log(y+h) + (E₁+E₂)/h + #Z·h·y^{σ−1}.

This is `psi_explicit_sharp` with A1 (the enumerated contour shift, `docstring`) as its only
remaining input: the de-smoothing (`efRieszSum_diff_sub_efZeroSum_le`) and the sharp/smoothed
bridge (`psi_sharp_of_riesz_bounds`) are both discharged here. At `h = y/T`, `E ≍ y(log qy)²/T`
the right-hand side is HB p.208's `O(yT^{−1}(log qy)²)` genre. -/
theorem psi_explicit_sharp_of_riesz_residues {q : ℕ} {Z : Finset ℂ} {σ : ℝ} (hσ : σ ≤ 1)
    (hZ : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re ≤ σ) {y h : ℝ} (hy : 1 ≤ y) (hh : 0 < h)
    (χ : DirichletCharacter ℂ q) {E₁ E₂ : ℝ}
    (h₁ : ‖psi1Chi y χ + efRieszSum Z y‖ ≤ E₁)
    (h₂ : ‖psi1Chi (y + h) χ + efRieszSum Z (y + h)‖ ≤ E₂) :
    ‖psiChiR y χ + efZeroSum Z y‖
      ≤ (h + 1) * Real.log (y + h) + (E₁ + E₂) / h + (Z.card : ℝ) * (h * y ^ (σ - 1)) := by
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hsock := psi_sharp_of_riesz_bounds (A₁ := -efRieszSum Z y)
    (A₂ := -efRieszSum Z (y + h)) hy hh χ (by simpa using h₁) (by simpa using h₂)
  have hdes := efRieszSum_diff_sub_efZeroSum_le hσ hZ hy hh
  have hsplit : psiChiR y χ + efZeroSum Z y
      = (psiChiR y χ - (-efRieszSum Z (y + h) - -efRieszSum Z y) / (h : ℂ))
        - ((efRieszSum Z (y + h) - efRieszSum Z y) / (h : ℂ) - efZeroSum Z y) := by
    field_simp
    ring
  rw [hsplit]
  calc ‖(psiChiR y χ - (-efRieszSum Z (y + h) - -efRieszSum Z y) / (h : ℂ))
        - ((efRieszSum Z (y + h) - efRieszSum Z y) / (h : ℂ) - efZeroSum Z y)‖
      ≤ ‖psiChiR y χ - (-efRieszSum Z (y + h) - -efRieszSum Z y) / (h : ℂ)‖
        + ‖(efRieszSum Z (y + h) - efRieszSum Z y) / (h : ℂ) - efZeroSum Z y‖ :=
        norm_sub_le _ _
    _ ≤ ((h + 1) * Real.log (y + h) + (E₁ + E₂) / h) + (Z.card : ℝ) * (h * y ^ (σ - 1)) :=
        add_le_add hsock hdes
    _ = (h + 1) * Real.log (y + h) + (E₁ + E₂) / h + (Z.card : ℝ) * (h * y ^ (σ - 1)) := by ring

/-! ## 4. The zero-enumeration supply — the Dirichlet-`L` half-box count

An *enumerated* `∑_{|γ| ≤ T}` is built one unit window at a time, and each window needs a
cardinality bound. The corpus has this for ζ (`Salt/SW/BoxCount.lean`, node A1-ab); this
section is its Dirichlet-`L` analogue, uniform in `q` and in the height `t₀`.

The landed `LFunction_growth_sphere` is at radius `7/4`, whose ball
`closedBall (2+it₀) (3/2)` reaches only `Re ≥ 1/2` **at zero height offset** — the corners
`(1/2, t₀ ± 1)` of the unit window sit at distance `√(13/4) ≈ 1.803` from the center and are
missed. We therefore re-derive the growth bound on the *wider* sphere `R = 39/20 = 1.95`
(still inside the `Re > 0` half-plane where `LFunction_eq_growthSum` holds: `2 − 1.95 = 1/20`)
and run the Jensen keystone at `r = 37/20 = 1.85 > 1.803`. -/

/-- The wide growth-sphere quantity for `L(·,χ)` at height `t`:
`M0Lbox(f,t) = 21·(4+|t|)·√f·(1+log f)`, the `R = 39/20` analogue of the landed
`5·(4+|t|)·√f·(1+log f)` (the `21` is `1 + 1/Re z` at the sphere's leftmost point
`Re z = 1/20`). -/
noncomputable def M0Lbox (f : ℕ) (t : ℝ) : ℝ :=
  21 * (4 + |t|) * Real.sqrt f * (1 + Real.log f)

lemma one_le_M0Lbox {f : ℕ} (hf : 2 ≤ f) (t : ℝ) : (1 : ℝ) ≤ M0Lbox f t := by
  have hfR : (2 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have h1 : (1 : ℝ) ≤ Real.sqrt f := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : (0 : ℝ) ≤ Real.log f := Real.log_nonneg (by linarith)
  have h3 : (84 : ℝ) ≤ 21 * (4 + |t|) := by have := abs_nonneg t; linarith
  have hA : (0 : ℝ) ≤ 21 * (4 + |t|) := by have := abs_nonneg t; linarith
  rw [M0Lbox]
  calc (1 : ℝ) ≤ 84 * 1 * 1 := by norm_num
    _ ≤ 21 * (4 + |t|) * Real.sqrt f * (1 + Real.log f) := by
        exact mul_le_mul (mul_le_mul h3 h1 (by norm_num) hA) (by linarith) (by norm_num)
          (by positivity)

/-- **The wide growth sphere.** On `|z − (2+it₀)| = 39/20` (real parts in `[1/20, 79/20]`),
`‖L(z,χ)‖ ≤ M0Lbox(f,t₀)`. Same route as the landed `LFunction_growth_sphere`, at the wider
radius: `1 + 1/Re z ≤ 21` and `‖z‖ ≤ 4 + |t₀|`. -/
theorem LFunction_growth_sphere_wide {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (t₀ : ℝ) :
    ∀ z ∈ Metric.sphere (2 + (t₀ : ℂ) * I) (39 / 20), ‖LFunction χ z‖ ≤ M0Lbox f t₀ := by
  intro z hz
  rw [Metric.mem_sphere, Complex.dist_eq] at hz
  have hcre : (2 + (t₀ : ℂ) * I).re = 2 := by simp
  have hzc : |z.re - 2| ≤ 39 / 20 := by
    have := Complex.abs_re_le_norm (z - (2 + (t₀ : ℂ) * I))
    rw [Complex.sub_re, hcre, hz] at this
    exact this
  have hzre : (1 : ℝ) / 20 ≤ z.re := by
    have := abs_le.mp hzc; linarith [this.1]
  have hσ : 0 < z.re := by linarith
  rw [LFunction_eq_growthSum χ hχ hf z hσ]
  have hbound := norm_growthSum_le χ hχ hf z hσ
  set P := Real.sqrt (f : ℝ) * (1 + Real.log f) with hP
  have hPnn : (0 : ℝ) ≤ P := by rw [hP]; exact sqrtlog_nonneg hf
  have h1 : 1 + 1 / z.re ≤ 21 := by
    have : 1 / z.re ≤ 20 := by rw [div_le_iff₀ hσ]; linarith
    linarith
  have hznorm : ‖z‖ ≤ 4 + |t₀| := by
    have hcnorm : ‖(2 : ℂ) + (t₀ : ℂ) * I‖ ≤ 2 + |t₀| := by
      calc ‖(2 : ℂ) + (t₀ : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(t₀ : ℂ) * I‖ := norm_add_le _ _
        _ = 2 + |t₀| := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
            norm_num
    calc ‖z‖ = ‖(2 + (t₀ : ℂ) * I) + (z - (2 + (t₀ : ℂ) * I))‖ := by ring_nf
      _ ≤ ‖(2 + (t₀ : ℂ) * I)‖ + ‖z - (2 + (t₀ : ℂ) * I)‖ := norm_add_le _ _
      _ ≤ (2 + |t₀|) + 39 / 20 := by rw [hz]; linarith [hcnorm]
      _ ≤ 4 + |t₀| := by linarith
  rw [M0Lbox, show (21 : ℝ) * (4 + |t₀|) * Real.sqrt f * (1 + Real.log f)
    = 21 * (4 + |t₀|) * P from by rw [hP]; ring]
  refine le_trans hbound ?_
  have hsr : ‖z‖ * (1 + 1 / z.re) ≤ (4 + |t₀|) * 21 :=
    mul_le_mul hznorm h1 (by positivity) (by positivity)
  calc P * ‖z‖ * (1 + 1 / z.re) = P * (‖z‖ * (1 + 1 / z.re)) := by ring
    _ ≤ P * ((4 + |t₀|) * 21) := mul_le_mul_of_nonneg_left hsr hPnn
    _ = 21 * (4 + |t₀|) * P := by ring

/-- **The logarithmic collapse of the wide growth quantity**: `log(4·M0Lbox(f,t)) ≤ 7·log Q`
with `Q = q(|t|+2)`, for `2 ≤ f ≤ q`. Factorwise (`84 ≤ Q⁴`, `4+|t| ≤ Q`, `√f ≤ Q`,
`1+log f ≤ f ≤ Q`), mirroring the landed `log_four_M0_le`. -/
lemma log_four_M0Lbox_le {f q : ℕ} {t : ℝ} (hf2 : 2 ≤ f) (hfq : f ≤ q) (hq2 : 2 ≤ q) :
    Real.log (4 * M0Lbox f t) ≤ 7 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hγ0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hf2R : (2 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf2
  have hfqR : (f : ℝ) ≤ (q : ℝ) := by exact_mod_cast hfq
  have hfpos : (0 : ℝ) < (f : ℝ) := by linarith
  set Q : ℝ := (q : ℝ) * (|t| + 2) with hQ
  have hQ4 : (4 : ℝ) ≤ Q := by rw [hQ]; nlinarith
  have hQpos : (0 : ℝ) < Q := by linarith
  have hqQ : (q : ℝ) ≤ Q := by rw [hQ]; nlinarith
  have hfQ : (f : ℝ) ≤ Q := le_trans hfqR hqQ
  have hlogf_nn : (0 : ℝ) ≤ Real.log (f : ℝ) := Real.log_nonneg (by linarith)
  have hb84 : (84 : ℝ) ≤ Q ^ 4 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hQ4 4)
  have hb1 : (4 + |t|) ≤ Q := by rw [hQ]; nlinarith
  have hQQ2 : Q ≤ Q ^ 2 := by nlinarith
  have hb2 : Real.sqrt (f : ℝ) ≤ Q := by
    rw [show Q = Real.sqrt (Q ^ 2) from (Real.sqrt_sq hQpos.le).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hb3 : (1 + Real.log (f : ℝ)) ≤ Q := by
    have hle : Real.log (f : ℝ) + 1 ≤ (f : ℝ) := by
      have h := Real.add_one_le_exp (Real.log (f : ℝ)); rwa [Real.exp_log hfpos] at h
    linarith
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (f : ℝ) := Real.sqrt_nonneg _
  have hprod : 4 * M0Lbox f t ≤ Q ^ 7 := by
    rw [M0Lbox]
    calc 4 * (21 * (4 + |t|) * Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)))
        = 84 * (4 + |t|) * Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)) := by ring
      _ ≤ Q ^ 4 * Q * Q * Q := by
          apply mul_le_mul (mul_le_mul (mul_le_mul hb84 hb1 (by linarith) (by positivity))
            hb2 hsqrt_nn (by positivity)) hb3 (by linarith) (by positivity)
      _ = Q ^ 7 := by ring
  have hMpos : (0 : ℝ) < 4 * M0Lbox f t := by
    have := one_le_M0Lbox hf2 t; linarith
  calc Real.log (4 * M0Lbox f t) ≤ Real.log (Q ^ 7) := Real.log_le_log hMpos hprod
    _ = 7 * Real.log Q := by rw [Real.log_pow]; push_cast; ring

/-- **The unit window sits in the Jensen ball.** The half-box
`{1/2 ≤ Re z ≤ 1, |Im z − t₀| ≤ 1}` — the piece of the critical strip an enumerated zero sum
batches over at height `t₀` — is contained in `closedBall (2+it₀) (37/20)`: the farthest
corner `(1/2, t₀±1)` is at distance `√(13/4) ≈ 1.803 < 1.85`. -/
lemma halfbox_subset_closedBall (t₀ : ℝ) :
    {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im - t₀| ≤ 1}
      ⊆ Metric.closedBall (2 + (t₀ : ℂ) * I) (37 / 20) := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hz
  rw [Metric.mem_closedBall, Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq]
  have hre : (z - (2 + (t₀ : ℂ) * I)).re = z.re - 2 := by simp
  have him : (z - (2 + (t₀ : ℂ) * I)).im = z.im - t₀ := by simp
  rw [hre, him]
  have habs := abs_le.mp h3
  have hsq : (z.re - 2) ^ 2 + (z.im - t₀) ^ 2 ≤ (37 / 20) ^ 2 := by nlinarith
  calc Real.sqrt ((z.re - 2) ^ 2 + (z.im - t₀) ^ 2) ≤ Real.sqrt ((37 / 20) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = 37 / 20 := Real.sqrt_sq (by norm_num)

/-- **THE WINDOW COUNT (N1's enumeration supply).** For a primitive `χ` mod `q ≥ 2` and any
height `t₀`, the zeros of `L(·,χ)` in `closedBall (2+it₀) (37/20)` — a ball containing the
whole unit window `{1/2 ≤ Re ρ ≤ 1, |Im ρ − t₀| ≤ 1}` of the critical strip
(`halfbox_subset_closedBall`) — counted with multiplicity, number at most

    (7/log(39/37))·log(q(|t₀|+2))   ( ≈ 133·log(q(|t₀|+2)) ).

Route: the landed Jensen keystone `LFunction_zero_count_le` at `r = 37/20`, `R = 39/20`,
fed by `LFunction_growth_sphere_wide` and collapsed by `log_four_M0Lbox_le`. This is the
Dirichlet-`L` analogue of the landed ζ count `Salt/SW/BoxCount.lean`. -/
theorem LFunction_halfbox_zero_count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (t₀ : ℝ) :
    ((∑ᶠ u, divisor (LFunction χ) (Metric.closedBall (2 + (t₀ : ℂ) * I) (37 / 20)) u : ℤ) : ℝ)
      ≤ (7 / Real.log (39 / 37)) * Real.log ((q : ℝ) * (|t₀| + 2)) := by
  have hlogpos : (0 : ℝ) < Real.log (39 / 37) := Real.log_pos (by norm_num)
  have hcount := LFunction_zero_count_le χ (ne_one_of_isPrimitive χ hχ hq) t₀
    (r := 37 / 20) (R := 39 / 20) (M := M0Lbox q t₀) (by norm_num) (by norm_num)
    (one_le_M0Lbox hq t₀) (LFunction_growth_sphere_wide χ hχ hq t₀)
  have hratio : (39 : ℝ) / 20 / (37 / 20) = 39 / 37 := by norm_num
  rw [hratio] at hcount
  refine le_trans hcount ?_
  rw [div_le_iff₀ hlogpos]
  have hlog4 := log_four_M0Lbox_le (f := q) (q := q) (t := t₀) hq le_rfl hq
  calc Real.log (4 * M0Lbox q t₀) ≤ 7 * Real.log ((q : ℝ) * (|t₀| + 2)) := hlog4
    _ = 7 / Real.log (39 / 37) * Real.log ((q : ℝ) * (|t₀| + 2)) * Real.log (39 / 37) := by
        field_simp

end Salt.SW
