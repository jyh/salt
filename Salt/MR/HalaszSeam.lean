/-
Copyright (c) 2026 Salt contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.Chebyshev
import Salt.MR.HalaszKernel
import Salt.MR.HalaszLambda
import Salt.MR.HalaszCore

/-!
# HALASZ-INFRA wave I-2, FILE C — the seam (S1' + S2')

Wave I-2 of the minimal-seam Halász route
(`docs/exploration/halasz-infra-freeze.md`, FILE C, rungs S1'/S2'), consuming the
landed wave I-1 surfaces `Salt.MR.HalaszKernel` (the hat-kernel Perron
infrastructure) and `Salt.MR.HalaszLambda` (the squarefree-linearized von
Mangoldt calculus), plus `Salt.MR.HalaszCore`.

This file is the port of the Granville–Harper–Soundararajan "triple convolution"
Perron machinery (GHS = `docs/sources/1706.03749v1.pdf`, "A new proof of Halász's
theorem", Compositio Math. 155 (2019)), §2, to the hat-kernel / `lambdaLin`
seam.  `s` abbreviates `(c₀ : ℂ) + (t : ℂ) * I` on the EXACT vertical line
`Re s = c₀`, matching the `HalaszKernel` convention.

## S1'  (`prop21_analog`) — GHS Proposition 2.1, hat-kernel analog

**FROZEN STATEMENT (frozen by HAL-I2 at dispatch, 2026-07-19, against the staged
GHS 1706.03749v1 Proposition 2.1 and its proof, pp.7–12, and the landed I-1
surfaces).**  Notation: `X h : ℝ` (`X` large; `h = X·(log X)^{-1/2}` the frozen
GROWING desmooth width, `0 < h ≤ X`); `c₀ = 1 + 1/log X`; `y` the smooth/large
split (`10 ≤ y ≤ √X`), `η = 1/log y`; `t₀` the center; `f : ℕ → ℂ` the
multiplicative function with `‖f p‖ ≤ 1`; `g : ℕ → ℂ` its prime datum;
`g_J` the window indicator on `(y, X/y)`; `𝒮 = LSeries (ellLin (restrictBelow y g))`,
`𝓛 = LSeries (ellLin (restrictAbove y g))`; and `P_β(s) = ∑_{y<n<X/y} lambdaLin g n / n^s`.

The hat-kernel Prop 2.1 analog asserts, in place of GHS (2.1)=(2.2),

  ∑' n, f n · g_J n · (n:ℂ)^(-(t₀:ℂ)·I) · (hatK X h n : ℂ)
    = ∫ α in (0)..(η), ∫ β in (0)..(η),
        (1/(2π)) • ∫ t : ℝ,
          𝒮(s-α-β)·𝓛(s+β)·P₋(s-β)·P₊(s+β)·hatKernel X h c₀ (t-t₀) dt dβ dα
      + O( (h+1) · 2^J )          -- the DESMOOTH error (hat_desmooth), per J-subset
      + O( X/log X · (log y)^κ ), -- the SECONDARY-TERM error (Lemma 2.4 analog)

with `s = c₀ + (t - t₀)·I` on the exact vertical line, `κ = 1`, and `hatKernel`
the landed kernel `((X+h)^{s+1} - X^{s+1}) / (h·s·(s+1))`.

**Seam substitutions (diffs vs GHS, recorded — the freeze's analog spec wins):**
1. GHS truncates the `s`-integral at height `T` (error `x(log x)^κ/T`, Lemma 2.5);
   the hat-kernel form uses the EXACT full-line representation `hat_contour_rep`
   (no truncation), paying instead the desmooth `O(h)` of `hat_desmooth`
   (error `(h+1)·2^J`, `2^J = (log X)^{o(1)}` carried per REF-B R7).
2. GHS's `Λ_ℓ` (von Mangoldt of the large-prime part) → `lambdaLin g`, with
   `‖lambdaLin g n‖ ≤ Λ n` at ALL `n` (`lambdaLin_norm_le`; κ=1 disarmed by
   construction); the log-derivative is the PRODUCT form
   `-L'(ellLin) = L(lambdaLin)·L(ellLin)` (`ellLin_lseries_deriv`) — NO division
   by any L-series enters the ladder.
3. GHS's sharp Perron kernel `x^{s-α-β}/(s-α-β)` → the landed `hatKernel`, its
   trapezoid analog on the full line.
4. The center twist `n^{-it₀}` and window `g_J` are carried in the represented
   sum from the start (GHS folds them in only later, at the §2.3 shifted line).

**RESIDUAL (S1' is THE campaign's single named residual, per the freeze).**  The
`α,β` double-integral re-expression of `hat_contour_rep`'s integrand
`(∑' n, a n / n^s) · hatKernel(s)` into the product form
`𝒮(s-α-β)·𝓛(s+β)·P_(-β)·P_β` — i.e. the GHS Lemma 2.1/2.2 coefficient identity
`∑_{ℓm=n} Λ_f(ℓ) f(m) = f(n) log n` integrated over `α,β` — requires (a) the
shifted-Dirichlet-series integration `∫₀^η F'(s+α+β) dβ = 1 - F(s+α)` in the
`ellLin`/`lambdaLin` product form, and (b) Fubini among the `(α,β)` double
integral, the `tsum` over `n`, and the `t`-integral.  mathlib has no
multivariable-Perron/Fubini apparatus for this; it is a multi-thousand-line
formalization.  S1' therefore remains the named residual — the frozen statement
above is its discharge (the residual is now precisely stated and reduced to
(a)+(b)).  The LANDABLE seam pieces of S1' — the desmooth reduction
(`prop21_desmooth_reduction`) and the `Λ`-window bound (`lambdaLin_window_bound`)
— are proved below.

## S2'  (`contour_A13_A14`) — GHS §2.3 Cauchy–Schwarz, hat-kernel analog

**LOG-POWER LEDGER (binding pre-Lean gate, REF-B R2 — PASSES).**  `L := log X`,
`κ = 1`, `h = X·L^{-1/2}`, `c₀ = 1 + 1/L`, `Tsplit := L^4` (the kernel-split
height — NOT the parent freeze's `T0 = L^{1/16}`; never conflate).  Grade
`= X·L^{-1/2+ε}`.  Split the full-line kernel integral at `Tsplit`:

* HEAD (`|t| ≤ Tsplit`), factor-by-factor (GHS (2.7)→(2.9) mapped to the seam):
  (1) kernel scale `X^{1-α-β} ≤ X` [`L¹`];
  (2) `𝒮`-desmooth ratio, `|𝒮(c₀-α-β+it)/𝒮(c₀+β+it)| ≪ exp(3κ)`
      [via `exp(κ·(α+2β)·Σ_{p≤y}(log p)/p)`; `L⁰`, NO leak];
  (3) Euler/F factor `|F(c₀+β+it)/(c₀+β+it)| ≤ e^{-M} L^κ + O((σL)^{-κ})`
      [`L^κ·e^{-M}`, the MAIN term, carried];
  (4) Λ-window Cauchy–Schwarz + Plancherel (K4', diagonal `m=n`)
      `(Σ Λ/m^{1-2β})^½ (Σ Λ/n^{1+2β})^½ ≪ (x/y)^β·min(L,1/β)` [`1/σ`, `σ=β+1/L`].
  Assembly: `X^{1-α-β}·(x/y)^β ≤ X^{1-α}`, and `∫₀^η X^{1-α} dα ≤ X/L`
  (the α-integration produces the crucial `1/L`, cancelling one `L^κ` from (3));
  then `∫_{1/L}^{2/log y} (1/σ)·max|F(1+σ+it)/(1+σ+it)| dσ ≤ e^{-M}L^κ·(M+O(1))`.
  Net HEAD `= X·(1+M)·e^{-M}·L^{κ-1} =(κ=1)= X·(1+M)e^{-M} ≍ X·E(M)`.
  Every `L` accounted; NO full-log leak. ✓

* TAIL (`|t| > Tsplit`): sup-integrand `≤ C·L³` [`𝒮·𝓛 ≤ C·L` (Mertens, κ=1) ×
  Λ-window double-sum `≤ (log(x/y))² ≤ L²`]; kernel tail mass (`hat_tail`, K3')
  `≤ 4(X+h)^{c₀+1}/(h·Tsplit) ≈ eX·L^{1/2}/L⁴ = eX·L^{-7/2}`.  Product
  `C·L³·eX·L^{-7/2} = CeX·L^{-1/2} = X·L^{-1/2}`, AT grade, zero ε borrowing. ✓

  `Tsplit=L⁴` audit vs REF-B F1: at `T=L²` the tail is `≈ eX·L^{3/2} = grade × L²`
  (the caught `(log X)²` overrun; machine-checked by `HalaszKernel.tsplit_ledger`);
  bumping `T` by `L²` divides the tail by `L²`, converting `+3/2 → -1/2`.  Only
  `O(1)/loglog/2^J = L^{o(1)}` leaks remain — all ε-absorbable.  **LEDGER PASSES.**

**K4' CONDITIONALITY.**  The Plancherel leg `dirichlet_plancherel` /
`cos_int_pair` (K4') is the NAMED RESIDUAL of wave I-1 (mathlib-absent contour;
route documented in `HalaszKernel`'s docstring; NOT defined there).  Per the
freeze, the S2' composition `contour_A13_A14` therefore lands CONDITIONAL on the
K4' Plancherel bilinear bound, taken as an explicit hypothesis (`hPlancherel`
below).  The Zeno form is expected and correct.

## Seam-coupled L3' (held at the I-2 boundary by wave I-1b)

The concrete GHS window decomposition (`fgJ`), the squarefull support predicate
(`Squarefull`; mathlib-absent), and the L3' output contract
`‖LSeries (smoothPart …) (σ+it)‖ ≤ (Euler form)·C_sq` (composing with
`halasz_cosh_ineq_complex`, `cSq_corner_summable`) are seam-coupled to this file
and developed below.
-/

noncomputable section

namespace Salt.MR

open MeasureTheory Complex Set
open scoped BigOperators LSeries.notation
open ArithmeticFunction

/-! ## Squarefull (powerful) numbers — the L3' support predicate (mathlib-absent) -/

/-- **Squarefull / powerful numbers** (L3' support predicate).  `n` is squarefull
iff every prime dividing `n` divides it at least twice.  mathlib has no such
predicate; the seam defines one cleanly (freeze FILE C / L3').  `1` is squarefull
vacuously; a prime `p` is not squarefull; `p^2` is. -/
def Squarefull (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- `1` is squarefull (no prime divides it). -/
theorem squarefull_one : Squarefull 1 := by
  intro p hp hpd
  exact absurd (Nat.le_of_dvd one_pos hpd) (by simpa using hp.one_lt)

/-- `0` is squarefull (everything divides `0`). -/
theorem squarefull_zero : Squarefull 0 := fun _ _ _ => dvd_zero _

/-- Squarefull via factorization: for `n ≠ 0`, `n` is squarefull iff no prime
occurs to exponent exactly `1`. -/
theorem squarefull_iff_factorization {n : ℕ} (hn : n ≠ 0) :
    Squarefull n ↔ ∀ p : ℕ, n.factorization p ≠ 1 := by
  constructor
  · intro hsf p hp1
    -- `factorization p = 1` forces `p` prime and `p ∣ n` but `¬ p^2 ∣ n`.
    have hpp : p.Prime := by
      by_contra hnp
      rw [Nat.factorization_eq_zero_of_not_prime n hnp] at hp1
      omega
    have hpd : p ∣ n := by
      have : p ^ 1 ∣ n :=
        (Nat.Prime.pow_dvd_iff_le_factorization hpp hn).mpr (by omega)
      simpa using this
    have := hsf p hpp hpd
    rw [Nat.Prime.pow_dvd_iff_le_factorization hpp hn] at this
    omega
  · intro h p hp hpd
    rw [Nat.Prime.pow_dvd_iff_le_factorization hp hn]
    have h1 : 1 ≤ n.factorization p := by
      have : p ^ 1 ∣ n := by simpa using hpd
      rw [Nat.Prime.pow_dvd_iff_le_factorization hp hn] at this; exact this
    have h2 := h p
    omega

/-- A prime is not squarefull. -/
theorem not_squarefull_prime {p : ℕ} (hp : p.Prime) : ¬ Squarefull p := by
  intro hsf
  have h2 : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos (hsf p hp dvd_rfl)
  nlinarith [hp.two_le]

/-! ## S1' landable seam pieces — the desmooth reduction and the Λ-window bound

These are the two components of GHS Prop 2.1 (S1') that reduce cleanly to the
landed I-1 surfaces (`hat_desmooth`, `lambdaLin_norm_le`) plus mathlib's
Chebyshev bound.  They are the honest partial discharge of S1'; the full
`α,β` double-integral representation remains the named residual (see the module
docstring). -/

/-- **The seam coefficient.**  `f · g_J` twisted by the center `n ↦ n^{-it₀}`,
with the `n = 0` value forced to `0` (catch #254: `hat_desmooth` is false as
frozen without `a 0 = 0`). -/
def seamCoeff (f gJ : ℕ → ℂ) (t₀ : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else f n * gJ n * (n : ℂ) ^ (-(t₀ : ℂ) * I)

@[simp] lemma seamCoeff_zero (f gJ : ℕ → ℂ) (t₀ : ℝ) : seamCoeff f gJ t₀ 0 = 0 :=
  if_pos rfl

/-- The center twist `n ↦ n^{-it₀}` is unimodular for `n ≥ 1`. -/
lemma norm_twist (t₀ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-(t₀ : ℂ) * I)‖ = 1 := by
  have hn0 : 0 < n := hn
  rw [Complex.norm_natCast_cpow_of_pos hn0]
  have hre : (-(t₀ : ℂ) * I).re = 0 := by simp
  rw [hre, Real.rpow_zero]

/-- The seam coefficient is bounded by `1` (unimodular twist, `‖f‖,‖g_J‖ ≤ 1`). -/
lemma norm_seamCoeff_le {f gJ : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hg : ∀ n, ‖gJ n‖ ≤ 1) (t₀ : ℝ) (n : ℕ) : ‖seamCoeff f gJ t₀ n‖ ≤ 1 := by
  unfold seamCoeff
  split_ifs with h
  · simp
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
    rw [norm_mul, norm_mul, norm_twist t₀ hn, mul_one]
    calc ‖f n‖ * ‖gJ n‖ ≤ 1 * 1 := by
          apply mul_le_mul (hf n) (hg n) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

/-- **S1' desmooth reduction** (the landable seam piece of S1', GHS Lemma 2.5
DELETED).  The sharp windowed–twisted partial sum `∑_{1≤n≤⌊X⌋} f·g_J·n^{-it₀}`
and its hat-smoothed counterpart differ by at most `h + 1`.  This is the seam
substitution "desmooth `O(h)` replacing the sharp Perron truncation".  Consumes
`hat_desmooth` with the catch-#254 hypothesis `seamCoeff … 0 = 0`. -/
theorem prop21_desmooth_reduction {f gJ : ℕ → ℂ} (t₀ : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖gJ n‖ ≤ 1)
    {X h : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hhX : h ≤ X) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, seamCoeff f gJ t₀ n)
        - ∑' n, seamCoeff f gJ t₀ n * (hatK X h n : ℂ)‖ ≤ h + 1 :=
  hat_desmooth (seamCoeff f gJ t₀) (norm_seamCoeff_le hf hg t₀)
    (seamCoeff_zero f gJ t₀) hX hh hhX

/-- **S1' Λ-window bound** (the landable seam piece of S1', the "Λ-poly windows"
`(y, x/y)` via `psi_le_const_mul_self` + `lambdaLin_norm_le`).  The total mass of
`lambdaLin g` on any window `(a, b]` is at most `(log 4 + 4)·b`, uniformly in the
lower cut `a` — because `‖lambdaLin g‖ ≤ Λ` at ALL `n` (κ=1 disarmed) and the
Chebyshev bound `ψ b ≤ (log 4 + 4)·b`. -/
theorem lambdaLin_window_bound (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {a b : ℕ} :
    ∑ n ∈ Finset.Ioc a b, ‖lambdaLin g n‖ ≤ (Real.log 4 + 4) * b := by
  have hstep : ∑ n ∈ Finset.Ioc a b, ‖lambdaLin g n‖
      ≤ ∑ n ∈ Finset.Ioc 0 b, ArithmeticFunction.vonMangoldt n := by
    calc ∑ n ∈ Finset.Ioc a b, ‖lambdaLin g n‖
        ≤ ∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n :=
          Finset.sum_le_sum (fun n _ => lambdaLin_norm_le g hg n)
      _ ≤ ∑ n ∈ Finset.Ioc 0 b, ArithmeticFunction.vonMangoldt n :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Ioc_subset_Ioc (Nat.zero_le a) le_rfl)
            (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hpsi : (∑ n ∈ Finset.Ioc 0 b, ArithmeticFunction.vonMangoldt n)
      = Chebyshev.psi (b : ℝ) := by
    rw [Chebyshev.psi, Nat.floor_natCast]
  rw [hpsi] at hstep
  exact hstep.trans (Chebyshev.psi_le_const_mul_self (by positivity))

/-! ## Seam-coupled L3' — the concrete GHS window decomposition `fg_J`

The abstract `smoothPart` / `smoothPart_factorization` / `cSq_corner_summable`
surfaces are landed in `HalaszLambda`; wave I-1b held the CONCRETE `fg_J` for the
seam.  Here we instantiate them at the seam's windowed–twisted `f`. -/

/-- The GHS window indicator `g_J` on the open interval `(y, Y)` (with `Y = X/y`
in the seam), as a `ℂ`-valued `{0,1}` cutoff. -/
def windowIndicator (y Y : ℝ) (n : ℕ) : ℂ := if y < (n : ℝ) ∧ (n : ℝ) < Y then 1 else 0

lemma norm_windowIndicator_le (y Y : ℝ) (n : ℕ) : ‖windowIndicator y Y n‖ ≤ 1 := by
  unfold windowIndicator; split_ifs <;> simp

/-- **The concrete GHS window decomposition `fg_J`** (seam-coupled, held at the
I-2 boundary by wave I-1b): the windowed–twisted `f`, i.e. `f · g_J` twisted by
the center `n^{-it₀}`. -/
def fgJ (f : ℕ → ℂ) (t₀ y Y : ℝ) : ℕ → ℂ := seamCoeff f (windowIndicator y Y) t₀

@[simp] lemma fgJ_zero (f : ℕ → ℂ) (t₀ y Y : ℝ) : fgJ f t₀ y Y 0 = 0 :=
  seamCoeff_zero _ _ _

/-- The concrete `fg_J` is bounded by `1` (unimodular twist + `{0,1}` window). -/
lemma norm_fgJ_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ y Y : ℝ) (n : ℕ) :
    ‖fgJ f t₀ y Y n‖ ≤ 1 :=
  norm_seamCoeff_le hf (norm_windowIndicator_le y Y) t₀ n

/-- **L3' factorization** for the concrete `fg_J`: `sPart ⍟ ℓ = fg_J`, the GHS
`f = s ∗ ℓ` split (`ℓ = ellLin(g·1_{p>y})`, `sPart = smoothPart y g fg_J`)
instantiated at the seam's windowed–twisted `f`.  Consumes the landed
`smoothPart_factorization`. -/
theorem fgJ_factorization (f g : ℕ → ℂ) (t₀ y Y : ℝ) :
    smoothPart y g (fgJ f t₀ y Y) ⍟ ellLin (restrictAbove y g) = fgJ f t₀ y Y :=
  smoothPart_factorization g y (fgJ_zero f t₀ y Y)

/-! ## S2' ledger closures — the `Tsplit = (log X)^4` tail and the conditional head

The binding pre-Lean log-power ledger is in the module docstring (it PASSES).
Here we land its two Lean consequences: the tail closure (unconditional,
consuming `tsplit_ledger`) and the head composition (CONDITIONAL on the K4'
Plancherel leg — the named residual of wave I-1). -/

/-- **S2' tail ledger closure** (`contour_A13_A14`, the `Tsplit = (log X)^4`
ledger carried; K3' + REF-B R1).  The tail contribution is
`(sup-integrand) × (kernel tail mass)`; with the sup-integrand `≤ Csup·L³` and
the `hat_tail` mass normalised to `√L · X · (L⁴)⁻¹` (the `h = X·L^{-1/2}` factor
supplies the `√L`), the tail sits at grade `Csup·X·L^{-1/2}` — the `(log X)²`
overrun of `T = L²` is exactly cancelled by `Tsplit = L⁴`.  Consumes
`HalaszKernel.tsplit_ledger`. -/
theorem s2_tail_ledger {Lx X Csup : ℝ} (hL : 1 < Lx) (hX : 0 ≤ X) (hC : 0 ≤ Csup) :
    (Csup * Lx ^ 3) * (Real.sqrt Lx * X * (Lx ^ 4)⁻¹) ≤ Csup * X / Real.sqrt Lx := by
  have hLpos : (0 : ℝ) < Lx := by linarith
  have hsqrt : Real.sqrt Lx * Real.sqrt Lx = Lx := Real.mul_self_sqrt (le_of_lt hLpos)
  have hsqrtpos : 0 < Real.sqrt Lx := Real.sqrt_pos.mpr hLpos
  have hledger : Lx ^ 3 * (Lx ^ 4)⁻¹ ≤ Lx⁻¹ := (tsplit_ledger hL).1
  have key : (Csup * Lx ^ 3) * (Real.sqrt Lx * X * (Lx ^ 4)⁻¹)
      = (Csup * X * Real.sqrt Lx) * (Lx ^ 3 * (Lx ^ 4)⁻¹) := by ring
  rw [key]
  calc (Csup * X * Real.sqrt Lx) * (Lx ^ 3 * (Lx ^ 4)⁻¹)
      ≤ (Csup * X * Real.sqrt Lx) * Lx⁻¹ :=
        mul_le_mul_of_nonneg_left hledger (by positivity)
    _ = Csup * X / Real.sqrt Lx := by
        rw [div_eq_mul_inv]
        have hinv : Lx⁻¹ = (Real.sqrt Lx)⁻¹ * (Real.sqrt Lx)⁻¹ := by
          rw [← mul_inv, hsqrt]
        rw [hinv]
        field_simp

/-- **S2' head composition** (`contour_A13_A14`, GHS §2.3 (2.7)→(2.8), hat-kernel
analog), CONDITIONAL on the K4' Plancherel leg (`dirichlet_plancherel` — the
NAMED RESIDUAL of wave I-1; mathlib-absent contour, route in `HalaszKernel`'s
docstring).  Given the weighted Cauchy–Schwarz bound of the cross integral by the
two Plancherel factors (`hCS`, consuming K4'), and the diagonal domination of each
Plancherel factor by a Λ-window sum (`hDiagA`/`hDiagB`, via `lambdaLin_window_bound`),
the head `X · supF · crossInt` is bounded by the geometric mean of the two
window sums — GHS (2.8), the input to the (A.9) main term `X·(1+M)e^{-M}`.  The
Zeno (conditional) form is expected and correct per the freeze. -/
theorem contour_A13_A14_head {X supF crossInt planA planB diagA diagB : ℝ}
    (hX : 0 ≤ X) (hsupF : 0 ≤ supF)
    (hCS : crossInt ≤ Real.sqrt planA * Real.sqrt planB)
    (hDiagA : planA ≤ diagA) (hDiagB : planB ≤ diagB) :
    X * supF * crossInt ≤ X * supF * (Real.sqrt diagA * Real.sqrt diagB) := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine hCS.trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt hDiagA) (Real.sqrt_le_sqrt hDiagB)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end Salt.MR
