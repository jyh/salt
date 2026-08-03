/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Defs
import Salt.BrunLower.MainTerm
import Salt.BrunLower.BlockDecomp
import Salt.HB.RosserDim4

/-!
# The fundamental-lemma packaging, the first-failure decomposition, and the per-δ transfer
(N5 wave 2)

Wave 1 (`Salt/HB/RosserDim4.lean`) instantiated Halberstam–Richert's Théorème 2 at sieve
dimension `A = 4` and proved the block-Brun **level bound** `chi_le_rpow_level`.  This file
supplies the three things Heath-Brown's p.199–200 assembly actually consumes — the scope
amendment recorded by the N5 gate check (`docs/blueprints/flags.md`).

## P1 — `fl_dim4_lower` / `fl_dim4_upper`: the fundamental-lemma consequence

HB works at level `D` with `s = (log D)/(log z) = z₀/3 → ∞` and quotes Iwaniec [10, Thm 4]
in the form `S₁′ − S₁ ≪ exp(−¼z₀)·S₁`.  The block-Brun substitute is the H-R truncation
error at the block depth `b` chosen so that *every kept `d` lies below `D`*:

* `flB s Λ = ⌊(s + 2 − levelE Λ)/2⌋₊` — the depth (`levelE Λ = 2e^Λ/(e^Λ−1)` is the
  `b`-free part of wave 1's `levelExp`).  With this `b`, `levelExp Λ ν b ≤ s` for `ν ≥ 1`,
  so `flB_level_bound` puts every kept `d` under `D = z^s`.
* `fl_defect_le` — the conversion `λ^{2b} → C·e^{−c·s}` at
  `c = flRate λ = log(1/λ)` and `C = flConst λ Λ`.

**The true constants.**  `flRate λ = log(1/λ)`; at `λ = 1/4` this is `log 4 = 1.3862…` per
unit of `s`, matching the ROSSER-SCOPE numerics exactly.  The fixed constant is
`flConst λ Λ = (2e^{2λ}/(1 − λ²e^{2+2λ}))·e^{levelE Λ·log(1/λ)}` on the **lower** side and
`λ` times that on the **upper** side.  At `λ = 1/4` the prefactor `2e^{1/2}/(1 − e^{5/2}/16)`
is `13.8203…`; at the *nominal* ladder scale `Λ = 2λ/A = λ/2 = 1/8`, `levelE = 17.0208…` and
`e^{17.0208·log 4} = e^{23.599} = 1.768·10^{10}`, giving

  `C_upper = 6.11·10^{10}`  (ROSSER-SCOPE's `6.1e10`, confirmed at the bytes),
  `C_lower = 2.44·10^{11}`  (four times it — the lower side carries `λ^{2b}`, not `λ^{2b+1}`).

At the *true* dimension-4 scale `Lam4 λ z = (λ/2)(1 − 300/loglog z)` the constant inflates
by `e^{log(1/λ)·(levelE Λ − levelE (λ/2))}` — the honest price of the (2.18) correction.
`flConst_quarter_le` records a clean envelope: for `Λ ≥ 1/10` (i.e. `loglog z ≥ 1500` at
`λ = 1/4`) `flConst (1/4) Λ ≤ 14·e^{31} = 4.07·10^{14}`; the true value there is
`13.8203·e^{29.135} = 6.22·10^{13}` (upper side `1.56·10^{13}`).

The threshold on the level ratio is `hs : levelE Λ ≤ s` (at `Λ = 1/8`: `s ≥ 17.021`), which
also forces `1 ≤ flB s Λ`.  HB's operating point `s = z₀/3 → ∞` is deep inside it.  The
defect conversion `fl_defect_le` itself is *unconditional* in `s`; the threshold is needed
only for `b ≥ 1` and for the level fit `levelExp ≤ s`.

## P2 — the first-failure decomposition (the wave's design stone)

Iwaniec's `S`-set identity (HB p.199) says: for the Rosser weights there is a set `S` with
`δ ≤ Max(D, z²)` for `δ ∈ S`, and *for any* `ρ`,
`Σ_{d∣P} ρ(d)λ_d = Σ_{d∣P} ρ(d)μ(d) + Σ_{δ∈S} Σ_{d∣P(δ)} ρ(dδ)μ(d)`.

For the **block-Brun** weight system `λ_d = μ(d)·χ_ν(d)` the identity is proved here from
scratch, with the set the kept-set's own definition supports:

  `failSet Λ z ν b P = {δ ∣ P : ¬χ_ν(δ) ∧ χ_ν(δ/p(δ))}`  — the **first-failure set**: `δ` is
  discarded, but `δ` with its *smallest* prime removed is kept.

`firstFailure_decomposition`: for any `ρ : ℕ → ℝ` and squarefree `P`,

  `Σ_{d∣P} μ(d)χ_ν(d)ρ(d) = Σ_{d∣P} μ(d)ρ(d) − Σ_{δ∈𝒮} Σ_{e∣P(δ)} μ(δe)ρ(δe)`,

where `P(δ)` is realised as `lowDiv P δ = {e ∣ P : every prime of e is < p(δ)}` (= the
divisors of `∏_{p∣P, p<p(δ)} p`).  The proof is a genuine bijection
`{d ∣ P : ¬χ_ν(d)} ≃ Σ_{δ∈𝒮} {e ∣ P(δ)}`, `d ↦ (δ, d/δ)`: existence is an induction that
strips the smallest prime (`exists_firstFailure`), uniqueness is the divisor-closure of
`χ_ν` applied to `δ/p(δ)` (`failSet_unique`).  **It is fully general in `ρ`** — no
multiplicativity, no positivity, no sign condition.

**THE SUPPORT FACT** (`failSet_le_rpow`): every `δ ∈ 𝒮` obeys
`δ ≤ z^{levelExp Λ ν b + 1}` — wave 1's level bound applied to the *kept* part `δ/p(δ)`,
times the one prime `p(δ) < z`.  So the honest δ-level costs **exactly one extra rung**
(a factor `z`), not the `z²` the brief budgeted; combined with `levelExp Λ ν b ≤ s`
(the `flB` choice) this is `δ ≤ z^{s+1} = D·z`, which is HB's `Max(D, z²)` in our units.

**THE SIGN** (`failSet_moebius`): every `δ ∈ 𝒮` has `Ω(δ) ≡ ν (mod 2)`, hence
`μ(δ) = (−1)^ν`, **constant on the whole first-failure set**.  This is H-R's (2.3) parity
mechanism read backwards: at a level `n` where `χ_ν` fails for `δ` but not for `δ/p(δ)` the
restricted count is forced to the value `2b − ν + 2n`, and at that level *all* of `δ`'s
primes are counted (`failSet_forced_count`).  It is what makes the correction one-signed —
`ν = 1` gives `+`, `ν = 2` gives `−` — and it is what lets P3's transfer go through.

## P3 — the per-δ transfer

`perDelta_transfer` / `transfer_of_decomposition`: the abstract lemma behind HB's p.200 line
`|S_i′ − S_i| ≪ BL|S₁′ − S₁|` (i = 2,3).  Given per-δ domination `|S^{(i)}(δ)| ≤ B·S^{(1)}(δ)`
with `S^{(1)}(δ) ≥ 0`, the transfer is immediate from the decomposition's shape *provided the
correction is one-signed* — which P2's `failSet_moebius` supplies.  `hb_perDelta_transfer`
is the wired form at the block-Brun weights: it takes exactly Lemma 6's per-δ hypotheses and
returns HB's display.

The `BoundingSieve` instance wiring (HB's `ρ₁ = G(d)/d`, `ρ₂ = G(d)A′(d)/d`,
`ρ₃ = G(d)A(d)²/d`) is **wave 3** and is deliberately not built here.
-/

open Finset Nat
open scoped ArithmeticFunction.Moebius

namespace Salt.HB

open Salt.BrunLower

/-! ## P1 — the fundamental-lemma packaging at dimension 4

### The level exponent's `b`-free part, and the depth `flB` -/

/-- The `b`-free part of wave 1's `levelExp`: `E(Λ) = 2e^Λ/(e^Λ − 1)`.  `E(1/8) = 17.021…`,
`E(1/10) = 21.017…`; `E(Λ) ≈ 2/Λ + 1` for small `Λ`. -/
noncomputable def levelE (Lam : ℝ) : ℝ := 2 * Real.exp Lam / (Real.exp Lam - 1)

lemma levelExp_eq_levelE (Lam : ℝ) (side b : ℕ) :
    levelExp Lam side b = 2 * b - side - 1 + levelE Lam := rfl

lemma one_lt_exp_of_pos {x : ℝ} (hx : 0 < x) : (1 : ℝ) < Real.exp x := by
  have := Real.add_one_le_exp x
  linarith

lemma levelE_pos {Lam : ℝ} (hLam : 0 < Lam) : 0 < levelE Lam := by
  have h1 : (1 : ℝ) < Real.exp Lam := one_lt_exp_of_pos hLam
  rw [levelE]
  apply _root_.div_pos (by positivity)
  linarith

/-- **The fundamental-lemma block depth.**  `b = ⌊(s + 2 − E(Λ))/2⌋` is the largest depth
whose level exponent still fits under the level ratio `s = (log D)/(log z)`. -/
noncomputable def flB (sRatio Lam : ℝ) : ℕ := ⌊(sRatio + 2 - levelE Lam) / 2⌋₊

/-- The threshold `E(Λ) ≤ s` already forces `b ≥ 1` (H-R's `hb`). -/
lemma one_le_flB {sRatio Lam : ℝ} (hs : levelE Lam ≤ sRatio) : 1 ≤ flB sRatio Lam := by
  apply Nat.le_floor
  push_cast
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- `2b ≤ s + 2 − E(Λ)` — the floor's upper half. -/
lemma two_flB_le {sRatio Lam : ℝ} (hs : levelE Lam ≤ sRatio) :
    2 * (flB sRatio Lam : ℝ) ≤ sRatio + 2 - levelE Lam := by
  have h := Nat.floor_le (a := (sRatio + 2 - levelE Lam) / 2) (by linarith)
  rw [flB]
  linarith

/-- `s − E(Λ) < 2b` — the floor's lower half, the source of the decay rate. -/
lemma sub_levelE_lt_two_flB {sRatio Lam : ℝ} :
    sRatio - levelE Lam < 2 * (flB sRatio Lam : ℝ) := by
  have h := Nat.lt_floor_add_one (a := (sRatio + 2 - levelE Lam) / 2)
  rw [flB]
  linarith

/-- **The `flB` depth fits under the level.**  `levelExp Λ ν (flB s Λ) ≤ s` for `ν ≥ 1`. -/
lemma levelExp_flB_le {sRatio Lam : ℝ} {side : ℕ} (hside : 1 ≤ side)
    (hs : levelE Lam ≤ sRatio) :
    levelExp Lam side (flB sRatio Lam) ≤ sRatio := by
  have hsd : (1 : ℝ) ≤ (side : ℝ) := by exact_mod_cast hside
  have := two_flB_le (sRatio := sRatio) (Lam := Lam) hs
  rw [levelExp_eq_levelE]
  linarith

/-- **P1(a) — every kept `d` lies under `D = z^s`.**  With the depth `b = flB s Λ`, the
block predicate's own support bound (wave 1's `chi_le_rpow_level`) puts every kept modulus
below the sieve level.  This is what makes the H-R truncation a *level-`D`* sieve. -/
theorem flB_level_bound {Lam z sRatio : ℝ} {side d : ℕ}
    (hLam : 0 < Lam) (hz : 1 < z) (hside : 1 ≤ side) (hs : levelE Lam ≤ sRatio)
    (hd : d ≠ 0) (hsq : Squarefree d) (hdz : ∀ p ∈ d.primeFactors, (p : ℝ) < z)
    (hchi : chi Lam z side (flB sRatio Lam) d) :
    (d : ℝ) ≤ z ^ sRatio :=
  le_trans (chi_le_rpow_level hLam hz hd hsq hdz hchi)
    (Real.rpow_le_rpow_of_exponent_le hz.le (levelExp_flB_le hside hs))

/-! ### The decay rate and the fixed constant -/

/-- The fundamental-lemma **decay rate per unit of `s`**: `c = log(1/λ)`.  At `λ = 1/4`,
`c = log 4 = 1.3862…`. -/
noncomputable def flRate (lam : ℝ) : ℝ := -Real.log lam

lemma flRate_pos {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) : 0 < flRate lam := by
  rw [flRate, neg_pos]
  exact Real.log_neg hlam hlam1

/-- The fundamental-lemma **fixed constant** at the ladder scale `Λ`:
`C = (2e^{2λ}/(1 − λ²e^{2+2λ}))·e^{c·E(Λ)}`.  The first factor is H-R's geometric close;
the second is the price of the `b`-to-`s` conversion. -/
noncomputable def flConst (lam Lam : ℝ) : ℝ :=
  2 * Real.exp (2 * lam) / (1 - lam ^ 2 * Real.exp (2 + 2 * lam))
    * Real.exp (flRate lam * levelE Lam)

/-- H-R's `(2.15)` side condition gives the geometric denominator's positivity. -/
lemma one_sub_lam_sq_exp_pos {lam : ℝ} (hlam : 0 < lam)
    (h12 : lam * Real.exp (1 + lam) < 1) : 0 < 1 - lam ^ 2 * Real.exp (2 + 2 * lam) := by
  have he : Real.exp (2 + 2 * lam) = Real.exp (1 + lam) * Real.exp (1 + lam) := by
    rw [← Real.exp_add]; ring_nf
  have hpos : 0 < Real.exp (1 + lam) := Real.exp_pos _
  have hsq : lam ^ 2 * Real.exp (2 + 2 * lam) = (lam * Real.exp (1 + lam)) ^ 2 := by
    rw [he]; ring
  rw [hsq]
  nlinarith [h12, mul_pos hlam hpos]

/-- The side condition also forces `λ < 1` (needed for a positive decay rate). -/
lemma lam_lt_one {lam : ℝ} (hlam : 0 < lam) (h12 : lam * Real.exp (1 + lam) < 1) :
    lam < 1 := by
  have h1 : (1 : ℝ) < Real.exp (1 + lam) := one_lt_exp_of_pos (by linarith)
  nlinarith [h12, hlam]

lemma flConst_pos {lam Lam : ℝ} (hlam : 0 < lam) (h12 : lam * Real.exp (1 + lam) < 1) :
    0 < flConst lam Lam := by
  have hden := one_sub_lam_sq_exp_pos hlam h12
  rw [flConst]
  positivity

/-- **P1(b) — THE `λ^{2b} → C·e^{−c·s}` CONVERSION.**  At the depth `b = flB s Λ`, H-R's
truncation defect is at most `flConst λ Λ · exp(−flRate λ · s)`.  This is the block-Brun
substitute for Iwaniec [10, Thm 4]'s `S₁′ − S₁ ≪ exp(−¼z₀)S₁`. -/
theorem fl_defect_le {lam Lam sRatio : ℝ} (hlam : 0 < lam)
    (h12 : lam * Real.exp (1 + lam) < 1) :
    2 * lam ^ (2 * flB sRatio Lam) * Real.exp (2 * lam)
        / (1 - lam ^ 2 * Real.exp (2 + 2 * lam))
      ≤ flConst lam Lam * Real.exp (-(flRate lam) * sRatio) := by
  have hden := one_sub_lam_sq_exp_pos hlam h12
  have hlam1 := lam_lt_one hlam h12
  have hrate := flRate_pos hlam hlam1
  set b := flB sRatio Lam with hbdef
  have hpow : lam ^ (2 * b) = Real.exp (-((2 * (b : ℝ)) * flRate lam)) := by
    have h1 : Real.exp (-((2 * (b : ℝ)) * flRate lam))
        = Real.exp (((2 * b : ℕ) : ℝ) * Real.log lam) := by
      congr 1
      push_cast
      rw [flRate]
      ring
    rw [h1, Real.exp_nat_mul, Real.exp_log hlam]
  have hlt := sub_levelE_lt_two_flB (sRatio := sRatio) (Lam := Lam)
  have hexp : Real.exp (-((2 * (b : ℝ)) * flRate lam))
      ≤ Real.exp (flRate lam * levelE Lam) * Real.exp (-(flRate lam) * sRatio) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hrate, hlt]
  have hfac : (0 : ℝ) < 2 * Real.exp (2 * lam) / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)) := by
    positivity
  have hrw : 2 * lam ^ (2 * b) * Real.exp (2 * lam)
        / (1 - lam ^ 2 * Real.exp (2 + 2 * lam))
      = (2 * Real.exp (2 * lam) / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
        * lam ^ (2 * b) := by
    field_simp
  rw [hrw, hpow, flConst]
  calc (2 * Real.exp (2 * lam) / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
        * Real.exp (-((2 * (b : ℝ)) * flRate lam))
      ≤ (2 * Real.exp (2 * lam) / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
        * (Real.exp (flRate lam * levelE Lam) * Real.exp (-(flRate lam) * sRatio)) :=
        mul_le_mul_of_nonneg_left hexp hfac.le
    _ = 2 * Real.exp (2 * lam) / (1 - lam ^ 2 * Real.exp (2 + 2 * lam))
          * Real.exp (flRate lam * levelE Lam) * Real.exp (-(flRate lam) * sRatio) := by ring

/-- The **upper** side carries one more power of `λ`. -/
theorem fl_defect_le_upper {lam Lam sRatio : ℝ} (hlam : 0 < lam)
    (h12 : lam * Real.exp (1 + lam) < 1) :
    2 * lam ^ (2 * flB sRatio Lam + 1) * Real.exp (2 * lam)
        / (1 - lam ^ 2 * Real.exp (2 + 2 * lam))
      ≤ lam * flConst lam Lam * Real.exp (-(flRate lam) * sRatio) := by
  have hden := one_sub_lam_sq_exp_pos hlam h12
  have h := fl_defect_le (lam := lam) (Lam := Lam) (sRatio := sRatio) hlam h12
  have hrw : 2 * lam ^ (2 * flB sRatio Lam + 1) * Real.exp (2 * lam)
        / (1 - lam ^ 2 * Real.exp (2 + 2 * lam))
      = lam * (2 * lam ^ (2 * flB sRatio Lam) * Real.exp (2 * lam)
        / (1 - lam ^ 2 * Real.exp (2 + 2 * lam))) := by
    rw [pow_succ]
    field_simp
  rw [hrw]
  calc lam * (2 * lam ^ (2 * flB sRatio Lam) * Real.exp (2 * lam)
        / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
      ≤ lam * (flConst lam Lam * Real.exp (-(flRate lam) * sRatio)) :=
        mul_le_mul_of_nonneg_left h hlam.le
    _ = lam * flConst lam Lam * Real.exp (-(flRate lam) * sRatio) := by ring

/-! ### The named numerics at `λ = 1/4` -/

/-- `E(Λ)` is antitone in `Λ` on `(0, ∞)` — a smaller ladder scale means a bigger level
exponent, hence a bigger fundamental-lemma constant. -/
lemma levelE_anti {Lam Lam' : ℝ} (h0 : 0 < Lam) (h : Lam ≤ Lam') :
    levelE Lam' ≤ levelE Lam := by
  have h1 : (1 : ℝ) < Real.exp Lam := one_lt_exp_of_pos h0
  have hle : Real.exp Lam ≤ Real.exp Lam' := Real.exp_le_exp.mpr h
  have h1' : (1 : ℝ) < Real.exp Lam' := lt_of_lt_of_le h1 hle
  rw [levelE, levelE, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hle, h1, h1']

/-- `flRate (1/4) = 2 log 2 = log 4 = 1.3862…` — the decay rate per unit of `s` at the
H-R parameter `λ = 1/4`. -/
lemma flRate_quarter : flRate (1 / 4 : ℝ) = 2 * Real.log 2 := by
  rw [flRate, show (1 / 4 : ℝ) = (2⁻¹) ^ 2 by norm_num, Real.log_pow, Real.log_inv]
  ring

/-- `E(1/10) ≤ 22.23`. -/
lemma levelE_tenth_le : levelE (1 / 10 : ℝ) ≤ 22.23 := by
  have hlow : (1.1 : ℝ) ≤ Real.exp (1 / 10 : ℝ) := by
    have := Real.add_one_le_exp (1 / 10 : ℝ)
    linarith
  rw [levelE, div_le_iff₀ (by linarith)]
  linarith

/-- **THE NAMED CONSTANT.**  At `λ = 1/4` and any ladder scale `Λ ≥ 1/10` — which at
`Λ = Lam4 (1/4) z = (1/8)(1 − 300/loglog z)` means `loglog z ≥ 1500` —

  `flConst (1/4) Λ ≤ 14·e^{31}`.

The two ingredients: the prefactor `2e^{1/2}/(1 − e^{5/2}/16) = 13.8203… ≤ 14`, and
`log 4 · E(Λ) ≤ log 4 · 22.23 = 30.82 ≤ 31`.  The *true* value at `Λ = 1/10` is
`13.8203·e^{29.135} = 6.22·10^{13}`; at the *nominal* scale `Λ = λ/2 = 1/8` it is
`13.8203·e^{23.599} = 2.44·10^{11}` (lower side), i.e. `6.11·10^{10}` on the upper side —
ROSSER-SCOPE's `6.1e10`, confirmed. -/
lemma flConst_quarter_le {Lam : ℝ} (hLam : (1 : ℝ) / 10 ≤ Lam) :
    flConst (1 / 4 : ℝ) Lam ≤ 14 * Real.exp 31 := by
  have hten : (0 : ℝ) < 1 / 10 := by norm_num
  -- (A) the prefactor
  have hy2 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hypos : (0 : ℝ) < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  have he1 : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
  have hy : Real.exp (1 / 2 : ℝ) ≤ 1.6489 := by nlinarith [hy2, hypos, he1]
  have h52 : Real.exp (5 / 2 : ℝ) = Real.exp (1 / 2 : ℝ) ^ 5 := by
    rw [show (5 / 2 : ℝ) = ((5 : ℕ) : ℝ) * (1 / 2) by norm_num, Real.exp_nat_mul]
  have h52le : Real.exp (5 / 2 : ℝ) ≤ 12.19 := by
    rw [h52]
    calc Real.exp (1 / 2 : ℝ) ^ 5 ≤ (1.6489 : ℝ) ^ 5 := pow_le_pow_left₀ hypos.le hy 5
      _ ≤ 12.19 := by norm_num
  have hA : 2 * Real.exp (2 * (1 / 4 : ℝ)) / (1 - (1 / 4 : ℝ) ^ 2 * Real.exp (2 + 2 * (1 / 4)))
      ≤ 14 := by
    have h2 : (2 : ℝ) + 2 * (1 / 4) = 5 / 2 := by norm_num
    have h1 : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
    rw [h2, h1, div_le_iff₀ (by nlinarith [h52le])]
    nlinarith [hy, h52le]
  -- (B) the exponent
  have hB : flRate (1 / 4 : ℝ) * levelE Lam ≤ 31 := by
    have hE : levelE Lam ≤ 22.23 :=
      le_trans (levelE_anti hten hLam) levelE_tenth_le
    have hEpos : 0 < levelE Lam := levelE_pos (lt_of_lt_of_le hten hLam)
    have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    rw [flRate_quarter]
    nlinarith [hE, hEpos, hl2, Real.log_two_gt_d9]
  rw [flConst]
  calc 2 * Real.exp (2 * (1 / 4 : ℝ)) / (1 - (1 / 4 : ℝ) ^ 2 * Real.exp (2 + 2 * (1 / 4)))
        * Real.exp (flRate (1 / 4 : ℝ) * levelE Lam)
      ≤ 14 * Real.exp (flRate (1 / 4 : ℝ) * levelE Lam) := by
        exact mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    _ ≤ 14 * Real.exp 31 := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hB) (by norm_num)

/-! ### The packaged fundamental-lemma endpoints -/

/-- **P1 — `fl_dim4_lower`: THE FUNDAMENTAL-LEMMA CONSEQUENCE AT DIMENSION 4 (lower side).**
At the depth `b = flB s Λ` — the depth for which every kept modulus lies under `D = z^s`
(`flB_level_bound`) — the H-R main sum obeys

  `mainSum λ⁻ ≥ W(z)·(1 − C·e^{−c·s})`,   `c = flRate λ = log(1/λ)`, `C = flConst λ Λ`.

This is the block-Brun substitute for Iwaniec [10, Thm 4] that HB's p.200 assembly quotes
as `S₁′ − S₁ ≪ exp(−¼z₀)S₁`.  Hypotheses beyond the level threshold `hs` are exactly
`Salt.BrunLower.mainSum_ge_of_lower'`'s: the `(2.16)` density inputs and the block
decomposition `hcorr`. -/
theorem fl_dim4_lower (s : BoundingSieve) {Lam z lam sRatio : ℝ} {r : ℕ}
    (hlam : 0 < lam) (h12 : lam * Real.exp (1 + lam) < 1) (hs : levelE Lam ≤ sRatio)
    (window : ℕ → Finset ℕ) (hwin : ∀ n, window n ⊆ s.prodPrimes.primeFactors)
    (Wr : ℕ → ℝ) (hWrnn : ∀ n ∈ Finset.Icc 1 r, 0 ≤ Wr n)
    (hWr : ∀ n ∈ Finset.Icc 1 r, Wr n ≤ Real.exp (2 * (n : ℝ) * lam))
    (hps : ∀ n ∈ Finset.Icc 1 r, (∑ p ∈ window n, s.nu p) ≤ 2 * (n : ℝ) * lam)
    (hcorr : W s * (1 - ∑ n ∈ Finset.Icc 1 r, Wr n *
            ∑ T ∈ (window n).powersetCard (2 * flB sRatio Lam - 2 + 2 * n), ∏ p ∈ T, s.nu p)
        ≤ s.mainSum (fun d => (μ d : ℝ) *
            (if chi Lam z 2 (flB sRatio Lam) d then (1 : ℝ) else 0))) :
    W s * (1 - flConst lam Lam * Real.exp (-(flRate lam) * sRatio))
      ≤ s.mainSum (fun d => (μ d : ℝ) *
          (if chi Lam z 2 (flB sRatio Lam) d then (1 : ℝ) else 0)) := by
  have hmain := mainSum_ge_of_lower' s (b := flB sRatio Lam) (one_le_flB hs) hlam h12
    window hwin Wr hWrnn hWr hps hcorr
  refine le_trans ?_ hmain
  have hWpos : (0 : ℝ) ≤ W s := (W_pos s).le
  have hdef := fl_defect_le (lam := lam) (Lam := Lam) (sRatio := sRatio) hlam h12
  exact mul_le_mul_of_nonneg_left (by linarith) hWpos

/-- **P1 — `fl_dim4_upper`: the mirror.**  `mainSum λ⁺ ≤ W(z)·(1 + λ·C·e^{−c·s})`.  The
upper side's defect carries one extra power of `λ` (H-R's `λ^{2b+1}` against `λ^{2b}`) —
at `λ = 1/4` that is the factor `4` between `C_upper = 6.11·10^{10}` and
`C_lower = 2.44·10^{11}`. -/
theorem fl_dim4_upper (s : BoundingSieve) {Lam z lam sRatio : ℝ} {r : ℕ}
    (hlam : 0 < lam) (h12 : lam * Real.exp (1 + lam) < 1) (hs : levelE Lam ≤ sRatio)
    (window : ℕ → Finset ℕ) (hwin : ∀ n, window n ⊆ s.prodPrimes.primeFactors)
    (Wr : ℕ → ℝ) (hWrnn : ∀ n ∈ Finset.Icc 1 r, 0 ≤ Wr n)
    (hWr : ∀ n ∈ Finset.Icc 1 r, Wr n ≤ Real.exp (2 * (n : ℝ) * lam))
    (hps : ∀ n ∈ Finset.Icc 1 r, (∑ p ∈ window n, s.nu p) ≤ 2 * (n : ℝ) * lam)
    (hcorr : s.mainSum (fun d => (μ d : ℝ) *
            (if chi Lam z 1 (flB sRatio Lam) d then (1 : ℝ) else 0))
        ≤ W s * (1 + ∑ n ∈ Finset.Icc 1 r, Wr n *
            ∑ T ∈ (window n).powersetCard (2 * flB sRatio Lam - 1 + 2 * n), ∏ p ∈ T, s.nu p)) :
    s.mainSum (fun d => (μ d : ℝ) *
        (if chi Lam z 1 (flB sRatio Lam) d then (1 : ℝ) else 0))
      ≤ W s * (1 + lam * flConst lam Lam * Real.exp (-(flRate lam) * sRatio)) := by
  have hmain := mainSum_le_of_upper' s (b := flB sRatio Lam) (one_le_flB hs) hlam h12
    window hwin Wr hWrnn hWr hps hcorr
  refine le_trans hmain ?_
  have hWpos : (0 : ℝ) ≤ W s := (W_pos s).le
  have hdef := fl_defect_le_upper (lam := lam) (Lam := Lam) (sRatio := sRatio) hlam h12
  exact mul_le_mul_of_nonneg_left (by linarith) hWpos

/-! ## P2 — the first-failure decomposition

### The two index sets -/

/-- `P(δ)`'s divisors, realised without naming `P(δ)`: the divisors of `P` all of whose
prime factors lie strictly below `δ`'s smallest prime factor.  For squarefree `P` this is
exactly the divisor set of `P(δ) = ∏_{p ∣ P, p < p(δ)} p` (HB p.199). -/
noncomputable def lowDiv (P δ : ℕ) : Finset ℕ :=
  P.divisors.filter (fun e => ∀ p ∈ e.primeFactors, p < δ.minFac)

/-- **THE FIRST-FAILURE SET `𝒮`.**  The divisors `δ` of `P` that the block predicate
discards but whose smallest prime is the *only* obstruction: `δ` fails `χ_ν` while
`δ/p(δ)` passes.  This is the block-Brun analogue of Iwaniec's `S`-set (HB p.199, with
characteristic function `σ_d` in [10, §3]). -/
noncomputable def failSet (Lam z : ℝ) (side b P : ℕ) : Finset ℕ :=
  P.divisors.filter (fun δ => ¬ chi Lam z side b δ ∧ chi Lam z side b (δ / δ.minFac))

lemma mem_lowDiv {P δ e : ℕ} :
    e ∈ lowDiv P δ ↔ (e ∣ P ∧ P ≠ 0) ∧ ∀ p ∈ e.primeFactors, p < δ.minFac := by
  simp [lowDiv, Nat.mem_divisors, and_assoc]

lemma mem_failSet {Lam z : ℝ} {side b P δ : ℕ} :
    δ ∈ failSet Lam z side b P ↔
      (δ ∣ P ∧ P ≠ 0) ∧ ¬ chi Lam z side b δ ∧ chi Lam z side b (δ / δ.minFac) := by
  simp [failSet, Nat.mem_divisors, and_assoc]

lemma failSet_ne_zero {Lam z : ℝ} {side b P δ : ℕ} (hδ : δ ∈ failSet Lam z side b P) :
    δ ≠ 0 := by
  rintro rfl
  obtain ⟨⟨hdvd, hP0⟩, _⟩ := mem_failSet.mp hδ
  exact hP0 (Nat.eq_zero_of_zero_dvd hdvd)

lemma failSet_ne_one {Lam z : ℝ} {side b P δ : ℕ} (hb : 1 ≤ b) (hside : side ≤ 2)
    (hδ : δ ∈ failSet Lam z side b P) : δ ≠ 1 := by
  rintro rfl
  exact (mem_failSet.mp hδ).2.1 (chi_one Lam z hb hside)

lemma failSet_squarefree {Lam z : ℝ} {side b P δ : ℕ} (hP : Squarefree P)
    (hδ : δ ∈ failSet Lam z side b P) : Squarefree δ :=
  Squarefree.squarefree_of_dvd (mem_failSet.mp hδ).1.1 hP

/-- The two halves of a first-failure factorisation are coprime: `δ`'s primes are all
`≥ p(δ)`, `e`'s are all `< p(δ)`. -/
lemma coprime_of_mem_lowDiv {δ e : ℕ} (hδ0 : δ ≠ 0) (he0 : e ≠ 0)
    (he : ∀ p ∈ e.primeFactors, p < δ.minFac) : Nat.Coprime δ e := by
  rw [← Nat.disjoint_primeFactors hδ0 he0, Finset.disjoint_left]
  intro q hq hq'
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have h1 : δ.minFac ≤ q :=
    Nat.minFac_le_of_dvd hqp.two_le (Nat.dvd_of_mem_primeFactors hq)
  have h2 := he q hq'
  omega

/-! ### The bijection: mapsTo, injectivity, surjectivity -/

/-- Maps-to: a first-failure pair multiplies to a discarded divisor. -/
lemma mul_mem_bad {Lam z : ℝ} {side b P δ e : ℕ}
    (hδ : δ ∈ failSet Lam z side b P) (he : e ∈ lowDiv P δ) :
    δ * e ∈ P.divisors.filter (fun d => ¬ chi Lam z side b d) := by
  obtain ⟨⟨hδP, hP0⟩, hnot, _⟩ := mem_failSet.mp hδ
  obtain ⟨⟨heP, _⟩, hlow⟩ := mem_lowDiv.mp he
  have hδ0 : δ ≠ 0 := failSet_ne_zero hδ
  have he0 : e ≠ 0 := by rintro rfl; exact hP0 (Nat.eq_zero_of_zero_dvd heP)
  have hcop := coprime_of_mem_lowDiv hδ0 he0 hlow
  refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hcop.mul_dvd_of_dvd_of_dvd hδP heP, hP0⟩, ?_⟩
  intro hchi
  exact hnot (chi_dvd_closed Lam z (Nat.mul_ne_zero hδ0 he0) ⟨e, rfl⟩ hchi)

/-- If every prime of `e` is below `δ'`'s smallest prime, then `δ' ∣ δ·e` forces
`δ' ∣ δ` — the primes of `δ'` cannot hide in `e`. -/
lemma dvd_of_primes_below {δ δ' e : ℕ} (hsq' : Squarefree δ') (he0 : e ≠ 0)
    (hdvd : δ' ∣ δ * e) (he : ∀ p ∈ e.primeFactors, p < δ'.minFac) : δ' ∣ δ := by
  have hall : ∀ q ∈ δ'.primeFactors, q ∣ δ := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqd : q ∣ δ * e := (Nat.dvd_of_mem_primeFactors hq).trans hdvd
    rcases (Nat.Prime.dvd_mul hqp).mp hqd with h | h
    · exact h
    · exfalso
      have hmem : q ∈ e.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, h, he0⟩
      have h1 := he q hmem
      have h2 : δ'.minFac ≤ q :=
        Nat.minFac_le_of_dvd hqp.two_le (Nat.dvd_of_mem_primeFactors hq)
      omega
  calc δ' = ∏ q ∈ δ'.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hsq').symm
    _ ∣ δ := Finset.prod_primes_dvd δ
        (fun q hq => (Nat.prime_of_mem_primeFactors hq).prime) hall

/-- **The key exclusion.**  Two first-failure elements cannot have strictly ordered
smallest primes over the same product: if `p(δ) < p(δ')` and `δ' ∣ δ·e` with `e`'s primes
below `p(δ)`, then `δ'` divides the *kept* part `δ/p(δ)`, so `χ_ν(δ')` holds — contradicting
`δ' ∈ 𝒮`. -/
lemma failSet_minFac_not_lt {Lam z : ℝ} {side b P δ δ' e : ℕ} (hb : 1 ≤ b) (hside : side ≤ 2)
    (hP : Squarefree P) (hδ : δ ∈ failSet Lam z side b P) (hδ' : δ' ∈ failSet Lam z side b P)
    (he : e ∈ lowDiv P δ) (hdvd : δ' ∣ δ * e) (hlt : δ.minFac < δ'.minFac) : False := by
  obtain ⟨⟨hδP, hP0⟩, _, hkept⟩ := mem_failSet.mp hδ
  obtain ⟨⟨heP, _⟩, hlow⟩ := mem_lowDiv.mp he
  have he0 : e ≠ 0 := by rintro rfl; exact hP0 (Nat.eq_zero_of_zero_dvd heP)
  have hδ0 : δ ≠ 0 := failSet_ne_zero hδ
  have hsq' : Squarefree δ' := failSet_squarefree hP hδ'
  have hlow' : ∀ p ∈ e.primeFactors, p < δ'.minFac := fun p hp => lt_trans (hlow p hp) hlt
  have hd : δ' ∣ δ := dvd_of_primes_below hsq' he0 hdvd hlow'
  have hp : (δ.minFac).Prime := Nat.minFac_prime (failSet_ne_one hb hside hδ)
  have hnd : ¬ (δ.minFac ∣ δ') := by
    intro h
    have : δ'.minFac ≤ δ.minFac := Nat.minFac_le_of_dvd hp.two_le h
    omega
  have hcop : Nat.Coprime δ.minFac δ' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
  have hmul : δ.minFac * δ' ∣ δ := hcop.mul_dvd_of_dvd_of_dvd (Nat.minFac_dvd δ) hd
  have hdd : δ' ∣ δ / δ.minFac := (Nat.dvd_div_iff_mul_dvd (Nat.minFac_dvd δ)).mpr hmul
  have hrw : δ.minFac * (δ / δ.minFac) = δ := Nat.mul_div_cancel' (Nat.minFac_dvd δ)
  have hne : δ / δ.minFac ≠ 0 := by
    intro h
    rw [h, Nat.mul_zero] at hrw
    exact hδ0 hrw.symm
  exact (mem_failSet.mp hδ').2.1 (chi_dvd_closed Lam z hne hdd hkept)

/-- **Injectivity of the first-failure factorisation.** -/
lemma failSet_unique {Lam z : ℝ} {side b P δ δ' e e' : ℕ} (hb : 1 ≤ b) (hside : side ≤ 2)
    (hP : Squarefree P) (hδ : δ ∈ failSet Lam z side b P) (he : e ∈ lowDiv P δ)
    (hδ' : δ' ∈ failSet Lam z side b P) (he' : e' ∈ lowDiv P δ')
    (heq : δ * e = δ' * e') : δ = δ' ∧ e = e' := by
  obtain ⟨⟨hδP, hP0⟩, _, _⟩ := mem_failSet.mp hδ
  obtain ⟨⟨heP, _⟩, hlow⟩ := mem_lowDiv.mp he
  obtain ⟨⟨heP', _⟩, hlow'⟩ := mem_lowDiv.mp he'
  have he0 : e ≠ 0 := by rintro rfl; exact hP0 (Nat.eq_zero_of_zero_dvd heP)
  have he0' : e' ≠ 0 := by rintro rfl; exact hP0 (Nat.eq_zero_of_zero_dvd heP')
  have hδ0 : δ ≠ 0 := failSet_ne_zero hδ
  have hd1 : δ' ∣ δ * e := ⟨e', heq⟩
  have hd2 : δ ∣ δ' * e' := ⟨e, heq.symm⟩
  have hmf : δ.minFac = δ'.minFac := by
    rcases lt_trichotomy δ.minFac δ'.minFac with h | h | h
    · exact absurd (failSet_minFac_not_lt hb hside hP hδ hδ' he hd1 h) (by simp)
    · exact h
    · exact absurd (failSet_minFac_not_lt hb hside hP hδ' hδ he' hd2 h) (by simp)
  have hsq : Squarefree δ := failSet_squarefree hP hδ
  have hsq' : Squarefree δ' := failSet_squarefree hP hδ'
  have hA : δ' ∣ δ :=
    dvd_of_primes_below hsq' he0 hd1 (fun p hp => hmf ▸ hlow p hp)
  have hB : δ ∣ δ' :=
    dvd_of_primes_below hsq he0' hd2 (fun p hp => hmf ▸ hlow' p hp)
  have hδeq : δ = δ' := Nat.dvd_antisymm hB hA
  subst hδeq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hδ0) heq⟩

/-- **Surjectivity: THE FIRST-FAILURE EXISTENCE.**  Every discarded divisor `d ∣ P` factors
as `δ·e` with `δ` a first-failure element and `e`'s primes all below `p(δ)`.  The proof
strips the smallest prime: either `d/p(d)` is already discarded (recurse) or `d` itself is
the first failure. -/
lemma exists_firstFailure {Lam z : ℝ} {side b : ℕ} (hb : 1 ≤ b) (hside : side ≤ 2)
    {P : ℕ} (hP : Squarefree P) :
    ∀ d : ℕ, d ∣ P → ¬ chi Lam z side b d →
      ∃ δ ∈ failSet Lam z side b P, ∃ e ∈ lowDiv P δ, δ * e = d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hdP hnot
    have hP0 : P ≠ 0 := hP.ne_zero
    have hd0 : d ≠ 0 := by rintro rfl; exact hP0 (Nat.eq_zero_of_zero_dvd hdP)
    have hd1 : d ≠ 1 := by rintro rfl; exact hnot (chi_one Lam z hb hside)
    have hp : (d.minFac).Prime := Nat.minFac_prime hd1
    have hpd : d.minFac ∣ d := Nat.minFac_dvd d
    have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hdP hP
    have hd'd : d / d.minFac ∣ d := Nat.div_dvd_of_dvd hpd
    have hd'P : d / d.minFac ∣ P := hd'd.trans hdP
    have hlt : d / d.minFac < d := Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hp.one_lt
    have hrwd : d.minFac * (d / d.minFac) = d := Nat.mul_div_cancel' hpd
    have hnpd : ¬ (d.minFac ∣ d / d.minFac) := by
      intro h
      obtain ⟨k, hk⟩ := h
      have hd_eq : d = d.minFac * d.minFac * k := by
        calc d = d.minFac * (d / d.minFac) := hrwd.symm
          _ = d.minFac * (d.minFac * k) := by rw [hk]
          _ = d.minFac * d.minFac * k := by ring
      exact hp.not_isUnit (hdsq _ ⟨k, hd_eq⟩)
    by_cases hchi' : chi Lam z side b (d / d.minFac)
    · refine ⟨d, mem_failSet.mpr ⟨⟨hdP, hP0⟩, hnot, hchi'⟩, 1, ?_, by ring⟩
      exact mem_lowDiv.mpr ⟨⟨one_dvd P, hP0⟩, by simp⟩
    · obtain ⟨δ, hδ, e, he, heq⟩ := ih (d / d.minFac) hlt hd'P hchi'
      obtain ⟨⟨heP, _⟩, hlow⟩ := mem_lowDiv.mp he
      have he0 : e ≠ 0 := by rintro rfl; exact hP0 (Nat.eq_zero_of_zero_dvd heP)
      have hδd' : δ ∣ d / d.minFac := ⟨e, heq.symm⟩
      have hδ1 : δ ≠ 1 := failSet_ne_one hb hside hδ
      have hδ0 : δ ≠ 0 := failSet_ne_zero hδ
      have hδmf : (δ.minFac).Prime := Nat.minFac_prime hδ1
      have hmfδd : δ.minFac ∣ d / d.minFac := (Nat.minFac_dvd δ).trans hδd'
      -- `p(d) < p(δ)`
      have hple : d.minFac ≤ δ.minFac :=
        Nat.minFac_le_of_dvd hδmf.two_le (hmfδd.trans hd'd)
      have hpne : d.minFac ≠ δ.minFac := by
        intro h
        exact hnpd (h ▸ hmfδd)
      have hplt : d.minFac < δ.minFac := lt_of_le_of_ne hple hpne
      -- `p(d)·e` is coprime to `δ` and divides `P`
      have hedvd : e ∣ d / d.minFac := ⟨δ, by rw [← heq]; ring⟩
      have hcop : Nat.Coprime d.minFac e := by
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro h
        exact hnpd (h.trans hedvd)
      refine ⟨δ, hδ, d.minFac * e, ?_, ?_⟩
      · refine mem_lowDiv.mpr ⟨⟨hcop.mul_dvd_of_dvd_of_dvd (hpd.trans hdP) heP, hP0⟩, ?_⟩
        intro q hq
        rw [Nat.primeFactors_mul hp.ne_zero he0, hp.primeFactors] at hq
        rcases Finset.mem_union.mp hq with h | h
        · rw [Finset.mem_singleton] at h; omega
        · exact hlow q h
      · calc δ * (d.minFac * e) = d.minFac * (δ * e) := by ring
          _ = d.minFac * (d / d.minFac) := by rw [heq]
          _ = d := hrwd

/-! ### The identity -/

/-- **P2 — THE FIRST-FAILURE DECOMPOSITION.**  For *any* `ρ : ℕ → ℝ` and squarefree `P`,
the block-Brun truncated Möbius sum differs from the untruncated one by a sum over the
first-failure set:

  `Σ_{d∣P} μ(d)χ_ν(d)ρ(d) = Σ_{d∣P} μ(d)ρ(d) − Σ_{δ∈𝒮} Σ_{e∣P(δ)} μ(δe)ρ(δe)`.

This is the block-Brun analogue of the Iwaniec `S`-set identity quoted at HB p.199 — proved
here from the kept set's own definition, with no hypothesis on `ρ` whatsoever. -/
theorem firstFailure_decomposition {Lam z : ℝ} {side b : ℕ} (hb : 1 ≤ b) (hside : side ≤ 2)
    {P : ℕ} (hP : Squarefree P) (ρ : ℕ → ℝ) :
    ∑ d ∈ P.divisors, (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0) * ρ d
      = ∑ d ∈ P.divisors, (μ d : ℝ) * ρ d
        - ∑ δ ∈ failSet Lam z side b P, ∑ e ∈ lowDiv P δ, (μ (δ * e) : ℝ) * ρ (δ * e) := by
  set F : ℕ → ℝ := fun d => (μ d : ℝ) * ρ d with hF
  have hkept : ∑ d ∈ P.divisors, (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0) * ρ d
      = ∑ d ∈ P.divisors.filter (fun d => chi Lam z side b d), F d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : chi Lam z side b d <;> simp [hF, h]
  have hsplit := Finset.sum_filter_add_sum_filter_not P.divisors
    (fun d => chi Lam z side b d) F
  have hbij : ∑ δ ∈ failSet Lam z side b P, ∑ e ∈ lowDiv P δ, F (δ * e)
      = ∑ d ∈ P.divisors.filter (fun d => ¬ chi Lam z side b d), F d := by
    rw [Finset.sum_sigma']
    refine Finset.sum_nbij (i := fun x : (_ : ℕ) × ℕ => x.1 * x.2) ?_ ?_ ?_ ?_
    · rintro ⟨δ, e⟩ hx
      rw [Finset.mem_sigma] at hx
      exact mul_mem_bad hx.1 hx.2
    · rintro ⟨δ, e⟩ hx ⟨δ', e'⟩ hx' hEq
      rw [Finset.coe_sigma, Set.mem_sigma_iff] at hx hx'
      obtain ⟨h1, h2⟩ := failSet_unique hb hside hP hx.1 hx.2 hx'.1 hx'.2 hEq
      simp only [Sigma.mk.injEq]
      exact ⟨h1, by subst h1; exact heq_of_eq h2⟩
    · rintro d hd
      rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨δ, hδ, e, he, hde⟩ := exists_firstFailure hb hside hP d hd.1.1 hd.2
      refine ⟨⟨δ, e⟩, ?_, hde⟩
      rw [Finset.mem_coe, Finset.mem_sigma]
      exact ⟨hδ, he⟩
    · intro x _
      rfl
  rw [hkept, hbij]
  linarith [hsplit]

/-! ### The support fact and the sign -/

/-- **THE SUPPORT FACT.**  Every first-failure element lies below `z^{levelExp + 1}`: the
kept part `δ/p(δ)` obeys wave 1's level bound, and the one stripped prime costs a single
factor `z`.  This is the block-Brun form of Iwaniec's `δ ≤ Max(D, z²)` (HB p.199) — one
extra rung, not two. -/
theorem failSet_le_rpow {Lam z : ℝ} {side b P δ : ℕ} (hb : 1 ≤ b) (hside : side ≤ 2)
    (hLam : 0 < Lam) (hz : 1 < z) (hP : Squarefree P)
    (hPz : ∀ p ∈ P.primeFactors, (p : ℝ) < z)
    (hδ : δ ∈ failSet Lam z side b P) :
    (δ : ℝ) ≤ z ^ (levelExp Lam side b + 1) := by
  obtain ⟨⟨hδP, hP0⟩, _, hkept⟩ := mem_failSet.mp hδ
  have hδ0 : δ ≠ 0 := failSet_ne_zero hδ
  have hδ1 : δ ≠ 1 := failSet_ne_one hb hside hδ
  have hp : (δ.minFac).Prime := Nat.minFac_prime hδ1
  have hpd : δ.minFac ∣ δ := Nat.minFac_dvd δ
  have hsq : Squarefree δ := failSet_squarefree hP hδ
  have hd'sq : Squarefree (δ / δ.minFac) :=
    Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd) hsq
  have hd'0 : δ / δ.minFac ≠ 0 := by
    intro h
    have hrw : δ.minFac * (δ / δ.minFac) = δ := Nat.mul_div_cancel' hpd
    rw [h, Nat.mul_zero] at hrw
    exact hδ0 hrw.symm
  have hd'z : ∀ p ∈ (δ / δ.minFac).primeFactors, (p : ℝ) < z := by
    intro p hp'
    exact hPz p (Nat.primeFactors_mono (((Nat.div_dvd_of_dvd hpd).trans hδP)) hP0 hp')
  have hlev := chi_le_rpow_level hLam hz hd'0 hd'sq hd'z hkept
  have hpz : ((δ.minFac : ℕ) : ℝ) < z :=
    hPz _ (Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hδP, hP0⟩)
  have hzpos : (0 : ℝ) < z := by linarith
  have hrw : δ.minFac * (δ / δ.minFac) = δ := Nat.mul_div_cancel' hpd
  have hcast : (δ : ℝ) = ((δ.minFac : ℕ) : ℝ) * ((δ / δ.minFac : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, hrw]
  rw [hcast, Real.rpow_add hzpos, Real.rpow_one]
  have hd'nn : (0 : ℝ) ≤ ((δ / δ.minFac : ℕ) : ℝ) := Nat.cast_nonneg _
  have hzlev : (0 : ℝ) ≤ z ^ levelExp Lam side b := (Real.rpow_pos_of_pos hzpos _).le
  calc ((δ.minFac : ℕ) : ℝ) * ((δ / δ.minFac : ℕ) : ℝ)
      ≤ ((δ.minFac : ℕ) : ℝ) * z ^ levelExp Lam side b :=
        mul_le_mul_of_nonneg_left hlev (Nat.cast_nonneg _)
    _ ≤ z ^ levelExp Lam side b * z := by nlinarith [hpz, hzlev]

/-- **THE FORCED COUNT.**  At a level `n` where `χ_ν` fails for `δ` but holds for
`δ/p(δ)`, the restricted count is forced to `2b − ν + 2n` *and* every prime of `δ` is
counted — so `Ω(δ) = 2b − ν + 2n` exactly.  This is H-R's (2.3) parity mechanism read
backwards (compare `Salt/BrunLower/BlockDecomp.lean`'s p.104 reading). -/
theorem failSet_forced_count {Lam z : ℝ} {side b δ : ℕ} (hb : 1 ≤ b) (hside : side ≤ 2)
    (hδ0 : δ ≠ 0) (hsq : Squarefree δ)
    (hnot : ¬ chi Lam z side b δ) (hkept : chi Lam z side b (δ / δ.minFac)) :
    ∃ n : ℕ, 1 ≤ n ∧ (δ.primeFactors.card : ℤ) = blockBound side b n + 1 := by
  have hδ1 : δ ≠ 1 := by rintro rfl; exact hnot (chi_one Lam z hb hside)
  have hp : (δ.minFac).Prime := Nat.minFac_prime hδ1
  have hpd : δ.minFac ∣ δ := Nat.minFac_dvd δ
  have hrw : δ.minFac * (δ / δ.minFac) = δ := Nat.mul_div_cancel' hpd
  have hd'0 : δ / δ.minFac ≠ 0 := by
    intro h; rw [h, Nat.mul_zero] at hrw; exact hδ0 hrw.symm
  have hnpd : ¬ (δ.minFac ∣ δ / δ.minFac) := by
    intro h
    obtain ⟨k, hk⟩ := h
    have hd_eq : δ = δ.minFac * δ.minFac * k := by
      calc δ = δ.minFac * (δ / δ.minFac) := hrw.symm
        _ = δ.minFac * (δ.minFac * k) := by rw [hk]
        _ = δ.minFac * δ.minFac * k := by ring
    exact hp.not_isUnit (hsq _ ⟨k, hd_eq⟩)
  have hpf : δ.primeFactors = insert δ.minFac (δ / δ.minFac).primeFactors := by
    conv_lhs => rw [← hrw]
    rw [Nat.primeFactors_mul hp.ne_zero hd'0, hp.primeFactors, Finset.insert_eq]
  have hpnot : δ.minFac ∉ (δ / δ.minFac).primeFactors := by
    intro h
    exact hnpd (Nat.dvd_of_mem_primeFactors h)
  rw [chi] at hnot
  push Not at hnot
  obtain ⟨n, hn1, hn⟩ := hnot
  refine ⟨n, hn1, ?_⟩
  have hkeptn := hkept n hn1
  -- `p(δ)` must be counted at level `n`
  have hcount : zLev Lam z n ≤ ((δ.minFac : ℕ) : ℝ) := by
    by_contra hcon
    apply absurd hkeptn
    push Not
    have heq : bigOmegaGe Lam z n δ = bigOmegaGe Lam z n (δ / δ.minFac) := by
      unfold bigOmegaGe
      rw [hpf, Finset.filter_insert, if_neg hcon]
    rw [heq] at hn
    exact hn
  -- hence every prime of `δ` is counted
  have hall : ∀ q ∈ δ.primeFactors, zLev Lam z n ≤ (q : ℝ) := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have : δ.minFac ≤ q := Nat.minFac_le_of_dvd hqp.two_le (Nat.dvd_of_mem_primeFactors hq)
    have hR : ((δ.minFac : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast this
    linarith
  have hfull : bigOmegaGe Lam z n δ = δ.primeFactors.card := by
    unfold bigOmegaGe
    rw [Finset.filter_true_of_mem hall]
  -- and the count is at most one more than the kept part's
  have hstep : bigOmegaGe Lam z n δ = bigOmegaGe Lam z n (δ / δ.minFac) + 1 := by
    unfold bigOmegaGe
    rw [hpf, Finset.filter_insert, if_pos hcount,
      Finset.card_insert_of_notMem (fun hmem => hpnot (Finset.filter_subset _ _ hmem))]
  rw [← hfull]
  rw [hstep] at hn ⊢
  push_cast at hn ⊢
  omega

/-- **THE SIGN IS CONSTANT ON `𝒮`.**  Every first-failure element has `Ω(δ) ≡ ν (mod 2)`,
hence `μ(δ) = (−1)^ν`.  This one-signedness is exactly what H-R's parity twist buys, and it
is what makes the P3 transfer available: for `ν = 1` the correction is `+`, for `ν = 2`
it is `−`. -/
theorem failSet_moebius {Lam z : ℝ} {side b P δ : ℕ} (hb : 1 ≤ b) (hside : side ≤ 2)
    (hP : Squarefree P) (hδ : δ ∈ failSet Lam z side b P) :
    (μ δ : ℝ) = (-1 : ℝ) ^ side := by
  obtain ⟨⟨hδP, hP0⟩, hnot, hkept⟩ := mem_failSet.mp hδ
  have hδ0 : δ ≠ 0 := failSet_ne_zero hδ
  have hsq : Squarefree δ := failSet_squarefree hP hδ
  obtain ⟨n, hn1, hn⟩ := failSet_forced_count hb hside hδ0 hsq hnot hkept
  -- `Ω(δ) = card δ.primeFactors` for squarefree `δ`
  have hcard : ArithmeticFunction.cardFactors δ = δ.primeFactors.card := by
    have h := (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hδ0).mpr hsq
    rw [← h, ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors,
      List.card_toFinset]
  rw [blockBound] at hn
  have hpar : δ.primeFactors.card % 2 = side % 2 := by omega
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, hcard]
  push_cast
  rcases Nat.even_or_odd side with hs | hs
  · have hc : Even (δ.primeFactors.card) :=
      Nat.even_iff.mpr (by rw [hpar]; exact Nat.even_iff.mp hs)
    rw [hc.neg_one_pow, hs.neg_one_pow]
  · have hc : Odd (δ.primeFactors.card) :=
      Nat.odd_iff.mpr (by rw [hpar]; exact Nat.odd_iff.mp hs)
    rw [hc.neg_one_pow, hs.neg_one_pow]

/-! ### The signed form, and the per-δ pieces `S^{(i)}(δ)` -/

/-- HB's `S^{(i)}(δ) = Σ_{d ∣ P(δ)} ρ_i(dδ)μ(d)` (Lemma 6). -/
noncomputable def deltaSum (P δ : ℕ) (ρ : ℕ → ℝ) : ℝ :=
  ∑ e ∈ lowDiv P δ, (μ e : ℝ) * ρ (δ * e)

/-- **P2 — THE SIGNED FIRST-FAILURE DECOMPOSITION.**  Combining
`firstFailure_decomposition` with `failSet_moebius`:

  `Σ_{d∣P} μ(d)χ_ν(d)ρ(d) − Σ_{d∣P} μ(d)ρ(d) = −(−1)^ν · Σ_{δ∈𝒮} S(δ)`,

with `S(δ) = deltaSum P δ ρ` — the correction is one-signed, uniformly in `ρ`.  This is the
shape HB's p.200 assembly consumes (his `S′ − S`). -/
theorem firstFailure_decomposition_signed {Lam z : ℝ} {side b : ℕ} (hb : 1 ≤ b)
    (hside : side ≤ 2) {P : ℕ} (hP : Squarefree P) (ρ : ℕ → ℝ) :
    (∑ d ∈ P.divisors, (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0) * ρ d)
        - ∑ d ∈ P.divisors, (μ d : ℝ) * ρ d
      = -((-1 : ℝ) ^ side) * ∑ δ ∈ failSet Lam z side b P, deltaSum P δ ρ := by
  have hdec := firstFailure_decomposition (Lam := Lam) (z := z) hb hside hP ρ
  have hinner : ∀ δ ∈ failSet Lam z side b P,
      ∑ e ∈ lowDiv P δ, (μ (δ * e) : ℝ) * ρ (δ * e)
        = ((-1 : ℝ) ^ side) * deltaSum P δ ρ := by
    intro δ hδ
    have hδ0 : δ ≠ 0 := failSet_ne_zero hδ
    have hmu := failSet_moebius hb hside hP hδ
    rw [deltaSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨⟨heP, hP0⟩, hlow⟩ := mem_lowDiv.mp he
    have he0 : e ≠ 0 := by rintro rfl; exact hP0 (Nat.eq_zero_of_zero_dvd heP)
    have hcop := coprime_of_mem_lowDiv hδ0 he0 hlow
    have hsplit : (μ (δ * e) : ℝ) = (μ δ : ℝ) * (μ e : ℝ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
      push_cast
      ring
    rw [hsplit, hmu]
    ring
  rw [hdec, Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  ring

/-! ## P3 — the per-δ transfer skeleton -/

/-- **P3(a) — THE ABSTRACT PER-δ TRANSFER.**  If every fibre of a decomposition satisfies
`|S^{(i)}(δ)| ≤ B·S^{(1)}(δ)` with `S^{(1)}(δ) ≥ 0`, the aggregate inherits the domination:
`|Σ S^{(i)}| ≤ B·|Σ S^{(1)}|`.  This is the whole content of HB's p.200 line
`|S_i′ − S_i| ≪ BL|S₁′ − S₁|` once the decomposition is in hand — and it is exactly where
the one-signedness of the correction is spent (`|Σ S^{(1)}| = Σ S^{(1)}`). -/
theorem perDelta_transfer {ι : Type*} (T : Finset ι) (S1 Si : ι → ℝ) (B : ℝ)
    (hnn : ∀ δ ∈ T, 0 ≤ S1 δ) (hdom : ∀ δ ∈ T, |Si δ| ≤ B * S1 δ) :
    |∑ δ ∈ T, Si δ| ≤ B * |∑ δ ∈ T, S1 δ| := by
  have h1 : |∑ δ ∈ T, Si δ| ≤ ∑ δ ∈ T, |Si δ| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ δ ∈ T, |Si δ| ≤ ∑ δ ∈ T, B * S1 δ := Finset.sum_le_sum hdom
  have h3 : ∑ δ ∈ T, B * S1 δ = B * ∑ δ ∈ T, S1 δ := (Finset.mul_sum _ _ _).symm
  have h4 : (0 : ℝ) ≤ ∑ δ ∈ T, S1 δ := Finset.sum_nonneg hnn
  rw [abs_of_nonneg h4]
  linarith

/-- **P3(b) — THE TRANSFER OVER A ONE-SIGNED DECOMPOSITION.**  Abstract over the shape the
first-failure identity produces: `S′ − S = ε·Σ_δ S(δ)` with a *fixed* sign `ε = ±1` shared
by both densities.  Then per-δ domination transfers to the aggregate defects. -/
theorem transfer_of_decomposition {ι : Type*} (T : Finset ι) (s1 si : ι → ℝ)
    (S1 S1' Si Si' eps B : ℝ) (heps : eps = 1 ∨ eps = -1)
    (hnn : ∀ δ ∈ T, 0 ≤ s1 δ) (hdom : ∀ δ ∈ T, |si δ| ≤ B * s1 δ)
    (hd1 : S1' - S1 = eps * ∑ δ ∈ T, s1 δ) (hdi : Si' - Si = eps * ∑ δ ∈ T, si δ) :
    |Si' - Si| ≤ B * |S1' - S1| := by
  have habs : |eps| = 1 := by rcases heps with h | h <;> rw [h] <;> norm_num
  rw [hd1, hdi, abs_mul, abs_mul, habs, one_mul, one_mul]
  exact perDelta_transfer T s1 si B hnn hdom

/-- **P3(c) — THE WIRED TRANSFER AT THE BLOCK-BRUN WEIGHTS.**  HB's p.200 display, with
Lemma 6's per-δ hypotheses as the only inputs: given
`S^{(1)}(δ) ≥ 0` and `|S^{(i)}(δ)| ≤ B·S^{(1)}(δ)` for every first-failure `δ`,

  `|S_i′ − S_i| ≤ B·|S₁′ − S₁|`,

where `S′` is the truncated (block-Brun λ-weighted) sum and `S` the plain Möbius sum.  The
fundamental-lemma saving proved for `ρ₁` (P1) therefore transfers to `ρ₂`, `ρ₃` at the
cost of the single factor `B` — HB's `BL`. -/
theorem hb_perDelta_transfer {Lam z : ℝ} {side b : ℕ} (hb : 1 ≤ b) (hside : side ≤ 2)
    {P : ℕ} (hP : Squarefree P) (rho1 rhoi : ℕ → ℝ) (B : ℝ)
    (hnn : ∀ δ ∈ failSet Lam z side b P, 0 ≤ deltaSum P δ rho1)
    (hdom : ∀ δ ∈ failSet Lam z side b P,
      |deltaSum P δ rhoi| ≤ B * deltaSum P δ rho1) :
    |(∑ d ∈ P.divisors, (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0) * rhoi d)
        - ∑ d ∈ P.divisors, (μ d : ℝ) * rhoi d|
      ≤ B * |(∑ d ∈ P.divisors, (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0) * rho1 d)
        - ∑ d ∈ P.divisors, (μ d : ℝ) * rho1 d| := by
  refine transfer_of_decomposition (failSet Lam z side b P)
    (fun δ => deltaSum P δ rho1) (fun δ => deltaSum P δ rhoi) _ _ _ _
    (-((-1 : ℝ) ^ side)) B ?_ hnn hdom
    (firstFailure_decomposition_signed hb hside hP rho1)
    (firstFailure_decomposition_signed hb hside hP rhoi)
  rcases Nat.even_or_odd side with h | h
  · right; simp [h.neg_one_pow]
  · left; simp [h.neg_one_pow]

end Salt.HB
