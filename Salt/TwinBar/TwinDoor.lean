/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Basic
import Salt.Chen.TwinDeficit
import Salt.TwinBar.Wall

/-!
# Q6b — the door: the minimal parity-breaking input for twins

Design: `docs/exploration/q6b-design.md` (post-gate, corrections C1–C4 applied).

**This is EXPLORATION, not a frozen blueprint node.**  The file adds NEW work only; it
imports two landed spines (`Salt.Chen.TwinDeficit` for the Λ-weighted twin carrier
`p1PrimeSum`, and `Salt.TwinBar.Wall` for the parity wall) plus `Salt.Basic` for the
target `TwinPrimeConjecture`.  It edits no landed file, is wired into no `All`, and is
sorry-free / axiom-clean.  Every OPEN mathematical gap is recorded as prose or as a
named `Prop`, never as a `sorry`'d theorem.

## The wall and the door (the dichotomy)

The landed parity wall (`no_parity_beating_certificate`, `Wall.lean`) is a strong
negative: on the witness pair `sPlus`/`sMinus` (`ParityWall.lean`), any lower-bound
certificate `Φ` that is *`SieveAgree`-tolerant* at a fixed level `D` — i.e. whose value
is controlled to within `2·B` whenever two sieves agree on `prodPrimes`, `nu`,
`totalMass` and share a Rosser-remainder budget `B` — captures only a vanishing
proportion of the prime mass `siftedSum (sMinus x) = 2(π(x) − π(√x))`.  The mechanism
is the **`λ ↦ −λ` involution**: flipping the sign of the lower-Möbius weights carries
`sPlus x` to `sMinus x` while preserving every field the tolerance hypothesis reads —
the `|rem d|` bounds are *literally identical* on the two witnesses (`sPlus_rem_bound`,
`sMinus_rem_bound`, `sieveAgree_pair` in `ParityWall.lean`), so a parity-blind
certificate cannot tell the prime-detecting witness from the sign-flipped decoy.

Every candidate lower-bound certificate `Φ` therefore lands on exactly one side of a
partition: **either** it is `SieveAgree`-tolerant (and the wall kills it), **or** it is
NOT tolerant — it reads the *sign* of the weights inside `multSum`, at the bilinear
`α ⊗ β` resolution.  `wall_or_door` is the door: any `Φ` that does capture a positive
proportion of `siftedSum (sMinus x)` provably falls in the second class.  Chen's switch
(`switchSieve_multSum_eq_apCount`, landed in the Goldbach spine) is the kernel-checked
proof-of-life that a certificate CAN read at signed resolution — the escape is
inhabited, not hypothetical.

## The door proper: `TwinB_min` (`TwinTypeII`)

The minimal *distributional* input that walks through the door is a level-θ twin
type-II asymptotic for the Λ-weighted carrier `p1PrimeSum x 1` — the sifted prime mass
`Σ_{n ∈ [x/2, x−2]} Λ(n)·1_{n prime}·1_{n+2 prime}` (`TwinDeficit.p1PrimeSum`).

GATE CORRECTION C1 (the main term is the Λ-weighted one).  Because the carrier carries
the von Mangoldt weight, its main term is one logarithm UP from the naive twin count:
`twinMainTerm x = twinC2 · x / log x`, NOT `𝔖 · x/(log x)²`.  The gate verified this
against the landed witness `p1_carrier_inhabited` (the `n = 17` term is `log 17`, not
`1`).  The classical Hardy–Littlewood constant `𝔖 = 2·twinC2` is the *unweighted*-count
constant; the window `[x/2, x−2]` halves it to `twinC2`.  `TwinTypeII` demands the
two-sided asymptotic `|p1PrimeSum x 1 − twinMainTerm x| ≤ C·x/(log x)^A` for every
saving `A > 0` — an honest error term, matching the shape of the landed distributional
conventions (`LambdaSummatory`, `HasLevel`).

GATE CORRECTION C2 (the constant must be genuine).  `twinC2` is the honest Euler
product `∏_{p>2} (1 − (p−1)⁻²)`, backed by a `Multipliable` witness
(`twinC2_multipliable`).  mathlib's `tprod` junk-defaults to `1` on a non-multipliable
family, so positivity `0 < twinC2` would otherwise pass ON A LIE (`0 < 1`); here it is
earned from `twinC2 = exp(∑' log factor) > 0` via the genuine convergence chain
(summability of `(p−1)⁻²` on the prime subtype → log-summability → `Real.exp_pos`).

GATE CORRECTION C4 (θ is not a binder).  `TwinB_min := TwinTypeII` directly; the
level-θ discussion — that consuming the twin bilinear form would require a distribution
level `θ > 1/2`, strictly past the large-sieve barrier — is commentary, not a phantom
binder.  The `apDiscBilinCutoff` reading (that the twin type-II sum decomposes as an
`α ⊗ β` bilinear form cut off at the sieve level, exactly the object Chen's switch reads
at signed resolution) likewise lives here in prose, not as a second `Prop`.

## What lands, and what does NOT (D5)

`twinB_min_implies_twins : TwinB_min → TwinPrimeConjecture` is the stretch and it LANDS
(class B): the main term `twinC2·x/log x` eventually dominates the error `C·x/(log x)²`
(at `A = 2`), forcing `p1PrimeSum x 1 > 0` for large `x`; a positive Λ-weighted twin
sum contains a genuine twin survivor `≥ x/2` (`twin_survivor_of_pos` — EASIER than the
P₂ survivor endgame, since `keepR 1` already filters to primes with no prime-power
crumb), and the threshold plumbing mirrors `Chen/Assembly.chen_of_hypotheses`.

Proving `TwinB_min` itself is the class-D content: the upper→asymptotic-lower upgrade is
the P₁ lower sieve, blocked at the large-sieve level-1/2 wall.  STATED-NOT-ATTEMPTED —
this is the flagship's **Challenge 2** and the open-problems board's entry #2.  Board
siblings, named here but NOT formalized: **TwinLambda** — fixed-shift Chowla
`Σ_{n≤x} λ(n)λ(n+2) = o(x)` over the landed Liouville carriers (`Mlambda`,
`LambdaRate.lean`) — is open on BOTH the premise (fixed-shift Chowla) and the
implication (the λ→Λ transfer); and the **Heath-Brown/Siegel** dichotomy, which needs
the same `N(T)` zero-density stack and does not route through the sieve interface.

## Anti-vacuity (Part III discipline)

`twinC2_pos` closes the zero-main-term alarm AND the C2 junk-default trap.  The error
half of `TwinTypeII` is not vacuously false: the landed upper bound
`windowed_bilinear_BV_sqrtD` (`Chen/WindowedBVStatement.lean`) already controls the
`‖·‖` side, so the NEW content is strictly the asymptotic-lower main term.  R4 (the
too-good-to-be-true tripwire): `TwinB_min` is a DISTRIBUTIONAL premise (a level-θ
asymptotic with an explicit `(log x)^A` saving), never a raw "`p1PrimeSum` is large";
nothing here proves it, and the landed carrier is inhabited only at a toy point
(`p1_carrier_inhabited`, the twin pair `(17,19)`), carrying no twin-prime content.
-/

open ArithmeticFunction Finset Filter
open Salt.Chen

namespace Salt.TwinBar

/-! ## D1a — the genuine twin constant `twinC2` (GATE CORRECTION C2)

The Euler product `∏_{p>2} (1 − (p−1)⁻²)`, indexed by the primes `> 2`, backed by a
real `Multipliable` witness so positivity is earned, not junk-defaulted. -/

/-- Index type for the twin Euler product: the primes `> 2`. -/
abbrev PrimesGt2 : Type := {p : ℕ // p.Prime ∧ 2 < p}

/-- **Summability of the log-derivative data** `(p−1)⁻²` over the primes `> 2` —
comparison with the `p = 2` series `Σ (p:ℝ)⁻²` restricted to the prime subtype (each
factor `(p−1)² ≥ p²/4` for `p ≥ 3`). -/
theorem twinC2_summand_summable :
    Summable (fun p : PrimesGt2 => ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹) := by
  have hbase : Summable (fun p : PrimesGt2 => (((p : ℕ) : ℝ) ^ 2)⁻¹) :=
    ((Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)).subtype _
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (hbase.mul_left 4)
  obtain ⟨_, h2p⟩ := p.2
  have hp3 : (3 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    have : 3 ≤ (p : ℕ) := h2p
    exact_mod_cast this
  have hpos1 : (0 : ℝ) < (((p : ℕ) : ℝ) - 1) ^ 2 := by nlinarith [hp3]
  have hpos2 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 2 := by nlinarith [hp3]
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hpos1 hpos2]
  nlinarith [hp3, sq_nonneg (((p : ℕ) : ℝ) - 3)]

/-- Each factor `1 − (p−1)⁻²` is strictly positive (for `p ≥ 3`, `(p−1)² ≥ 4`). -/
theorem twinC2_factor_pos (p : PrimesGt2) : 0 < 1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹ := by
  obtain ⟨_, h2p⟩ := p.2
  have hp3 : (3 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    have : 3 ≤ (p : ℕ) := h2p
    exact_mod_cast this
  have hz : (4 : ℝ) ≤ (((p : ℕ) : ℝ) - 1) ^ 2 := by nlinarith [hp3]
  have hzpos : (0 : ℝ) < (((p : ℕ) : ℝ) - 1) ^ 2 := by linarith
  have hzne : (((p : ℕ) : ℝ) - 1) ^ 2 ≠ 0 := ne_of_gt hzpos
  have hrw : 1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹
      = ((((p : ℕ) : ℝ) - 1) ^ 2 - 1) / (((p : ℕ) : ℝ) - 1) ^ 2 := by
    rw [sub_div, div_self hzne, one_div]
  rw [hrw]
  exact div_pos (by linarith) hzpos

/-- **Log-summability** of the factors — the multipliability datum: `Σ log(1 − (p−1)⁻²)`
converges, from `twinC2_summand_summable` via `Real.summable_log_one_add_of_summable`. -/
theorem twinC2_log_summable :
    Summable (fun p : PrimesGt2 => Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹)) := by
  have h := Real.summable_log_one_add_of_summable twinC2_summand_summable.neg
  simpa only [sub_eq_add_neg] using h

/-- **The `Multipliable` witness** (GATE CORRECTION C2): the factor family is genuinely
multipliable, so the `tprod` below is the honest Euler product, not the junk default. -/
theorem twinC2_multipliable :
    Multipliable (fun p : PrimesGt2 => 1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹) :=
  Real.multipliable_of_summable_log twinC2_factor_pos twinC2_log_summable

/-- **The genuine twin constant** `twinC2 = ∏_{p>2} (1 − (p−1)⁻²)` — the Hardy–Littlewood
singular series `𝔖 = 2·twinC2`, halved by the window `[x/2, x−2]`. -/
noncomputable def twinC2 : ℝ :=
  ∏' p : PrimesGt2, (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹)

/-- **`twinC2 > 0`** — earned, not junk: `twinC2 = exp(∑' log factor) > 0` via the genuine
convergence chain.  Closes the zero-main-term alarm and the C2 junk-default trap. -/
theorem twinC2_pos : 0 < twinC2 := by
  rw [twinC2, ← Real.rexp_tsum_eq_tprod twinC2_factor_pos twinC2_log_summable]
  exact Real.exp_pos _

/-! ## D1b — the door Props (GATE CORRECTIONS C1/C4) -/

/-- **The Λ-weighted, window-correct main term** `twinC2 · x / log x` (C1). -/
noncomputable def twinMainTerm (x : ℕ) : ℝ := twinC2 * (x : ℝ) / Real.log x

/-- **`TwinTypeII`** — the level-θ two-sided twin type-II asymptotic for the Λ-weighted
carrier: for every saving `A > 0`, `|p1PrimeSum x 1 − twinMainTerm x| ≤ C·x/(log x)^A`. -/
def TwinTypeII : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    |p1PrimeSum x 1 - twinMainTerm x| ≤ C * (x : ℝ) / (Real.log x) ^ A

/-- **`TwinB_min`** — the minimal parity-breaking distributional input for twins (C4:
`θ` is commentary, not a binder). -/
def TwinB_min : Prop := TwinTypeII

/-- Anti-vacuity (D4.4): the landed twin carrier is inhabited at the toy point `x = 35`
(the twin pair `(17, 19)`); consumed here as a compiled fact. -/
example : 0 < p1PrimeSum 35 1 := p1_carrier_inhabited

/-! ## D2 — the implication `TwinB_min → TwinPrimeConjecture` (the stretch, class B)

Step 2 (the survivor extraction) is EASIER than the landed P₂ endgame: `keepR 1`
already filters to primes, so a nonzero summand delivers a genuine twin pair with no
prime-power crumb to discharge.  Step 1 (main term dominates) is `Wall.lean`-style rate
arithmetic; the threshold plumbing mirrors `Chen/Assembly.chen_of_hypotheses`. -/

/-- **Step 2 (survivor extraction).**  A positive Λ-weighted twin sum `p1PrimeSum x 1`
contains a genuine twin pair `n ≥ x/2`: a nonzero summand has `keepR 1 n ≠ 0` (so `n`
prime) and `p1Ind (n+2) ≠ 0` (so `n+2` prime), and `n` lies in the window `[x/2, x−2]`. -/
theorem twin_survivor_of_pos {x : ℕ} (hpos : 0 < p1PrimeSum x 1) :
    ∃ n : ℕ, x / 2 ≤ n ∧ n.Prime ∧ (n + 2).Prime := by
  have hpos' : 0 < ∑ n ∈ twinWindow x, vonMangoldt n * keepR 1 n * p1Ind (n + 2) := hpos
  obtain ⟨n, hn, hterm⟩ :
      ∃ n ∈ twinWindow x, 0 < vonMangoldt n * keepR 1 n * p1Ind (n + 2) := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    exact absurd (Finset.sum_nonpos hcon) (not_le.mpr hpos')
  have hkeepne : keepR 1 n ≠ 0 := by
    intro h0; rw [h0] at hterm; simp at hterm
  obtain ⟨hprime, -⟩ := keepR_eq_one_iff.mp (keepR_eq_one_of_ne_zero hkeepne)
  have hp2ne : p1Ind (n + 2) ≠ 0 := by
    intro h0; rw [h0] at hterm; simp at hterm
  have hnp : (n + 2).Prime := by
    unfold p1Ind at hp2ne
    by_contra hnp
    rw [if_neg hnp] at hp2ne
    exact hp2ne rfl
  have hlo : x / 2 ≤ n := by rw [twinWindow, Finset.mem_Icc] at hn; exact hn.1
  exact ⟨n, hlo, hprime, hnp⟩

/-- **Step 1 (main term dominates).**  Under `TwinTypeII`, there is a threshold `x₀` past
which the Λ-weighted twin sum is strictly positive: at saving `A = 2` the error
`C·x/(log x)²` is eventually below the main term `twinC2·x/log x`, which is positive by
`twinC2_pos`.  The threshold is `exp(C/twinC2)`, realised as a natural via
`exists_nat_gt`. -/
theorem twinTypeII_eventually_pos (h : TwinTypeII) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → 0 < p1PrimeSum x 1 := by
  obtain ⟨C, hC⟩ := h 2 (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.exp (C / twinC2))
  refine ⟨max m 2, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxm : m ≤ x := le_trans (le_max_left _ _) hx
  have hbound := hC x hx2
  have hC2 : 0 < twinC2 := twinC2_pos
  have hL : 0 < Real.log x := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hm0 : (0 : ℝ) < (m : ℝ) := lt_trans (Real.exp_pos _) hm
  have hlogm : C / twinC2 < Real.log m := by
    have := Real.log_lt_log (Real.exp_pos (C / twinC2)) hm
    rwa [Real.log_exp] at this
  have hlogx : C / twinC2 < Real.log x := by
    have hmx : Real.log m ≤ Real.log x := Real.log_le_log hm0 (by exact_mod_cast hxm)
    linarith
  have hkey : C < twinC2 * Real.log x := by
    have hml := mul_lt_mul_of_pos_right hlogx hC2
    have he : C / twinC2 * twinC2 = C := by field_simp
    rw [he] at hml
    rw [mul_comm]; exact hml
  have hLsq : (Real.log x) ^ (2 : ℝ) = (Real.log x) ^ 2 := Real.rpow_two _
  rw [hLsq] at hbound
  have htm : twinMainTerm x = twinC2 * (x : ℝ) / Real.log x := rfl
  have hgap : 0 < twinC2 * (x : ℝ) / Real.log x - C * (x : ℝ) / (Real.log x) ^ 2 := by
    have heq : twinC2 * (x : ℝ) / Real.log x - C * (x : ℝ) / (Real.log x) ^ 2
        = (x : ℝ) * (twinC2 * Real.log x - C) / (Real.log x) ^ 2 := by
      field_simp
    rw [heq]
    exact div_pos (mul_pos hxpos (by linarith [hkey])) (pow_pos hL 2)
  have h1 := (abs_le.mp hbound).1
  rw [htm] at h1
  linarith [h1, hgap]

/-- **The implication (D2).**  `TwinB_min → TwinPrimeConjecture`: past the threshold the
twin sum is positive, so each `n` yields a twin survivor `≥ x/2 ≥ n` (choosing
`x = max x₀ (2n)`); the `∀ n, ∃ p ≥ n` plumbing mirrors the landed Chen endgame.  R4
tripwire: the antecedent is the DISTRIBUTIONAL `TwinTypeII`, never proved here. -/
theorem twinB_min_implies_twins (h : TwinB_min) : TwinPrimeConjecture := by
  obtain ⟨x₀, hx₀⟩ := twinTypeII_eventually_pos h
  intro n
  obtain ⟨p, hlo, hp, hp2⟩ := twin_survivor_of_pos (hx₀ (max x₀ (2 * n)) (le_max_left _ _))
  have hx2n : 2 * n ≤ max x₀ (2 * n) := le_max_right _ _
  exact ⟨p, by omega, hp, hp2⟩

/-! ## D3 — the dichotomy `wall_or_door` (the headline; GATE CORRECTION C3)

A corollary of the landed `no_parity_beating_certificate`, carrying its FULL hypothesis
set explicitly (C3).  It formalises the wall/door partition: any lower-bound certificate
`Φ` that captures a positive proportion of the prime mass `siftedSum (sMinus x)` is NOT
`SieveAgree`-tolerant at level `D` — it must read the *sign* of the weights, past what
the tolerance hypothesis can see.  The proof is a one-line contraposition; the
quantifier structure (the fixed level `D`, the `2·B` tolerance, the `atTop` capture)
byte-matches `Wall.lean:533`.  The involution mechanism (`λ ↦ −λ` preserving every
`SieveAgree` field, `sPlus`/`sMinus` sharing `|rem|` bounds) is recorded in the module
docstring. -/
theorem wall_or_door (A : ℝ) (hA : 2 < A) (hLS : LambdaSummatory A) (D : ℕ) (hD : 2 ≤ D)
    (Φ : BoundingSieve → ℝ)
    (hcert : ∀ s, Φ s ≤ s.siftedSum)
    (hprop : ∃ c > 0, ∀ᶠ x in atTop, c * (sMinus x).siftedSum ≤ Φ (sMinus x)) :
    ¬ (∀ s t (B : ℝ), SieveAgree s t D B → |Φ s - Φ t| ≤ 2 * B) := fun htol =>
  no_parity_beating_certificate A hA hLS D hD Φ htol hcert hprop

end Salt.TwinBar
