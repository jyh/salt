/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦AFFINE FORK⟧ — the stride/offset de-specialization of the log-Chowla failure Prop,
λ-BV wave 2-W (the consumer at Tao's affine atom), 2026-09-03

The landed log-Chowla spine is Tao arXiv:1509.05422v2 Theorem 2.3 at the model point
`(a, b) = (1, 0)`; `ShiftFork` opened the shift-`h` axis beside it.  This module opens the
OTHER axis Tao's theorem is stated on — the affine forms `a·n + b`, `a·n + b + h` — as a
NEW failure Prop `logChowlaFailsAff` with new arity, and pins the landed `logChowlaFails h`
as its `(1, 0)` member.  Every landed declaration keeps its bytes and its arity.

What is here:
* `logChowlaFailsAff a b h eps x ω` — Tao (2.4)'s failure Prop at the affine forms
  (Liouville model `g₁ = g₂ = λ`), windowed `(x/ω, x]`, weight `1/n` IN THE CLASS INDEX
  (Tao's normaliser; the whole design rests on this and it is checked against the source).
* `LogChowlaAffSupply a b h` — THE SUPPLY DEMAND (a `def`, the crown of this block): the
  flat-family witnessed-scale spine at the affine forms.  It has a producer at `(1, 0)`
  (`Salt.MR.logChowlaAffSupply_one_zero`, in `Salt/MR/AffineSupplyH.lean`) and NONE at
  `a ≥ 2` — the `a ≥ 2` supply is wave 2-S, a port of Tao's general-`a` case, not this wave.
* `affWindow_survivorMass_ge` / `exists_affSurvivor_of_not_failsAff` — the finding of the
  freeze: at ONE residue class the window's own normalisation is the main term.  Where the
  affine atom does not fail, `Σ (1 − λλ)/n ≥ (1 − ε)·log ω − 1 ≥ 63.5 > 0`
  (`harmonic_window_bounds` + `regime_logOmega_ge`), so some window element has
  `λ(an+b)λ(an+b+h) = −1`.  No `ε` pin, no Möbius sum, no common window.
* `zRough_oddOmega_infinite_of_affSupply` — THE PRIZE SHAPE, conditional on the supply at
  `(P, r, 2)`: infinitely many `n` with `n(n+2)` coprime to `P` and `Ω(n(n+2))` odd.  With
  `exists_admissible_class` + `rough_of_coprime_primorial` it is stated at the primorial
  (`zRough_oddOmega_infinite_of_affSupply_primorial`): "for every fixed `z`, infinitely many
  `n` with `n(n+2)` `z`-rough and `Ω(n(n+2))` odd" — §7 verdict 3's honest statement, NOT
  almost-primality, nothing toward twin primes by itself, and CONDITIONAL on the unproduced
  stride supply.

⛔ **`a = 0` is degenerate** (refuter pass 2026-09-03, §A): mathlib's `liouville 0 = 0`, so at
`(a, b) = (0, 0)` every summand is `0`, `logChowlaFailsAff 0 0 h …` is FALSE at every regime,
and `LogChowlaAffSupply 0 0 h` is inhabited trivially.  `exists_affSurvivor_of_not_failsAff`
therefore carries `0 < a` EXPLICITLY (without it the statement is FALSE: `0 = −1`); the
consumers supply it from `0 < P` and `Nat.one_pos`.  `LogChowlaAffSupply`'s own definition
is NOT weakened — its vacuous inhabitation at `(0, 0)` is recorded here, not fenced.

Scope: definitional/foundational plus one elementary consumer chain.  No claim about Chowla,
about the door, or about twins is made or moved by this file.  Import direction: this file is
`Salt.Entropy`-internal (`Salt/Entropy` cannot import `Salt/MR` or `Salt/TwinBar`); the
`a = 1` supply and the integration control live in `Salt/MR/AffineSupplyH.lean`.
-/
import Salt.Entropy.Chowla.ShiftFork
import Salt.Entropy.Chowla.LogMeasure
import Salt.Entropy.Chowla.TowerFlatBuilder
import Salt.Entropy.Chowla.Regime
import Salt.Entropy.Chowla.SignSplit
import Mathlib

open ArithmeticFunction Finset

namespace Salt.Entropy.Chowla

/-! ## W1 — the failure Prop at Tao Theorem 2.3's affine forms -/

/-- **W1.** Tao 1509.05422 Theorem 2.3's failure Prop at the affine forms `a·n + b`,
`a·n + b + h` (Liouville model): "log-Chowla fails at stride `a`, offset `b`, shift `h`,
scale `(x, ω)`, margin `ε`".  The weight is `1/n` in the CLASS index and the right-hand side
is `ε·log ω` at the full window scale — Tao's own normalisation (textdump:555-560), which is
what makes the window's normaliser the main term at one class.  At `(a, b) = (1, 0)` it is
the landed `logChowlaFails h` (`ShiftFork.lean:62`), see `logChowlaFailsAff_one_zero`.

At `a = 0` every summand vanishes (`liouville 0 = 0`) and the Prop is false at every regime;
see the module header. -/
def logChowlaFailsAff (a b h : ℕ) (eps : ℚ) (x ω : ℕ) : Prop :=
  (eps : ℝ) * Real.log (ω : ℝ) <
    |∑ n ∈ Finset.Ioc (x / ω) x,
      (ArithmeticFunction.liouville (a * n + b) : ℝ)
        * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) / (n : ℝ)|

/-- **W2 (compat, class A).**  `(a, b) = (1, 0)` is the landed shift-`h` Prop: after
`unfold`, the forms are `1 * n + 0` and `1 * n + 0 + h`, and `simp only [one_mul, add_zero]`
(NOT `zero_add`) under the binder closes the `Iff`. -/
theorem logChowlaFailsAff_one_zero (h : ℕ) (eps : ℚ) (x ω : ℕ) :
    logChowlaFailsAff 1 0 h eps x ω ↔ logChowlaFails h eps x ω := by
  unfold logChowlaFailsAff logChowlaFails
  simp only [one_mul, add_zero]

/-! ## S1 — the supply demand -/

/-- **S1 — THE SUPPLY DEMAND (a `def`, the crown of this block).**
The flat-family witnessed-scale spine at the affine forms: for every `A₀` a regime of the
flat family (`R.Hlo = flatDesignBase A`, `162 ≤ A`, `A₀ ≤ A`) at which log-Chowla does NOT
fail at `(a, b, h)`.  The `ε` is the regime's own (`R.eps ≤ 1/2` by `R.heps1`), and that is
enough for every consumer below — no upper pin on `ε` is demanded.

Producers: at `(1, 0)` and every `h` with `log h ≤ 7`, `Salt.MR.logChowlaAffSupply_one_zero`
(from the landed `logChowla2_v7_rated_h`).  At `a ≥ 2`: NONE — that is wave 2-S.
⛔ At `(a, b) = (0, 0)` this Prop is inhabited VACUOUSLY (`liouville 0 = 0` makes every summand
of `logChowlaFailsAff 0 0 h …` vanish); nothing consumes `a = 0`, and the consumers below
carry `0 < a`. -/
def LogChowlaAffSupply (a b h : ℕ) : Prop :=
  ∀ A₀ : ℝ, ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧
    ∃ R : ChowlaRegime, R.Hlo = flatDesignBase A ∧ ¬ logChowlaFailsAff a b h R.eps R.x R.ω

/-! ## W3–W4 — the survivor at one class: the window's normaliser is the main term -/

/-- **W3 (class B).**  At a window where the affine atom does not fail, the survivor mass
`Σ (1 − λ(an+b)λ(an+b+h))/n` is at least `(1 − ε)·log ω − 1`: `sum_sub_distrib` splits the
sum into `Σ 1/n − Σ λλ/n`, `harmonic_window_bounds .1` bounds the head below by `log ω − 1`,
and `¬ hnf` (`not_lt`, then `abs_le`) bounds the tail by `ε·log ω`.  TRUE at every `(a, b)`,
`a = b = 0` included (the split needs no positivity). -/
theorem affWindow_survivorMass_ge {a b h : ℕ} {eps : ℚ} {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hnf : ¬ logChowlaFailsAff a b h eps x ω) :
    (1 - (eps : ℝ)) * Real.log (ω : ℝ) - 1
      ≤ ∑ n ∈ Finset.Ioc (x / ω) x,
          (1 - (ArithmeticFunction.liouville (a * n + b) : ℝ)
            * (ArithmeticFunction.liouville (a * n + b + h) : ℝ)) / (n : ℝ) := by
  have hb := (harmonic_window_bounds hx hω hωx).1
  simp only [logChowlaFailsAff, not_lt] at hnf
  have htail := (abs_le.mp hnf).2
  have hsplit : ∑ n ∈ Finset.Ioc (x / ω) x,
      (1 - (ArithmeticFunction.liouville (a * n + b) : ℝ)
        * (ArithmeticFunction.liouville (a * n + b + h) : ℝ)) / (n : ℝ)
      = (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        - ∑ n ∈ Finset.Ioc (x / ω) x,
            (ArithmeticFunction.liouville (a * n + b) : ℝ)
              * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) / (n : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [sub_div, one_div]
  rw [hsplit]
  linarith

/-- Liouville at a nonzero argument is `±1` after the cast to `ℝ`. -/
private lemma liouville_real_eq_one_or {m : ℕ} (hm : m ≠ 0) :
    (ArithmeticFunction.liouville m : ℝ) = 1 ∨ (ArithmeticFunction.liouville m : ℝ) = -1 := by
  rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors m) with hpow | hpow
  · left
    rw [ArithmeticFunction.liouville_apply hm, hpow]
    norm_num
  · right
    rw [ArithmeticFunction.liouville_apply hm, hpow]
    norm_num

/-- **W4 (class B).**  A survivor in the window.  The floor: `affWindow_survivorMass_ge` at
`R.hx R.hω R.hωx`, then `linarith [regime_logOmega_ge R, R.heps1]` (the LANDED
`129 ≤ log R.ω`, `SignSplit.lean:174` — `R.hωbig` ALONE does not give it, its leading term's
sign needs `hPNTwindow` + `hHlo_floor` + `hHlohi`, which that lemma already runs), so the
sum is `≥ 63.5 > 0`.  A positive sum has a positive term (`Finset.exists_lt_of_sum_lt`
against the zero function, or the contrapositive of `Finset.sum_nonpos`); a positive term
`(1 − λλ)/n > 0` forces `λλ < 1`; and `λλ ∈ {−1, 1}` because BOTH arguments are nonzero —
`n ≥ 1` on the window (`Nat.div_pos R.hωx` gives `1 ≤ x/ω`) and `0 < a` — so
`liouville_apply` + `neg_one_pow_eq_or` on each factor.

⛔ `0 < a` is NOT decorative: at `a = b = 0` the hypothesis holds at every regime
(`liouville 0 = 0`) and the conclusion reads `0 = −1`.  Refuter pass 2026-09-03, §A. -/
theorem exists_affSurvivor_of_not_failsAff {a b h : ℕ} (ha : 0 < a) {R : ChowlaRegime}
    (hnf : ¬ logChowlaFailsAff a b h R.eps R.x R.ω) :
    ∃ n ∈ Finset.Ioc (R.x / R.ω) R.x,
      (ArithmeticFunction.liouville (a * n + b) : ℝ)
        * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) = -1 := by
  have hmass := affWindow_survivorMass_ge R.hx R.hω R.hωx hnf
  have hlog := regime_logOmega_ge R
  have hεhalf : (R.eps : ℝ) ≤ 1 / 2 := by
    have hq : ((R.eps : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast R.heps1
    simpa using hq
  have hhalf : (1 / 2 : ℝ) * Real.log (R.ω : ℝ) ≤ (1 - (R.eps : ℝ)) * Real.log (R.ω : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hdpos : 0 < R.x / R.ω := Nat.div_pos R.hωx (by have := R.hω; omega)
  by_contra hcon
  have hzero : ∑ n ∈ Finset.Ioc (R.x / R.ω) R.x,
      (1 - (ArithmeticFunction.liouville (a * n + b) : ℝ)
        * (ArithmeticFunction.liouville (a * n + b + h) : ℝ)) / (n : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    have hne : (ArithmeticFunction.liouville (a * n + b) : ℝ)
        * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) ≠ -1 :=
      fun hq => hcon ⟨n, hn, hq⟩
    rw [Finset.mem_Ioc] at hn
    have hnpos : 0 < n := lt_trans hdpos hn.1
    have han : 0 < a * n := Nat.mul_pos ha hnpos
    have h1 : a * n + b ≠ 0 := (Nat.add_pos_left han b).ne'
    have h2 : a * n + b + h ≠ 0 := (Nat.add_pos_left (Nat.add_pos_left han b) h).ne'
    have hprod : (ArithmeticFunction.liouville (a * n + b) : ℝ)
        * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) = 1 := by
      rcases liouville_real_eq_one_or h1 with p1 | p1 <;>
        rcases liouville_real_eq_one_or h2 with p2 | p2
      · rw [p1, p2]; norm_num
      · exact absurd (by rw [p1, p2]; norm_num) hne
      · exact absurd (by rw [p1, p2]; norm_num) hne
      · rw [p1, p2]; norm_num
    rw [hprod]
    norm_num
  linarith [hmass, hzero]

/-! ## W5–W7 — the elementary bridges -/

/-- **W5 (class A).**  `λ(m)·λ(m+2) = −1 ↔ Ω(m(m+2)) odd`, `m ≥ 1`.  Complete
multiplicativity is `Salt.Entropy.Chowla.liouville_mul` (`ChowlaFailure.lean:67`, in scope
here; the `Salt.TwinBar` twin `liouville_twinProd_mul` is NOT importable from `Salt/Entropy`),
then `ArithmeticFunction.liouville_apply` (`m(m+2) ≠ 0`) and the parity of `(−1)^Ω`
(`neg_one_pow_eq_neg_one_iff_odd`-shape / `Odd.neg_one_pow`, `Even.neg_one_pow`). -/
theorem liouville_shift_two_eq_neg_one_iff {m : ℕ} (hm : 0 < m) :
    (ArithmeticFunction.liouville m : ℝ) * (ArithmeticFunction.liouville (m + 2) : ℝ) = -1
      ↔ Odd (ArithmeticFunction.cardFactors (m * (m + 2))) := by
  have hne : m * (m + 2) ≠ 0 := Nat.mul_ne_zero hm.ne' (by omega)
  have hkey : (ArithmeticFunction.liouville m : ℝ)
      * (ArithmeticFunction.liouville (m + 2) : ℝ)
      = (-1 : ℝ) ^ (ArithmeticFunction.cardFactors (m * (m + 2))) := by
    have hz := liouville_mul m (m + 2)
    rw [ArithmeticFunction.liouville_apply hne] at hz
    have hr := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at hr
    exact hr.symm
  rw [hkey]
  constructor
  · intro hpow
    rcases Nat.even_or_odd (ArithmeticFunction.cardFactors (m * (m + 2))) with hev | hod
    · rw [hev.neg_one_pow] at hpow
      norm_num at hpow
    · exact hod
  · intro hod
    exact hod.neg_one_pow

/-- **W6 (class A).**  An admissible class mod `P` stays coprime along the progression:
`hcop` splits (`Nat.Coprime.coprime_dvd_left` with `dvd_mul_right`/`dvd_mul_left`) into
`Coprime r P` and `Coprime (r+2) P`; each transports by `Nat.coprime_add_mul_left_left`
(present the forms as `r + P * n` and `(r + 2) + P * n`, one `add_comm`/`omega`-rewrite each);
`Nat.Coprime.mul_left` recombines. -/
theorem coprime_twinProd_of_affine {P r : ℕ} (hcop : Nat.Coprime (r * (r + 2)) P) (n : ℕ) :
    Nat.Coprime ((P * n + r) * (P * n + r + 2)) P := by
  have hr : Nat.Coprime r P := Nat.Coprime.coprime_dvd_left (dvd_mul_right r (r + 2)) hcop
  have hr2 : Nat.Coprime (r + 2) P :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_left (r + 2) r) hcop
  have e2 : P * n + r + 2 = P * n + (r + 2) := by ring
  rw [e2]
  exact Nat.Coprime.mul_left ((Nat.coprime_mul_left_add_left r P n).mpr hr)
    ((Nat.coprime_mul_left_add_left (r + 2) P n).mpr hr2)

/-- **W6b (class A).**  An admissible class exists mod every `P ≥ 1` — and the witness is
EXPLICIT, no CRT: `r := P − 1` has `r ≡ −1` and `r + 2 ≡ 1 (mod P)`, so `r(r+2) = P² − 1` is
coprime to `P`.  In Lean: `Coprime (P - 1) P` by `Nat.coprime_self_add_right` after
`P = (P - 1) + 1` (`Nat.sub_add_cancel hP`) and `Nat.coprime_one_right`; `Coprime (P - 1 + 2) P`
by `Nat.coprime_add_self_left` after `P - 1 + 2 = 1 + P`; then `Nat.Coprime.mul_left`.
Instantiated at `P = primorial z` (`primorial_pos`) this is the "`r` admissible" of the prize
sentence, minted rather than read from a docstring (refuter pass 2026-09-03, §B7). -/
theorem exists_admissible_class (P : ℕ) (hP : 0 < P) :
    ∃ r : ℕ, Nat.Coprime (r * (r + 2)) P := by
  refine ⟨P - 1, ?_⟩
  have h1 : Nat.Coprime (P - 1) P := by
    have hc : Nat.Coprime (P - 1) (P - 1 + 1) :=
      Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    rwa [Nat.sub_add_cancel hP] at hc
  have h2 : Nat.Coprime (P - 1 + 2) P := by
    have hc : Nat.Coprime (1 + P) P := Nat.coprime_add_self_left.mpr (Nat.coprime_one_left P)
    have e : P - 1 + 2 = 1 + P := by omega
    rwa [← e] at hc
  exact Nat.Coprime.mul_left h1 h2

/-- **W6c (class A).**  Coprime to the primorial of `z` means `z`-rough: every prime factor
exceeds `z`.  For `p ∈ m.primeFactors` (`Nat.mem_primeFactors`: `p.Prime ∧ p ∣ m ∧ m ≠ 0`),
if `p ≤ z` then `p ∣ primorial z` (`Nat.Prime.dvd_primorial_iff`), so `p ∣ gcd m (primorial z)
= 1` (`Nat.Coprime.eq_one_of_dvd`-shape / `Nat.eq_one_of_dvd_one`), contradicting
`p.Prime.one_lt`. -/
theorem rough_of_coprime_primorial {m z : ℕ} (hcop : Nat.Coprime m (primorial z)) :
    ∀ p ∈ m.primeFactors, z < p := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpm, -⟩ := hp
  rcases Nat.lt_or_ge z p with hlt | hle
  · exact hlt
  · exfalso
    have hdvd : p ∣ primorial z := (Nat.Prime.dvd_primorial_iff hpp).mpr hle
    have hg : p ∣ Nat.gcd m (primorial z) := Nat.dvd_gcd hpm hdvd
    rw [hcop] at hg
    exact absurd (Nat.eq_one_of_dvd_one hg) hpp.ne_one

/-- **W7 (class A).**  `flatDesignBase A = ⌈exp(exp(3.2A))⌉₊` is unbounded in `A`
(`TowerFlatBuilder.lean:95`): take `A₀ := Real.log (Real.log (M + 1)) / 3.2 + 1` when
`1 < M + 1`, so `exp(exp(3.2A)) ≥ exp(exp(3.2A₀)) > M + 1 > M` (`Real.exp_le_exp`,
`Real.exp_log`, `Nat.le_ceil`); the case `M + 1 ≤ 1` (so `M ≤ 0 < 1 ≤ flatDesignBase A`) is
its own line — `flatDesignBase A ≥ 1` because `exp(·) > 0` and `Nat.ceil_pos`. -/
theorem flatDesignBase_unbounded (M : ℝ) :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → M < ((flatDesignBase A : ℕ) : ℝ) := by
  refine ⟨max M 0, fun A hA => ?_⟩
  have hAM : M ≤ A := le_trans (le_max_left _ _) hA
  have hA0 : (0 : ℝ) ≤ A := le_trans (le_max_right _ _) hA
  have h1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  have h2 : Real.exp (3.2 * A) + 1 ≤ Real.exp (Real.exp (3.2 * A)) := Real.add_one_le_exp _
  have h3 : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    rw [flatDesignBase]
    exact Nat.le_ceil _
  linarith

/-! ## W8 — the prize shape -/

/-- **W8 — THE PRIZE SHAPE (class B), CONDITIONAL on the supply at `(P, r, 2)`.**  Every
survivor `n` of `exists_affSurvivor_of_not_failsAff` (at `ha := hP`) lies in `(x/ω, x]`, and
`x/ω ≥ R.Hhi ≥ R.Hlo = flatDesignBase A` (`R.hheadroom`, `R.hHlohi`, S1's equation), and
`A ≥ A₀` is free — so `m := P·n + r ≥ n > M` for every `M` (`flatDesignBase_unbounded`,
`hsup A₀`), and the set is unbounded, hence infinite (`Set.infinite_of_not_bddAbove`).
Membership: `liouville_shift_two_eq_neg_one_iff` at `m` (`0 < m` from `n ≥ 1`) and
`coprime_twinProd_of_affine`.  The forms `P * n + r + 2` and `m + 2` are syntactically equal.

⛔ Conditional on `LogChowlaAffSupply P r 2`, which has NO producer at `P ≥ 2` (wave 2-S).
NOT almost-primality; nothing toward twin primes by itself. -/
theorem zRough_oddOmega_infinite_of_affSupply {P r : ℕ} (hP : 0 < P)
    (hcop : Nat.Coprime (r * (r + 2)) P) (hsup : LogChowlaAffSupply P r 2) :
    {n : ℕ | Nat.Coprime (n * (n + 2)) P
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  intro hbdd
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨A₀, hA₀⟩ := flatDesignBase_unbounded (M : ℝ)
  obtain ⟨A, -, hA₀A, R, hHloeq, hnf⟩ := hsup A₀
  obtain ⟨n, hn, hprod⟩ := exists_affSurvivor_of_not_failsAff hP hnf
  rw [Finset.mem_Ioc] at hn
  have hbaseR : (M : ℝ) < ((flatDesignBase A : ℕ) : ℝ) := hA₀ A hA₀A
  have hbase : M < flatDesignBase A := by exact_mod_cast hbaseR
  have hle : flatDesignBase A ≤ R.x / R.ω := by
    rw [← hHloeq]
    exact le_trans R.hHlohi R.hheadroom
  have hMn : M < n := lt_trans hbase (lt_of_le_of_lt hle hn.1)
  have hnle : n ≤ P * n + r := le_trans (Nat.le_mul_of_pos_left n hP) (Nat.le_add_right _ _)
  have hmpos : 0 < P * n + r := lt_of_le_of_lt (Nat.zero_le M) (lt_of_lt_of_le hMn hnle)
  have hmem : P * n + r ∈ {n : ℕ | Nat.Coprime (n * (n + 2)) P
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))} := by
    refine ⟨coprime_twinProd_of_affine hcop n, ?_⟩
    exact (liouville_shift_two_eq_neg_one_iff hmpos).mp hprod
  have hub := hM hmem
  omega

/-- **W8b (class A) — the prize sentence, at the primorial.**
`zRough_oddOmega_infinite_of_affSupply` at `P := primorial z` (`primorial_pos`) with
`rough_of_coprime_primorial` under `Set.Infinite.mono`: "for every fixed `z`, infinitely many
`n` with `n(n+2)` `z`-rough and `Ω(n(n+2))` odd" — §7 verdict 3's honest statement, and
`exists_admissible_class` supplies an `r` for every `z`.  ⛔ Still CONDITIONAL on the stride
supply at `(primorial z, r, 2)`, held by nobody; at `z ≤ 1` (`primorial z = 1`) it is the
unconditional `Salt.MR.oddOmega_twinProd_infinite`. -/
theorem zRough_oddOmega_infinite_of_affSupply_primorial {z r : ℕ}
    (hcop : Nat.Coprime (r * (r + 2)) (primorial z))
    (hsup : LogChowlaAffSupply (primorial z) r 2) :
    {n : ℕ | (∀ p ∈ (n * (n + 2)).primeFactors, z < p)
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))}.Infinite := by
  have hinf := zRough_oddOmega_infinite_of_affSupply (primorial_pos z) hcop hsup
  exact hinf.mono (fun n hn => ⟨rough_of_coprime_primorial hn.1, hn.2⟩)

end Salt.Entropy.Chowla
