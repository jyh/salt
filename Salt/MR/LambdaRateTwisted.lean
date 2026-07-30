/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.LambdaRate

/-!
# ⟦O3⟧ — THE TWISTED `μ → λ` BRIDGE (the KMT port, wave P-1)

Design: `docs/exploration/port-freeze-0729.md`, §"What the refuters changed" item 3
(the obligation register O1–O7).  This file is the `χ,t`-twisted twin of the LANDED
`Salt/TwinBar/LambdaRate.lean` chain, i.e. **O3**:

> the `χ,t`-twisted bridge is mechanical — complete multiplicativity distributes over
> the convolution.

Everything here is unconditional EXCEPT the one named input `MmuChiRate`, which is the
port's centerpiece and is **NOT landed** (see "The honest slot" below).

## Contents

* **§1 — the general law.**  `mul_apply_mul_twist`: for `f g : ArithmeticFunction R` and any
  `h : ℕ → R` that is completely multiplicative on nonzero arguments,
  `(f ∗ g)(n)·h(n) = ∑_{ab=n} (f(a)h(a))·(g(b)h(b))` for `n ≠ 0`; and its
  `ArithmeticFunction`-level form `pmul_mul_of_twist`,
  `(f ∗ g)·h = (f·h) ∗ (g·h)`.  **Mathlib does not have this** (checked 2026-07-29 against
  `Mathlib/NumberTheory/ArithmeticFunction/*`: it has the pointwise product
  `ArithmeticFunction.pmul`, `pmul_comm`, `pmul_assoc`, `pmul_zeta`,
  `IsMultiplicative.pmul`, and `ppow`, but no law relating `pmul` to the Dirichlet
  convolution `*`, and no `IsCompletelyMultiplicative` predicate at all).
* **§2 — the twisted datum.**  `chiBarTwist χ t n = χ̄(n)·n^{it}`, its complete
  multiplicativity (`chiBarTwist_mul`) and 1-boundedness (`norm_chiBarTwist_le_one`); §1
  instantiated at it through the landed `λ = 1_sq ∗ μ`
  (`liouville_twist_eq_sum_divisorsAntidiagonal`).
* **§3 — the twisted summatory functions and the truncation transfer.**
  `MmuChi`, `MlambdaChi` (ℂ-valued), and
  `MlambdaChi_eq_sum_MmuChi : M_{λχ̄}(y) = ∑_{d ≤ √y} χ̄(d²)d^{2it}·M_{μχ̄}(⌊y/d²⌋)`
  — the twisted `Mlambda_eq_sum_Mmu` (`LambdaRate.lean:298`), unconditional.
* **§4 — the rate fold.**  `MmuChiRate` (the honest slot), `LambdaChiSummatory`,
  `MlambdaChi_rate` and the deliverable `LambdaChiSummatory_of_MmuChiRate`.

## THE CONJUGATION CONVENTION (the ⟦barred χ⟧ trap)

KMT print the twist **unbarred** (`χ(n)·n^{-it}`).  **This file follows the CORPUS, which
bars it**: the corpus's twisted Liouville datum is
`Salt.MR.lamChi χ n = lam n · conj (χ n)` (`Salt/MR/ChiFloor.lean:184`) and its
integer-correct sibling `Salt.MR.liouChi χ n = liouvilleC n · conj (χ n)`
(`Salt/MR/CapFreeAssembly.lean:454`, completely multiplicative by
`Salt.MR.liouChi_mul`, `Salt/MR/M4ErrRewire.lean:289`).  The character-sum orientation that
forces the bar is recorded at `Salt/MR/M4Chars.lean:29–60`: the residue-class decomposition
`λ(m)·1_{m ≡ b₀} = (1/φ(q))·∑_χ χ(b₀)·lamChi χ m` puts the **unconjugated** character on the
COEFFICIENT and the conjugate on the DATUM.  So the datum here is `λ·χ̄` and the sums are
`M_{λχ̄}`, `M_{μχ̄}`.  Note the sibling name `Salt.MR.chiTwist` (`Salt/MR/ChiEuler.lean:74`)
is the **unbarred** `g`-side datum `χ(n)·n^{it}` — a different object; hence the fresh name
`chiBarTwist` here.

Sign of the height: `chiBarTwist χ t` carries `n^{+it}` (written out as the corpus's own
`Salt.MR.costwist t n = exp((t·log n)·I)`, `Salt/MR/NonPret.lean:52` — syntactically the same
term, so the two are `rfl`-equal for any future consumer).  KMT's `n^{-it}` is
`chiBarTwist χ (-t)`; every statement below is `∀ t : ℝ`, so the sign is immaterial.

## The carriers (the ⟦ArithmeticFunction vs `ℕ → ℂ`⟧ trap)

`Salt/TwinBar/LambdaRate.lean` uses `ArithmeticFunction` for the *identity* (`chiSq`,
`moebius`, `liouville`) and bare ℕ-indexed `Finset.Icc 1 y` sums for the *summatory
functions*.  This file makes the SAME choice.  The landed `Salt.TwinBar.Mmu`/`Mlambda` are
ℝ-valued and are **not touched**: the twisted sums are ℂ-valued with `‖·‖` in the rate.

## The imports (deliberate)

Only `Salt.TwinBar.LambdaRate`.  The MR data `liouChi`/`costwist` sit behind a large import
cone (`CapFreeAssembly` → `VkTwistLadder`/`SiegelBand`/`RHSGrade`/`M4Residue`), so the twist
is written out here instead; `chiBarTwist χ t n = liouChi-style χ̄(n) · costwist t n` holds by
`rfl` once a consumer imports both.  All five arithmetic helpers of the fold are
CHARACTER-BLIND and are **cited, not re-proved**: `Salt.TwinBar.sum_inv_sq_Icc_le`,
`sum_inv_sq_Ioc_le`, `log_natSqrt_ge`, `le_sqrt_sqrt_of_pow4_le`, `eventually_pow4_le`.

## THE HONEST SLOT (`MmuChiRate` is NOT landed)

`MmuChiRate` is a hypothesis `Prop`, the twisted twin of `Salt.TwinBar.MmuRate`
(`LambdaRate.lean:58`).  Unlike `MmuRate` — which is LANDED as
`Salt.SW.mmuRate_holds` (`Salt/SW/MobiusRateClose.lean:1059`) — **`MmuChiRate` has no
proof in this corpus and is not expected to be cheap.**  It is exactly the port's two open
obligations from the freeze:

* **O4** — the `χ`-twisted μ-rate: the `MobiusRateClose` re-run at `L(s,χ)` in place of
  `ζ(s)` (freeze estimate 700–1400 ln);
* **O5** — the `t`-aspect, i.e. the `χ`-VK / Landau–Page zero-free region (freeze estimate
  800–2000 ln; **the same stone as P-6's stone B**, the campaign's isolated `D`-risk, in
  front of which the freeze puts the P-0′ B-probe).

Nothing in this file discharges any part of O4 or O5, and nothing here should be read as
evidence that they are close.  What this file establishes is only the *bridge*: given the
twisted **μ**-rate, the twisted **λ**-rate follows by the same hyperbola fold as the
untwisted case, with the price stated next.

## The honest price of the fold (the ⟦spend the ±1 explicitly⟧ rule)

The fold evaluates the μ-rate at `⌊y/d²⌋`, not at `y`, and only `log⌊y/d²⌋ ≥ (log y)/4` is
available there (`Salt.TwinBar.log_natSqrt_ge`).  The conductor gate therefore moves:
`MmuChiRate` is stated at the freeze's range `q ≤ (log y)^12` and `LambdaChiSummatory` comes
out at `q ≤ (log y)^11`.  **The fold spends exactly one of the twelve exponents of conductor
range** — the `4^12` loss is absorbed by that one exponent for `y` past `exp(4^12)`, an
eventual threshold folded into the `x₀` of the conclusion.  (The gate is on the MODULUS `q`,
not on `conductor χ`; since `conductor χ ≤ q` this is the weaker, hence more conservative,
form of the freeze's `cond χ ≤ (log y)^12` — it demands less of O4/O5.)
-/

open ArithmeticFunction
open scoped BigOperators

namespace Salt.MR

/-! ## 1. A completely multiplicative twist distributes over Dirichlet convolution -/

/-- **The general law (§1).**  If `h : ℕ → R` is completely multiplicative on nonzero
arguments (`h(ab) = h(a)·h(b)` for `a, b ≠ 0`), then twisting by `h` distributes over the
Dirichlet convolution: for every `n ≠ 0`,

  `(f ∗ g)(n)·h(n) = ∑_{ab = n} (f(a)·h(a))·(g(b)·h(b))`.

A one-line rearrangement over the divisor antidiagonal: `h(n) = h(a)·h(b)` on each pair.
The `n ≠ 0` and `a, b ≠ 0` guards are real — the twists we care about (`χ̄(n)·n^{it}`) are
NOT multiplicative at `0` (`log 0 = 0` makes the phase `1` there).

Mathlib has no such lemma: it has `ArithmeticFunction.pmul` and its own algebra
(`pmul_comm`/`pmul_assoc`/`pmul_zeta`/`IsMultiplicative.pmul`/`ppow`) but nothing relating
`pmul` to `*`, and no completely-multiplicative predicate. -/
theorem mul_apply_mul_twist {R : Type*} [CommSemiring R] (f g : ArithmeticFunction R)
    {h : ℕ → R} (hh : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → h (a * b) = h a * h b)
    {n : ℕ} (hn : n ≠ 0) :
    (f * g) n * h n
      = ∑ ab ∈ n.divisorsAntidiagonal, (f ab.1 * h ab.1) * (g ab.2 * h ab.2) := by
  rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ab hab => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hab
  obtain ⟨hprod, _⟩ := hab
  have ha : ab.1 ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hprod
    exact hn hprod.symm
  have hb : ab.2 ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hprod
    exact hn hprod.symm
  rw [← hprod, hh ab.1 ab.2 ha hb]
  ring

/-- **The general law, `ArithmeticFunction`-level.**  `(f ∗ g)·h = (f·h) ∗ (g·h)` (pointwise
product `pmul` against Dirichlet convolution `*`) for `h` completely multiplicative on
nonzero arguments.  At `n = 0` both sides vanish because every `ArithmeticFunction` does. -/
theorem pmul_mul_of_twist {R : Type*} [CommSemiring R] (f g h : ArithmeticFunction R)
    (hh : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → h (a * b) = h a * h b) :
    (f * g).pmul h = (f.pmul h) * (g.pmul h) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ArithmeticFunction.pmul_apply, mul_apply_mul_twist f g hh hn,
      ArithmeticFunction.mul_apply]
    exact Finset.sum_congr rfl fun ab _ => by
      rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]

/-! ## 2. The twisted datum `χ̄(n)·n^{it}` -/

/-- **The twisted datum `χ̄(n)·n^{it}`** (BARRED `χ` — the corpus's `lamChi`/`liouChi`
orientation, see the file header).  The phase factor is written out as the corpus's own
`Salt.MR.costwist t n = exp((t·log n)·I)` (`Salt/MR/NonPret.lean:52`), term-for-term, so the
two agree by `rfl` for a consumer importing both. -/
noncomputable def chiBarTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℕ → ℂ :=
  fun n => (starRingEnd ℂ) (χ (n : ZMod q))
    * Complex.exp (((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)

/-- **The twisted datum is COMPLETELY MULTIPLICATIVE on nonzero arguments** — the single
analytic input to §1's general law.  `χ` is a `MulChar` (`map_mul`, no coprimality) and the
phase adds through `Real.log_mul` (which is where `a, b ≠ 0` is spent: `log 0 = 0`). -/
theorem chiBarTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ∀ a b : ℕ, a ≠ 0 → b ≠ 0 →
      chiBarTwist χ t (a * b) = chiBarTwist χ t a * chiBarTwist χ t b := by
  intro a b ha hb
  have hca : ((a : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hcb : ((b : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hb
  unfold chiBarTwist
  have hcast : ((a * b : ℕ) : ZMod q) = (a : ZMod q) * (b : ZMod q) := by push_cast; ring
  have hlog : Real.log ((a * b : ℕ) : ℝ) = Real.log (a : ℝ) + Real.log (b : ℝ) := by
    push_cast
    exact Real.log_mul hca hcb
  have hphase : (((t * Real.log ((a * b : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)
      = ((t * Real.log (a : ℝ) : ℝ) : ℂ) * Complex.I
        + ((t * Real.log (b : ℝ) : ℝ) : ℂ) * Complex.I := by
    rw [hlog]
    push_cast
    ring
  rw [hcast, map_mul, map_mul, hphase, Complex.exp_add]
  ring

/-- The twisted datum is 1-bounded (it VANISHES at `p | q`, as `χ` does). -/
theorem norm_chiBarTwist_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    ‖chiBarTwist χ t n‖ ≤ 1 := by
  unfold chiBarTwist
  rw [norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact DirichletCharacter.norm_le_one χ _

/-- At the trivial character mod `1` and height `0` the twist is identically `1` — the
consistency check that pins the orientation (`ZMod 1` is a subsingleton, and the phase is
`exp 0`). -/
@[simp] theorem chiBarTwist_one_zero (n : ℕ) :
    chiBarTwist (1 : DirichletCharacter ℂ 1) 0 n = 1 := by
  unfold chiBarTwist
  rw [Subsingleton.elim ((n : ℕ) : ZMod 1) 1, map_one, map_one]
  norm_num

/-- **§1 instantiated at the twisted datum** through the landed `λ = 1_sq ∗ μ`
(`Salt.TwinBar.liouville_eq_chiSq_mul_moebius`): for `n ≠ 0`,
`λ(n)·χ̄(n)n^{it} = ∑_{ab=n} (1_sq(a)·χ̄(a)a^{it})·(μ(b)·χ̄(b)b^{it})`.

This is the conceptual content of O3 ("complete multiplicativity distributes over the
convolution").  The summatory fold of §3 does NOT consume this form: it goes through the
landed `d`-shaped identity `Salt.TwinBar.liouville_eq_sum_moebius` instead, which has
already paid for the square-divisor reindex `a = d²`; re-running that bijection in the
twisted setting would be ~45 lines of duplication for the same content. -/
theorem liouville_twist_eq_sum_divisorsAntidiagonal {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ((ArithmeticFunction.liouville n : ℤ) : ℂ) * chiBarTwist χ t n
      = ∑ ab ∈ n.divisorsAntidiagonal,
          (((Salt.TwinBar.chiSq ab.1 : ℤ) : ℂ) * chiBarTwist χ t ab.1)
            * (((ArithmeticFunction.moebius ab.2 : ℤ) : ℂ) * chiBarTwist χ t ab.2) := by
  have hcoe : ((ArithmeticFunction.liouville : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)
      = ((Salt.TwinBar.chiSq : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)
        * ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
    rw [← ArithmeticFunction.intCoe_mul, Salt.TwinBar.liouville_eq_chiSq_mul_moebius]
  have h := mul_apply_mul_twist
      (((Salt.TwinBar.chiSq : ArithmeticFunction ℤ) : ArithmeticFunction ℂ))
      (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ))
      (chiBarTwist_mul χ t) hn
  rw [← hcoe] at h
  simpa only [ArithmeticFunction.intCoe_apply] using h

/-! ## 3. The twisted summatory functions and the truncation transfer -/

/-- **The twisted Möbius summatory function** `M_{μχ̄}(y) = ∑_{n ≤ y} μ(n)·χ̄(n)n^{it}`,
ℂ-valued.  (The landed ℝ-valued `Salt.TwinBar.Mmu` is untouched.) -/
noncomputable def MmuChi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.moebius n : ℤ) : ℂ) * chiBarTwist χ t n

/-- **The twisted Liouville summatory function** `M_{λχ̄}(y) = ∑_{n ≤ y} λ(n)·χ̄(n)n^{it}`,
ℂ-valued.  (The landed ℝ-valued `Salt.TwinBar.Mlambda` is untouched.) -/
noncomputable def MlambdaChi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.liouville n : ℤ) : ℂ) * chiBarTwist χ t n

@[simp] theorem MmuChi_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    MmuChi χ t 0 = 0 := by
  simp [MmuChi]

/-- At the trivial character mod `1` and height `0` the twisted sums are the landed ones
(cast to ℂ) — the consistency check against `Salt/TwinBar/LambdaRate.lean`. -/
theorem MmuChi_one_zero (y : ℕ) :
    MmuChi (1 : DirichletCharacter ℂ 1) 0 y = ((Salt.TwinBar.Mmu y : ℝ) : ℂ) := by
  unfold MmuChi Salt.TwinBar.Mmu
  push_cast
  exact Finset.sum_congr rfl fun n _ => by rw [chiBarTwist_one_zero, mul_one]

/-- At the trivial character mod `1` and height `0` the twisted sums are the landed ones
(cast to ℂ) — the consistency check against `Salt/TwinBar/LambdaRate.lean`. -/
theorem MlambdaChi_one_zero (y : ℕ) :
    MlambdaChi (1 : DirichletCharacter ℂ 1) 0 y = ((Salt.TwinBar.Mlambda y : ℝ) : ℂ) := by
  unfold MlambdaChi Salt.TwinBar.Mlambda
  push_cast
  exact Finset.sum_congr rfl fun n _ => by rw [chiBarTwist_one_zero, mul_one]

/-- **The twisted pointwise identity in `d`-form**: for `1 ≤ n ≤ y`,
`λ(n)·w(n) = ∑_{d ≤ y, d² ∣ n} w(d²)·(μ(n/d²)·w(n/d²))` with `w = chiBarTwist χ t`.
The landed ℤ-valued `Salt.TwinBar.liouville_eq_sum_moebius` supplies the combinatorics; the
only new step is `w(n) = w(d²)·w(n/d²)`, i.e. complete multiplicativity at the factorization
`n = d²·(n/d²)`. -/
theorem liouville_twist_eq_sum_moebius_twist {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    {n y : ℕ} (hn1 : 1 ≤ n) (hny : n ≤ y) :
    ((ArithmeticFunction.liouville n : ℤ) : ℂ) * chiBarTwist χ t n
      = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ^ 2 ∣ n),
          chiBarTwist χ t (d ^ 2)
            * (((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℂ)
                * chiBarTwist χ t (n / d ^ 2)) := by
  have hn0 : n ≠ 0 := by omega
  have hC : ((ArithmeticFunction.liouville n : ℤ) : ℂ)
      = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ^ 2 ∣ n),
          ((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℂ) := by
    rw [Salt.TwinBar.liouville_eq_sum_moebius hn1 hny, Int.cast_sum]
  rw [hC, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_filter] at hd
  obtain ⟨_, hdvd⟩ := hd
  have hd0 : d ^ 2 ≠ 0 := by
    rintro h0
    rw [h0] at hdvd
    exact hn0 (Nat.eq_zero_of_zero_dvd hdvd)
  have hq0 : n / d ^ 2 ≠ 0 := by
    have hpos : 0 < d ^ 2 := Nat.pos_of_ne_zero hd0
    have h1 : 1 ≤ n / d ^ 2 := (Nat.one_le_div_iff hpos).mpr (Nat.le_of_dvd (by omega) hdvd)
    omega
  have hsplit : chiBarTwist χ t n = chiBarTwist χ t (d ^ 2) * chiBarTwist χ t (n / d ^ 2) := by
    rw [← chiBarTwist_mul χ t (d ^ 2) (n / d ^ 2) hd0 hq0, Nat.mul_div_cancel' hdvd]
  rw [hsplit]
  ring

/-- **The twisted inner multiples bijection**: `∑_{n ≤ y, d² ∣ n} μ(n/d²)·w(n/d²)
= M_{μχ̄}(⌊y/d²⌋)` — the twisted `Salt.TwinBar.Mmu_inner`, same `n = d²m` bijection. -/
theorem MmuChi_inner {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (y d : ℕ) (hd : 1 ≤ d) :
    ∑ n ∈ (Finset.Icc 1 y).filter (fun n => d ^ 2 ∣ n),
        (((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℂ) * chiBarTwist χ t (n / d ^ 2))
      = MmuChi χ t (y / d ^ 2) := by
  have hd2 : 0 < d ^ 2 := by positivity
  unfold MmuChi
  refine Finset.sum_bij' (fun n _ => n / d ^ 2) (fun m _ => d ^ 2 * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hny⟩, hdvd⟩ := hn
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hd2).mpr (Nat.le_of_dvd (by omega) hdvd),
           Nat.div_le_div_right hny⟩
  · intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmy⟩ := hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · exact Nat.mul_pos hd2 (by omega)
    · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd2).mp hmy
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _
    exact Nat.mul_div_cancel_left m hd2
  · intro n _
    rfl

/-- **The twisted hyperbola fold (UNCONDITIONAL)**:
`M_{λχ̄}(y) = ∑_{d ≤ √y} χ̄(d²)d^{2it}·M_{μχ̄}(⌊y/d²⌋)`.

The twisted `Salt.TwinBar.Mlambda_eq_sum_Mmu` (`LambdaRate.lean:298`).  The per-`d` factor
`w(d²) = χ̄(d²)·d^{2it}` is exactly what complete multiplicativity leaves behind, and it is
the ONLY difference from the untwisted identity; `‖w(d²)‖ ≤ 1` then makes the rate fold
character-blind. -/
theorem MlambdaChi_eq_sum_MmuChi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (y : ℕ) :
    MlambdaChi χ t y
      = ∑ d ∈ Finset.Icc 1 (Nat.sqrt y), chiBarTwist χ t (d ^ 2) * MmuChi χ t (y / d ^ 2) := by
  have hpt : ∀ n ∈ Finset.Icc 1 y,
      ((ArithmeticFunction.liouville n : ℤ) : ℂ) * chiBarTwist χ t n
        = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ^ 2 ∣ n),
            chiBarTwist χ t (d ^ 2)
              * (((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℂ)
                  * chiBarTwist χ t (n / d ^ 2)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact liouville_twist_eq_sum_moebius_twist χ t hn.1 hn.2
  unfold MlambdaChi
  rw [Finset.sum_congr rfl hpt]
  -- inner filter → `ite` over the ambient `Icc 1 y`
  have hstep1 : ∀ n : ℕ,
      ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ^ 2 ∣ n),
          chiBarTwist χ t (d ^ 2)
            * (((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℂ)
                * chiBarTwist χ t (n / d ^ 2))
        = ∑ d ∈ Finset.Icc 1 y,
            (if d ^ 2 ∣ n then
              chiBarTwist χ t (d ^ 2)
                * (((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℂ)
                    * chiBarTwist χ t (n / d ^ 2))
             else 0) := by
    intro n; rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun n _ => hstep1 n), Finset.sum_comm]
  -- inner `ite` → filter over `n`, pull `w(d²)` out, then collapse via `MmuChi_inner`
  have hstep2 : ∀ d ∈ Finset.Icc 1 y,
      ∑ n ∈ Finset.Icc 1 y,
          (if d ^ 2 ∣ n then
            chiBarTwist χ t (d ^ 2)
              * (((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℂ)
                  * chiBarTwist χ t (n / d ^ 2))
           else 0)
        = chiBarTwist χ t (d ^ 2) * MmuChi χ t (y / d ^ 2) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hpull : ∀ n : ℕ,
        (if d ^ 2 ∣ n then
          chiBarTwist χ t (d ^ 2)
            * (((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℂ)
                * chiBarTwist χ t (n / d ^ 2))
         else 0)
        = chiBarTwist χ t (d ^ 2)
            * (if d ^ 2 ∣ n then
                (((ArithmeticFunction.moebius (n / d ^ 2) : ℤ) : ℂ)
                  * chiBarTwist χ t (n / d ^ 2))
               else 0) := by
      intro n; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun n _ => hpull n), ← Finset.mul_sum, ← Finset.sum_filter,
      MmuChi_inner χ t y d hd.1]
  rw [Finset.sum_congr rfl hstep2]
  -- trim `Icc 1 y` down to `Icc 1 (√y)` (`d > √y ⇒ ⌊y/d²⌋ = 0 ⇒ M_{μχ̄} = 0`)
  refine (Finset.sum_subset ?_ ?_).symm
  · intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, le_trans hd.2 (Nat.sqrt_le_self y)⟩
  · intro d hd hd'
    rw [Finset.mem_Icc] at hd
    have hdgt : Nat.sqrt y < d := by
      by_contra h
      exact hd' (Finset.mem_Icc.mpr ⟨hd.1, Nat.not_lt.mp h⟩)
    have hlt : y < d ^ 2 := Nat.sqrt_lt'.mp hdgt
    rw [Nat.div_eq_of_lt hlt, MmuChi_zero, mul_zero]

/-- **Crude bound** `‖M_{μχ̄}(y)‖ ≤ y` — the twisted `Salt.TwinBar.Mmu_abs_le`
(`|μ| ≤ 1` and `‖w‖ ≤ 1`). -/
theorem norm_MmuChi_le {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (y : ℕ) :
    ‖MmuChi χ t y‖ ≤ (y : ℝ) := by
  unfold MmuChi
  calc ‖∑ n ∈ Finset.Icc 1 y, ((ArithmeticFunction.moebius n : ℤ) : ℂ) * chiBarTwist χ t n‖
      ≤ ∑ n ∈ Finset.Icc 1 y, ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * chiBarTwist χ t n‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 y, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul]
        have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
          have hcast : ((ArithmeticFunction.moebius n : ℤ) : ℂ)
              = (((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℂ) := by push_cast; ring
          rw [hcast, Complex.norm_real, Real.norm_eq_abs]
          calc |((ArithmeticFunction.moebius n : ℤ) : ℝ)|
              = ((|ArithmeticFunction.moebius n| : ℤ) : ℝ) := by rw [Int.cast_abs]
            _ ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
            _ = 1 := by norm_num
        have hw := norm_chiBarTwist_le_one χ t n
        calc ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ * ‖chiBarTwist χ t n‖
            ≤ 1 * 1 := by
              exact mul_le_mul hmu hw (norm_nonneg _) zero_le_one
          _ = 1 := by norm_num
    _ = (y : ℝ) := by rw [Finset.sum_const, Nat.card_Icc]; simp

/-! ## 4. The rate fold: `MmuChiRate ⇒ LambdaChiSummatory` -/

/-- **THE HONEST SLOT — the `χ,t`-twisted effective Möbius summatory rate.  NOT LANDED.**

`‖∑_{n ≤ y} μ(n)χ̄(n)n^{it}‖ ≤ C·y/(log y)^A` for every saving `A > 0`, **uniformly over
the height `t ∈ ℝ` and over the modulus range `q ≤ (log y)^12`** (the freeze's conductor
range; the gate is on the modulus, which is the weaker demand since `conductor χ ≤ q`).

This is the twisted twin of `Salt.TwinBar.MmuRate` (`LambdaRate.lean:58`).  The untwisted
`MmuRate` IS landed (`Salt.SW.mmuRate_holds`); **this `Prop` is not**, and is the port's
open centerpiece: it is exactly obligation **O4** (the `MobiusRateClose` re-run at `L(s,χ)`
instead of `ζ`) plus obligation **O5** (the `t`-aspect, i.e. the `χ`-VK / Landau–Page
region — the same stone as P-6's stone B, the campaign's isolated `D`-risk).  See
`docs/exploration/port-freeze-0729.md` §"What the refuters changed" item 3.  No part of it
is discharged in this file. -/
def MmuChiRate : Prop :=
  ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      (q : ℝ) ≤ (Real.log y) ^ (12 : ℕ) → ∀ t : ℝ,
        ‖MmuChi χ t y‖ ≤ C * y / (Real.log y) ^ A

/-- **The twisted Liouville summatory rate at a fixed saving `A`** — the twisted twin of
`Salt.TwinBar.LambdaSummatory` (`LambdaRate.lean:64`), at the conductor range
`q ≤ (log y)^11`: the fold spends one of `MmuChiRate`'s twelve exponents (see the file
header). -/
def LambdaChiSummatory (A : ℝ) : Prop :=
  ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      (q : ℝ) ≤ (Real.log y) ^ (11 : ℕ) → ∀ t : ℝ,
        ‖MlambdaChi χ t y‖ ≤ C * y / (Real.log y) ^ A

/-- `log y → ∞` along ℕ, in eventual form. -/
private lemma eventually_log_ge (c : ℝ) : ∀ᶠ y : ℕ in Filter.atTop, c ≤ Real.log y := by
  have h : Filter.Tendsto (fun y : ℕ => Real.log (y : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop c

/-- **THE RATE FOLD.**  From the twisted Möbius rate `MmuChiRate`, the twisted Liouville
summatory inherits the same power-log rate, uniformly in `t` and in `q ≤ (log y)^11`.

The proof is `Salt.TwinBar.Mlambda_rate`'s, with `|·|` replaced by `‖·‖` and the extra
per-`d` factor `w(d²)` absorbed by `‖w(d²)‖ ≤ 1`.  From the twisted identity
`M_{λχ̄}(y) = ∑_{d ≤ √y} w(d²)M_{μχ̄}(⌊y/d²⌋)`, split at `d ≤ √√y ≈ y^{1/4}`: on the small
range `log⌊y/d²⌋ ≥ log √y ≥ (log y)/4` and `∑ 1/d² ≤ 2`, giving `≤ 2C·4^A·y/(log y)^A`; on
the tail `‖M_{μχ̄}‖ ≤ ⌊y/d²⌋ ≤ y/d²` and `∑_{d>√√y} 1/d² ≤ 1/√√y ≤ 1/(log y)^A`, giving
`≤ y/(log y)^A`.  The conductor gate is the one new piece of bookkeeping: the μ-rate is
invoked at `⌊y/d²⌋`, so `q ≤ (log y)^11` must be upgraded to `q ≤ (log⌊y/d²⌋)^12`, which is
where `log y ≥ 4^12` is spent (an eventual threshold). -/
theorem MlambdaChi_rate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (11 : ℕ) → ∀ t : ℝ,
          ‖MlambdaChi χ t y‖ ≤ C * y / (Real.log y) ^ A := by
  obtain ⟨C, x₀mu, hCpos, hMmuBound⟩ := hMmu A hA
  have h4A : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have hC'pos : (0 : ℝ) < 2 * C * (4 : ℝ) ^ A + 1 := by
    have h := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hCpos) h4A
    linarith
  have key : ∀ᶠ y : ℕ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (11 : ℕ) → ∀ t : ℝ,
          ‖MlambdaChi χ t y‖ ≤ (2 * C * (4 : ℝ) ^ A + 1) * y / (Real.log y) ^ A := by
    filter_upwards [Salt.TwinBar.eventually_pow4_le A, Filter.eventually_ge_atTop 16,
        Filter.eventually_ge_atTop (x₀mu ^ 2),
        eventually_log_ge ((4 : ℝ) ^ (12 : ℕ))] with y hpow4 hy16 hyx0 hlog4
    intro q _ χ hq t
    have hLpos : 0 < Real.log y := lt_of_lt_of_le (by positivity) hlog4
    have hL0 : (0 : ℝ) ≤ Real.log y := hLpos.le
    have hs1 : 1 ≤ Nat.sqrt y := Nat.le_sqrt.mpr (by nlinarith [hy16])
    have hq_le_s : Nat.sqrt (Nat.sqrt y) ≤ Nat.sqrt y := Nat.sqrt_le_self _
    have hq1 : 1 ≤ Nat.sqrt (Nat.sqrt y) := Nat.le_sqrt.mpr (by nlinarith [hs1])
    have hs_ge_x0 : x₀mu ≤ Nat.sqrt y := by
      rw [Nat.le_sqrt]
      calc x₀mu * x₀mu = x₀mu ^ 2 := by ring
        _ ≤ y := hyx0
    have hlogs : Real.log y / 4 ≤ Real.log (Nat.sqrt y) := Salt.TwinBar.log_natSqrt_ge hy16
    -- `(log y)^A ≤ √√y`
    have hlogAq : (Real.log y) ^ A ≤ (Nat.sqrt (Nat.sqrt y) : ℝ) := by
      have hLA_le_K : (Real.log y) ^ A ≤ (Nat.ceil ((Real.log y) ^ A) : ℝ) := Nat.le_ceil _
      have hK_le : (Nat.ceil ((Real.log y) ^ A) : ℝ) ≤ (Real.log y) ^ A + 1 :=
        (Nat.ceil_lt_add_one (Real.rpow_nonneg hL0 A)).le
      have hK4 : Nat.ceil ((Real.log y) ^ A) ^ 4 ≤ y := by
        have hle : ((Nat.ceil ((Real.log y) ^ A) : ℝ)) ^ 4 ≤ (y : ℝ) :=
          le_trans (by gcongr) hpow4
        exact_mod_cast hle
      calc (Real.log y) ^ A ≤ (Nat.ceil ((Real.log y) ^ A) : ℝ) := hLA_le_K
        _ ≤ (Nat.sqrt (Nat.sqrt y) : ℝ) := by
              exact_mod_cast Salt.TwinBar.le_sqrt_sqrt_of_pow4_le hK4
    -- expand and split the `d`-sum
    have hbound : ‖MlambdaChi χ t y‖
        ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt y), ‖MmuChi χ t (y / d ^ 2)‖ := by
      rw [MlambdaChi_eq_sum_MmuChi]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun d _ => ?_)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_chiBarTwist_le_one χ t (d ^ 2))
    refine le_trans hbound ?_
    have hdisj : Disjoint (Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)))
        (Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_Icc] at ha
      rw [Finset.mem_Ioc] at hb
      omega
    have hIccsplit : Finset.Icc 1 (Nat.sqrt y)
        = Finset.Icc 1 (Nat.sqrt (Nat.sqrt y))
          ∪ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y) := by
      ext a; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
    rw [hIccsplit, Finset.sum_union hdisj]
    -- the small range: the twisted μ-rate, at the UPGRADED conductor gate
    have hsmall : ∑ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)), ‖MmuChi χ t (y / d ^ 2)‖
        ≤ 2 * C * (4 : ℝ) ^ A * y / (Real.log y) ^ A := by
      have key_d : ∀ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)),
          ‖MmuChi χ t (y / d ^ 2)‖
            ≤ C * (4 : ℝ) ^ A * y / (Real.log y) ^ A * ((d : ℝ) ^ 2)⁻¹ := by
        intro d hd
        rw [Finset.mem_Icc] at hd
        obtain ⟨hd1, hdq⟩ := hd
        have hd2s : d ^ 2 ≤ Nat.sqrt y :=
          le_trans (Nat.pow_le_pow_left hdq 2) (Nat.sqrt_le' (Nat.sqrt y))
        have hts : Nat.sqrt y ≤ y / d ^ 2 := by
          rw [Nat.le_div_iff_mul_le (show 0 < d ^ 2 by positivity)]
          calc Nat.sqrt y * d ^ 2 ≤ Nat.sqrt y * Nat.sqrt y := by gcongr
            _ ≤ y := Nat.sqrt_le y
        have htx : x₀mu ≤ y / d ^ 2 := le_trans hs_ge_x0 hts
        have hlogt : Real.log y / 4 ≤ Real.log ((y / d ^ 2 : ℕ) : ℝ) := by
          refine le_trans hlogs ?_
          apply Real.log_le_log (by exact_mod_cast (by omega : 0 < Nat.sqrt y))
          exact_mod_cast hts
        -- THE CONDUCTOR GATE UPGRADE: `q ≤ (log y)^11 ≤ (log y / 4)^12 ≤ (log⌊y/d²⌋)^12`
        have hgate : (q : ℝ) ≤ (Real.log ((y / d ^ 2 : ℕ) : ℝ)) ^ (12 : ℕ) := by
          have hratio : (1 : ℝ) ≤ Real.log y / (4 : ℝ) ^ (12 : ℕ) :=
            (one_le_div (by positivity)).mpr hlog4
          have h11 : (Real.log y) ^ (11 : ℕ) ≤ (Real.log y / 4) ^ (12 : ℕ) := by
            calc (Real.log y) ^ (11 : ℕ) = (Real.log y) ^ (11 : ℕ) * 1 := by ring
              _ ≤ (Real.log y) ^ (11 : ℕ) * (Real.log y / (4 : ℝ) ^ (12 : ℕ)) :=
                  mul_le_mul_of_nonneg_left hratio (pow_nonneg hL0 11)
              _ = (Real.log y / 4) ^ (12 : ℕ) := by
                  rw [div_pow]; ring
          have h12 : (Real.log y / 4) ^ (12 : ℕ)
              ≤ (Real.log ((y / d ^ 2 : ℕ) : ℝ)) ^ (12 : ℕ) := by
            have h04 : (0 : ℝ) ≤ Real.log y / 4 := by linarith
            gcongr
          linarith
        have hMt := hMmuBound (y / d ^ 2) htx q χ hgate t
        have hL4pos : 0 < Real.log y / 4 := by linarith
        have hrpow : (Real.log y / 4) ^ A ≤ (Real.log ((y / d ^ 2 : ℕ) : ℝ)) ^ A :=
          Real.rpow_le_rpow hL4pos.le hlogt hA.le
        calc ‖MmuChi χ t (y / d ^ 2)‖
            ≤ C * ((y / d ^ 2 : ℕ) : ℝ) / (Real.log ((y / d ^ 2 : ℕ) : ℝ)) ^ A := hMt
          _ ≤ C * ((y / d ^ 2 : ℕ) : ℝ) / (Real.log y / 4) ^ A :=
                div_le_div_of_nonneg_left (mul_nonneg hCpos.le (Nat.cast_nonneg _))
                  (Real.rpow_pos_of_pos hL4pos A) hrpow
          _ = C * ((y / d ^ 2 : ℕ) : ℝ) * (4 : ℝ) ^ A / (Real.log y) ^ A := by
                rw [Real.div_rpow hL0 (by norm_num), div_div_eq_mul_div]
          _ ≤ C * (4 : ℝ) ^ A * y / (Real.log y) ^ A * ((d : ℝ) ^ 2)⁻¹ := by
                have hcast : ((y / d ^ 2 : ℕ) : ℝ) ≤ (y : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
                  have h := Nat.cast_div_le (m := y) (n := d ^ 2) (α := ℝ)
                  rwa [Nat.cast_pow, div_eq_mul_inv] at h
                have hCoef : (0 : ℝ) ≤ C * (4 : ℝ) ^ A / (Real.log y) ^ A :=
                  div_nonneg (mul_nonneg hCpos.le (Real.rpow_nonneg (by norm_num) A))
                    (Real.rpow_nonneg hL0 A)
                calc C * ((y / d ^ 2 : ℕ) : ℝ) * (4 : ℝ) ^ A / (Real.log y) ^ A
                    = (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * ((y / d ^ 2 : ℕ) : ℝ) := by ring
                  _ ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * ((y : ℝ) * ((d : ℝ) ^ 2)⁻¹) :=
                        mul_le_mul_of_nonneg_left hcast hCoef
                  _ = C * (4 : ℝ) ^ A * y / (Real.log y) ^ A * ((d : ℝ) ^ 2)⁻¹ := by ring
      calc ∑ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)), ‖MmuChi χ t (y / d ^ 2)‖
          ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)),
              C * (4 : ℝ) ^ A * y / (Real.log y) ^ A * ((d : ℝ) ^ 2)⁻¹ :=
            Finset.sum_le_sum key_d
        _ = (C * (4 : ℝ) ^ A * y / (Real.log y) ^ A) *
              ∑ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)), ((d : ℝ) ^ 2)⁻¹ := by
              rw [Finset.mul_sum]
        _ ≤ (C * (4 : ℝ) ^ A * y / (Real.log y) ^ A) * 2 :=
              mul_le_mul_of_nonneg_left (Salt.TwinBar.sum_inv_sq_Icc_le _)
                (div_nonneg (mul_nonneg (mul_nonneg hCpos.le h4A.le) (Nat.cast_nonneg _))
                  (Real.rpow_nonneg hL0 A))
        _ = 2 * C * (4 : ℝ) ^ A * y / (Real.log y) ^ A := by ring
    -- the tail: the crude bound only (no character input)
    have hlarge : ∑ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y),
        ‖MmuChi χ t (y / d ^ 2)‖ ≤ (y : ℝ) / (Real.log y) ^ A := by
      have hbd : ∀ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y),
          ‖MmuChi χ t (y / d ^ 2)‖ ≤ (y : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
        intro d _
        calc ‖MmuChi χ t (y / d ^ 2)‖ ≤ ((y / d ^ 2 : ℕ) : ℝ) := norm_MmuChi_le _ _ _
          _ ≤ (y : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
                have h := Nat.cast_div_le (m := y) (n := d ^ 2) (α := ℝ)
                rwa [Nat.cast_pow, div_eq_mul_inv] at h
      calc ∑ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y), ‖MmuChi χ t (y / d ^ 2)‖
          ≤ ∑ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y),
              (y : ℝ) * ((d : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum hbd
        _ = (y : ℝ) * ∑ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y),
              ((d : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
        _ ≤ (y : ℝ) * (Nat.sqrt (Nat.sqrt y) : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_left (Salt.TwinBar.sum_inv_sq_Ioc_le hq1 hq_le_s)
                (Nat.cast_nonneg _)
        _ ≤ (y : ℝ) / (Real.log y) ^ A := by
              rw [div_eq_mul_inv]
              have hLA : (0 : ℝ) < (Real.log y) ^ A := Real.rpow_pos_of_pos hLpos A
              have hinv : (Nat.sqrt (Nat.sqrt y) : ℝ)⁻¹ ≤ ((Real.log y) ^ A)⁻¹ := by
                gcongr
              exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
    calc ∑ d ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt y)), ‖MmuChi χ t (y / d ^ 2)‖
          + ∑ d ∈ Finset.Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y), ‖MmuChi χ t (y / d ^ 2)‖
        ≤ 2 * C * (4 : ℝ) ^ A * y / (Real.log y) ^ A + (y : ℝ) / (Real.log y) ^ A :=
          add_le_add hsmall hlarge
      _ = (2 * C * (4 : ℝ) ^ A + 1) * y / (Real.log y) ^ A := by ring
  rw [Filter.eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  exact ⟨2 * C * (4 : ℝ) ^ A + 1, N, hC'pos, hN⟩

/-- **⟦O3⟧ THE DELIVERABLE — the twisted `μ → λ` bridge.**  The twisted `λχ̄ n^{it}` window
rate at every saving `A > 0`, CONDITIONAL on the twisted μ-rate slot `MmuChiRate`.

The twisted twin of `Salt.TwinBar.LambdaSummatory_of_MmuRate` (`LambdaRate.lean:577`).
Everything in the *bridge* is unconditional; the hypothesis `MmuChiRate` is **not landed**
and is exactly the port's obligations **O4** (the `MobiusRateClose` re-run at `L(s,χ)`) and
**O5** (the `t`-aspect / `χ`-VK region) — see `MmuChiRate`'s docstring and
`docs/exploration/port-freeze-0729.md`. -/
theorem LambdaChiSummatory_of_MmuChiRate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    LambdaChiSummatory A :=
  MlambdaChi_rate hMmu A hA

end Salt.MR
