/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.BaseCase
import Salt.Vmvt.Linnik
import Salt.Vmvt.Shifted

/-!
# Theorem 24.5 — the Vinogradov Mean Value Theorem (Linnik–Karatsuba induction)

This file is the centerpiece of the VMVT campaign: the explicit form of the
Vinogradov Mean Value Theorem (Vaughan PSU Chapter 24, **Theorem 24.5**),
proved — over multiple sessions — by the elementary Linnik–Karatsuba p-adic
induction on `r`.

## The target statement (source Theorem 24.5)

> There is a positive number `C` such that when `k ≥ 2`, `r` is a positive
> integer and `x ≥ 1`,
> `J_k(x, kr) ≤ D(k,r) · x^{2rk − ½k(k+1) + η(k,r)}`,
> `D(k,r) = exp(C·r·k²·log k)`,  `η(k,r) = ½k²(1 − 1/k)^r`.

We port it in the **consumer's form** on the interval object `JkI` and — as the
task authorises ("`D` as any closed form that the induction produces … constants
utterly free, track honestly") — we take the algebraic closed form

* `η(k,r) = vmvtEta k r  = ½·k²·(1 − 1/k)^r`   (**the exponent is load-bearing;
  it matches the source EXACTLY**),
* `E(k,r) = vmvtExp k r  = 2rk − ½k(k+1) + η(k,r)`,
* `D(k,r) = vmvtConst k r = (C₀ k)^r` with `C₀ k = k⁶·k!·2^{k²}·3`.

`C₀ k` is the per-step constant the induction produces (see the D-recursion
below); it is `r`-independent, so `D(k,r) = (C₀ k)^r`, and `3 > e` absorbs the
`(1+tiny)^{E} ≤ e` slack of the large-`x` regime. The whole bound is packaged as
the predicate `VmvtBound k r x`.

## The proof skeleton (from the source — the recollection-guide)

Induction on `r`, `k` fixed.

* **Base `r = 1`.** The exponent is exactly `k` (verified: `vmvtExp_one`), and
  `J_k(x,k) ≤ k!·x^k` is the landed base case `JkI_le` (Lemma 24.3(a)).  Landed
  here as `vmvt_base`.
* **Step `r → r`, `r ≥ 2`.** Two regimes.
  - *Small `x`* (`x ≤ exp(C·max(k,r)·log k)`): the trivial estimate
    `J_k(x,kr) ≤ x^{2kr}` already gives the bound because
    `½k(k+1) − η(k,r) ≤ min(k², rk)` (source (3.1) discussion).
  - *Large `x`* (`x > exp(C·max(k,r)·log k)`): the p-adic argument.
    1. `y := x^{1/k}`; choose the least `z` with `#{p prime : y < p ≤ y+z} =
       ½k(k²−1)` (= Θ(k³); NB the source OCR "½k(k−1)" is missing a factor of
       `k` — the pigeonhole below needs the count to *exceed* the bad-prime
       bound `½k²(k−1)`).  By PNT `z ≤ y`, so every chosen `p ∈ (x^{1/k},
       2x^{1/k}]`.
    2. **Transversality split.** `J_k = ∑_h R(h)²` with `R = R₁ + R₂`, `R₁`/`R₂`
       counting the tuples whose first `k` coordinates are distinct / not
       distinct.  `J_k ≤ 2(S₁+S₂)`, `Sᵢ = ∑ Rᵢ²`.  The degenerate `S₂`-case
       collapses two variables and is dominated by a Hölder-on-counts step
       (the `Ncount_union_le` machinery); the transversal `S₁`-case is the main
       term.  A solution counted by `R₁` has `P(m) = ∏_{i<j≤k}(mᵢ−mⱼ)` with
       `0 < |P(m)| < x^{½k(k−1)} = y^{½k²(k−1)}`, so at most `½k²(k−1)` primes
       `p > y` divide it; since the range holds `½k(k²−1) > ½k²(k−1)` primes,
       **some** chosen `p ∤ P(m)` — the `m_q` are then distinct mod `p`.  Hence
       `R₁(h) ≤ ∑_{p} R₄(h,p)`.
    3. **The transversal count via Linnik.**  `I(p) := ∑_h R₄(h,p)² ≤
       p^{2rk−2k}·max_a I₁(p,a)`, and `I₁(p,a) ≤ card B(p,a)·J_k(⟨a/p,(x−a)/p⟩,
       (r−1)k)`.  `B(p,a)` is a p-adic residue count: by **`linnik_lemma`**
       (range→`ZMod p^k` bridge) `card B(p,a) ≤ x^k·k!·p^{k(k−1)/2}`.  The
       remaining `(r−1)k` variables live in an affine box → `Jk_image_affine`
       + the inductive hypothesis on `JkI` at scale `x/p`.
    4. **Assembly.**  Collecting exponents (see the arithmetic below) gives the
       recursion, which the closed forms satisfy on the nose.

## The recursion arithmetic (worked on paper, VALIDATED in Lean below)

Substituting `p = θ·x^{1/k}`, `θ ∈ (1,2]`, and the IH at scale `x/p`, the total
`x`-exponent produced by one step is

  `k` (the `x^k` Linnik `m`-freedom)
  `+ (2rk−2k)/k = 2r−2`  (the `p^{2rk−2k}` Hölder factor)
  `+ ½k(k−1)/k = ½(k−1)`  (the `p^{k(k−1)/2}` Linnik residue count)
  `+ (1−1/k)·E(k,r−1)`   (the `(x/p)^{E(k,r−1)}` inductive box),

whose sum is `3/2·k + 2r − 5/2 + (1−1/k)·E(k,r−1)`.  Using the **η-recursion**
`η(k,r) = (1−1/k)·η(k,r−1)` one checks this equals `E(k,r)` exactly:

  **`vmvtExp_succ`  :  E(k,r+1) = 3/2·k + 2(r+1) − 5/2 + (1−1/k)·E(k,r)`**.

The net residual **prime power** is
`B = (2rk−2k) + ½k(k−1) − E(k,r−1) = k² − η(k,r−1) ∈ [½k², k²]`,
so the leftover constant `θ^B ≤ 2^B ≤ 2^{k²}`.  Together with `k⁶·k!` (the
`k⁶ = (k²·binom)²`-grade combinatorial losses and the `card B` factorial) and
the `(1+tiny)^{E} ≤ e < 3` regime factor, the **D-recursion** is

  `D(k,r) ≤ C₀(k)·D(k,r−1)`,   `C₀(k) = k⁶·k!·2^{k²}·3`,

which the closed form `D(k,r) = (C₀ k)^r` satisfies with equality
(`vmvtConst_succ`).

## Status / resume map (updated per rung)

* **R1 — DONE (this session).**  Statement (`VmvtBound`), the closed forms
  (`vmvtEta`/`vmvtExp`/`vmvtConst`/`vmvtC0`), the validated recursion arithmetic
  (`vmvtEta_succ`, `vmvtExp_one`, `vmvtExp_succ`, `vmvtConst_succ`), and the base
  case `vmvt_base : VmvtBound k 1 x`.  All sorry-free, axioms clean.
* **R2 — NEXT.**  Two halves.
  - *Prime selection (PNT-dependent — the named obstruction).*  Need
    `½k(k²−1) = Θ(k³)` primes in `(y, 2y]`, `y = x^{1/k}`.  Bertrand
    (`Nat.exists_prime_lt_and_le_two_mul`) gives only **one** prime per dyadic
    block, not Θ(k³); the real requirement is a Chebyshev lower bound
    `π(2y) − π(y) ≥ ½k(k²−1)`, to be wired from the corpus
    (`Salt/Chen/MertensPNT`, `Salt/BrunLower` prime-in-interval counts) — valid
    once `y ≳ k³·log k`, i.e. in the large-`x` regime.  `p > k` is free from
    `p > y ≥ k`.
  - *Transversality covering (PNT-free — landable now).*  Given a prime set `P`
    with the pigeonhole property, `R₁(h) ≤ ∑_{p∈P} R₄(h,p)` is a pure union
    bound (mirror of `rcount_biUnion_le`).  Needs the counting objects
    `R₁`/`R₄` (distinct-mod-`p` on the first `k` of the `kr` coordinates) atop
    the `sig`/`rcount` frame of `Shifted.lean`.  The degenerate `S₂` collapse
    via `Ncount_union_le`; **CAUTION** the `S₂ ≥ S₁` sub-case needs a genuine
    *Hölder-on-counts* (self-improving `J ≤ 4k⁴·J^{1−1/(kr)}`) that is **not**
    in the toolkit — a second named gap.
* **R3.**  The transversal count: the range→`ZMod p^k` bridge feeding
  `linnik_lemma`, giving `card B(p,a) ≤ x^k·k!·p^{k(k−1)/2}`; the affine box via
  `Jk_image_affine` at scale `x/p`.
* **R4.**  The one-step recursion inequality `VmvtBound k (r−1) · → VmvtBound k r`
  (large-`x`), assembled on the validated exponent arithmetic; the small-`x`
  trivial branch.
* **R5.**  The unwound closed form: strong induction on `r` off `vmvt_base` +
  R4, delivering the full `∃ C, …` Theorem 24.5.
-/

namespace Salt.Vmvt

open Finset

/-! ## The closed forms (η, exponent, constant) -/

/-- `η(k,r) = ½·k²·(1 − 1/k)^r` — the source's exponent decay term. -/
noncomputable def vmvtEta (k r : ℕ) : ℝ := (1 / 2) * (k : ℝ) ^ 2 * (1 - 1 / (k : ℝ)) ^ r

/-- The load-bearing exponent `E(k,r) = 2rk − ½k(k+1) + η(k,r)` of Theorem 24.5.
This matches the source EXACTLY (the exponent is what makes VMVT nontrivial). -/
noncomputable def vmvtExp (k r : ℕ) : ℝ :=
  2 * (r : ℝ) * (k : ℝ) - (1 / 2) * (k : ℝ) * ((k : ℝ) + 1) + vmvtEta k r

/-- The per-step constant `C₀(k) = k^{24k²}` the induction produces (`r`-independent).

**Re-grade (2026-07-18 house authorization; VMVT-R5b, then VMVT-SUMMIT-2).**
Source-faithful free constant: Vaughan PSU Theorem 24.5's `D(k,r) = exp(C·r·k²·log k)`
has `C` FREE, so `C₀(k)` is unconstrained (only the exponent `E(k,r)` is
load-bearing).  The original value `k⁶·k!·2^{k²}·3` was exp-grade too small for the
medium-`x` regime — the trivial small-`x` bound could not reach the prime-pigeonhole
threshold (R4/R5b flags, `docs/blueprints/flags.md`).  The R5b re-grade `k^{8k²}`
still could not bridge to the effective prime supply; the SUMMIT-2 re-grade to
`k^{24k²} = exp(24k²·log k)` (SECOND authorized statement change, same source
free-constant justification, `C` still free) makes the two-arm bridge
`Xmed = k^{24·max(k,r)} ≥ Y'(k)^k` clear at `k ≥ 2` (both the `y₁ ≤ 2¹⁴` supply arm
and the `64(k³+1)²` pigeonhole arm; see `Summit2.lean`).  The old value survives as a
lower bound through `old_c0_le`, so every landed proof that consumed it re-closes
through the bridge. -/
noncomputable def vmvtC0 (k : ℕ) : ℝ := (k : ℝ) ^ (24 * k ^ 2)

/-- The constant `D(k,r) = (C₀ k)^r`.  A closed form the induction produces;
`D` is unconstrained by the source (only `E` is load-bearing). -/
noncomputable def vmvtConst (k r : ℕ) : ℝ := (vmvtC0 k) ^ r

/-- **The mean-value bound predicate.**  `VmvtBound k r x` is the conclusion of
Theorem 24.5 in the consumer's interval form:
`J_k(x, kr) ≤ D(k,r)·x^{E(k,r)}` (with `^` the real power `Real.rpow`). -/
def VmvtBound (k r x : ℕ) : Prop :=
  (JkI k (k * r) x : ℝ) ≤ vmvtConst k r * (x : ℝ) ^ (vmvtExp k r)

/-! ## The recursion arithmetic (paper derivation, validated by the kernel) -/

/-- **η-recursion.**  `η(k,r+1) = (1 − 1/k)·η(k,r)`.  Holds for every `k` (it is
just `pow_succ` on `(1−1/k)^r`). -/
theorem vmvtEta_succ (k r : ℕ) : vmvtEta k (r + 1) = (1 - 1 / (k : ℝ)) * vmvtEta k r := by
  unfold vmvtEta
  rw [pow_succ]
  ring

/-- **Base exponent check.**  `E(k,1) = k` (needs `k ≠ 0` to cancel `1/k`).  This
is the numerical heart of the base case: the `r = 1` exponent collapses to `k`,
matching Lemma 24.3(a)'s `J_k(x,k) ≤ k!·x^k`. -/
theorem vmvtExp_one (k : ℕ) (hk : (k : ℝ) ≠ 0) : vmvtExp k 1 = (k : ℝ) := by
  unfold vmvtExp vmvtEta
  rw [pow_one]
  field_simp
  ring

/-- **The exponent recursion (load-bearing).**  `E(k,r+1) = 3/2·k + 2(r+1) − 5/2
+ (1 − 1/k)·E(k,r)`.  Every term on the right is exactly the `x`-exponent that
one Linnik–Karatsuba step contributes (file header).  Proving it in the kernel
rigorously validates the hand arithmetic of the assembly. -/
theorem vmvtExp_succ (k r : ℕ) (hk : (k : ℝ) ≠ 0) :
    vmvtExp k (r + 1) =
      3 / 2 * (k : ℝ) + 2 * ((r : ℝ) + 1) - 5 / 2 + (1 - 1 / (k : ℝ)) * vmvtExp k r := by
  unfold vmvtExp
  rw [vmvtEta_succ]
  push_cast
  -- treat the opaque power `(1 − 1/k)^r` inside `vmvtEta` as an atom
  unfold vmvtEta
  field_simp
  ring

/-- **The D-recursion.**  `D(k,r+1) = C₀(k)·D(k,r)` — exact, since
`D(k,r) = (C₀ k)^r`.  The induction only needs `D(k,r+1) ≥ C₀(k)·D(k,r)`; the
closed form gives equality. -/
theorem vmvtConst_succ (k r : ℕ) : vmvtConst k (r + 1) = vmvtC0 k * vmvtConst k r := by
  unfold vmvtConst
  rw [pow_succ]
  ring

/-- **The re-grade bridge (VMVT-R5b / SUMMIT-2).**  The former per-step constant
`k⁶·k!·2^{k²}·3` sits below the re-graded `vmvtC0 k = k^{24k²}` for `k ≥ 2`.  Proof:
`k! ≤ k^k`, `2^{k²} ≤ k^{k²}`, `3 ≤ k²`, so the product is `≤ k^{6+k+k²+2} ≤ k^{24k²}`
(exponents: `k²+k+8 ≤ 24k²` for `k ≥ 2`).  Every landed proof that consumed the old
value re-closes THROUGH this bridge (its type `… ≤ vmvtC0 k` is re-grade-stable). -/
theorem old_c0_le {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) ^ 6 * (k.factorial : ℝ) * (2 : ℝ) ^ (k ^ 2) * 3 ≤ vmvtC0 k := by
  have hnat : k ^ 6 * k.factorial * 2 ^ (k ^ 2) * 3 ≤ k ^ (24 * k ^ 2) := by
    have hf : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
    have h2 : 2 ^ (k ^ 2) ≤ k ^ (k ^ 2) := Nat.pow_le_pow_left hk (k ^ 2)
    have h3 : 3 ≤ k ^ 2 := by nlinarith [hk]
    have step : k ^ 6 * k.factorial * 2 ^ (k ^ 2) * 3 ≤ k ^ 6 * k ^ k * k ^ (k ^ 2) * k ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) hf) h2) h3
    calc k ^ 6 * k.factorial * 2 ^ (k ^ 2) * 3
        ≤ k ^ 6 * k ^ k * k ^ (k ^ 2) * k ^ 2 := step
      _ = k ^ (6 + k + k ^ 2 + 2) := by rw [← pow_add, ← pow_add, ← pow_add]
      _ ≤ k ^ (24 * k ^ 2) := Nat.pow_le_pow_right (by omega) (by nlinarith [hk])
  calc (k : ℝ) ^ 6 * (k.factorial : ℝ) * (2 : ℝ) ^ (k ^ 2) * 3
      = ((k ^ 6 * k.factorial * 2 ^ (k ^ 2) * 3 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((k ^ (24 * k ^ 2) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = vmvtC0 k := by rw [vmvtC0]; push_cast; ring

/-! ## The base case `r = 1` (Lemma 24.3(a)) -/

/-- `k! ≤ D(k,1) = C₀(k) = k⁶·k!·2^{k²}·3`.  The factorial sits under the whole
per-step constant — trivially, since the cofactor `k⁶·2^{k²}·3 ≥ 1`. -/
theorem factorial_le_vmvtConst_one {k : ℕ} (hk : 2 ≤ k) :
    (k.factorial : ℝ) ≤ vmvtConst k 1 := by
  unfold vmvtConst
  rw [pow_one]
  have hbridge := old_c0_le hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hp6 : (1 : ℝ) ≤ (k : ℝ) ^ 6 := one_le_pow₀ hk1
  have hp2 : (1 : ℝ) ≤ (2 : ℝ) ^ (k ^ 2) := one_le_pow₀ (by norm_num)
  have hfac0 : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hcof : (k.factorial : ℝ)
      ≤ (k : ℝ) ^ 6 * (k.factorial : ℝ) * (2 : ℝ) ^ (k ^ 2) * 3 := by
    nlinarith [hp6, hp2, hfac0, mul_nonneg hfac0 (le_trans zero_le_one hp2),
      mul_nonneg (mul_nonneg hfac0 (le_trans zero_le_one hp6)) (le_trans zero_le_one hp2)]
  linarith [hcof, hbridge]

/-- **Theorem 24.5, base case `r = 1`.**  `VmvtBound k 1 x`, i.e.
`J_k(x, k) ≤ D(k,1)·x^{E(k,1)}`.  Since `E(k,1) = k` (`vmvtExp_one`) this is the
landed `J_k(x,k) ≤ k!·x^k` (`JkI_le`, Lemma 24.3(a)) with `k! ≤ D(k,1)`. -/
theorem vmvt_base {k x : ℕ} (hk : 2 ≤ k) (_hx : 1 ≤ x) : VmvtBound k 1 x := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold VmvtBound
  rw [mul_one, vmvtExp_one k hk0, Real.rpow_natCast]
  -- ℕ base bound, cast to ℝ
  have hcast : (JkI k k x : ℝ) ≤ (k.factorial : ℝ) * (x : ℝ) ^ k := by
    exact_mod_cast JkI_le (k := k) (b := k) x (le_refl k)
  refine hcast.trans ?_
  have hxk : (0 : ℝ) ≤ (x : ℝ) ^ k := by positivity
  exact mul_le_mul_of_nonneg_right (factorial_le_vmvtConst_one hk) hxk

end Salt.Vmvt
