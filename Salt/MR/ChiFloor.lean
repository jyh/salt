/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DistHalasz
import Salt.MR.PretentiousTriangle
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# ROUTE A leg H1 — the `k`-th-power pretentious floor for the `λ·χ̄` datum (`ChiFloor`)

The stone that retires stone 9's last `D`-risk (`docs/exploration/chi-check-0724.md`, the
"BIGGER FINDING"): the quality arm needs NO `χ`-power region on the extreme-`t` range
`|t| ≥ 1/(2·ord χ)`.  Taking `k = 2·ord(χ)` (even), the `k`-th power of the `λ·χ̄` datum is
the PRINCIPAL character `χ₀` (`λ(p)^k = 1`; `χ̄(p)^k = χ₀(p)`, exact at `p | q` too), and the
`k`-fold power inequality transfers the ALREADY-LANDED `ζ`-side floor `dist_one_floor_pow`
(`DistHalasz.lean:179`, no upper cap on `|b|`) back down at the cost of a `1/k²` factor and the
`p | q` deficit `∑_{p | q, p ≤ X} 1/p`.

## Contents

* `one_sub_re_pow_le` (C1 core) — the PER-PRIME power inequality `1 − Re(z^k) ≤ k²(1 − Re z)`
  for `‖z‖ ≤ 1`, proved ALGEBRAICALLY (no polar form): `2(1 − Re w) = ‖1 − w‖² + 1 − ‖w‖²`,
  then `‖1 − z^k‖ ≤ k‖1 − z‖` and `1 − ‖z‖^{2k} ≤ k(1 − ‖z‖²)`.
* `pretDistSq_pow_le` (C1) — `𝔻(f^k, g^k; x)² ≤ k²·𝔻(f, g; x)²` at full 1-bounded generality,
  and `pretDist_pow_le` — its square-root form `𝔻(f^k, g^k; x) ≤ k·𝔻(f, g; x)`.
* `lamChi`, `chiPrin`, `lamChi_pow` (C2) — the `λ·χ̄` datum, the principal datum, and the
  character-power identity `(λ·χ̄)^k = χ₀` for `k` even with `χ^k = 1`; plus the EXACT twist
  transfer `pretDistSq_chi_twist` / `pretDistSq_lam_chi_twist`
  (`𝔻(λ, χ·n^{it}; X)² = 𝔻(λ·χ̄, n^{it}; X)²`) that connects the MRT quality shape to it.
* `primeDivSum`, `pretDistSq_chiPrin_ge` (C3) — the `p | q` correction, with the HONEST
  constant `1` (not `2`): the per-prime defect is exactly `cos(b·log p)/p ≥ −1/p`.
* `chi_floor_of_order`, `chi_floor_of_order_div` (C4) — the H1 exit, and
  `chi_floor_orderOf` / `chi_floor_orderOf_twisted` — its `k := 2·orderOf χ` instantiation,
  in the `λ·χ̄` and in the MRT `𝔻(λ, χ·n^{it})` shape.

## The sqrt-vs-sq resolution (RECORDED)

The landed triangle `pretDist_triangle` (`PretentiousTriangle.lean:172`) is on the SQRT form
`pretDist = √pretDistSq`, and iterating it `k` times does NOT give the clean `k·𝔻` bound: the
step `𝔻(f^{j+1}, g^{j+1}) ≤ 𝔻(f^{j+1}, f^j g) + 𝔻(f^j g, g^{j+1})` leaves the factors
`‖f‖^{2j}`, `‖g‖^{2j}` glued to the two `Re`s, and for `‖f‖ < 1` those factors run the WRONG
way (`(1 − ‖f‖^{2j})·Re ≤ 0` needs `Re ≤ 0`).  The `λ·χ̄` datum is exactly of that kind — it
VANISHES at `p | q`.  So this file does not iterate the triangle at all: the `k`-fold bound is
proved directly on `pretDistSq`, TERMWISE, from the algebraic pointwise inequality
`1 − Re(z^k) ≤ k²(1 − Re z)` (which is sharp in `k`: `z = e^{iθ}`, `θ → 0`).  The square-root
corollary `pretDist_pow_le` is then free.  `pretDist_triangle` is not consumed.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## C1 — the `k`-fold power inequality (termwise, on `pretDistSq`) -/

/-- Real geometric step: `1 − s^k ≤ k(1 − s)` for `s ∈ [0,1]`. -/
private lemma one_sub_pow_le_mul {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (k : ℕ) :
    1 - s ^ k ≤ (k : ℝ) * (1 - s) := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hsm : s ^ m ≤ 1 := pow_le_one₀ h0 h1
    have hstep : (1 : ℝ) - s ^ (m + 1) = (1 - s ^ m) + s ^ m * (1 - s) := by ring
    have hmul : s ^ m * (1 - s) ≤ 1 * (1 - s) :=
      mul_le_mul_of_nonneg_right hsm (by linarith)
    rw [hstep]
    push_cast
    linarith [ih, hmul]

/-- Complex geometric step: `‖1 − z^k‖ ≤ k‖1 − z‖` for `‖z‖ ≤ 1`. -/
private lemma norm_one_sub_pow_le {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℕ) :
    ‖1 - z ^ k‖ ≤ (k : ℝ) * ‖1 - z‖ := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hstep : (1 : ℂ) - z ^ (m + 1) = (1 - z ^ m) + z ^ m * (1 - z) := by ring
    have h1 : ‖(1 - z ^ m) + z ^ m * (1 - z)‖ ≤ ‖1 - z ^ m‖ + ‖z ^ m * (1 - z)‖ :=
      norm_add_le _ _
    have h2 : ‖z ^ m * (1 - z)‖ ≤ ‖1 - z‖ := by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg z) hz)
    rw [hstep]
    push_cast
    linarith [ih, h1, h2]

/-- **C1 core — the per-prime power inequality.**  For `‖z‖ ≤ 1` and any `k`,
`1 − Re(z^k) ≤ k²·(1 − Re z)`.

Purely algebraic (no polar decomposition): with the identity
`2(1 − Re w) = ‖1 − w‖² + (1 − ‖w‖²)`, the claim splits into the two geometric estimates
`‖1 − z^k‖ ≤ k‖1 − z‖` and `1 − (‖z‖²)^k ≤ k(1 − ‖z‖²) ≤ k²(1 − ‖z‖²)`. -/
theorem one_sub_re_pow_le {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℕ) :
    1 - (z ^ k).re ≤ (k : ℝ) ^ 2 * (1 - z.re) := by
  have hid : ∀ w : ℂ, ‖1 - w‖ ^ 2 = 1 - 2 * w.re + ‖w‖ ^ 2 := by
    intro w
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hr0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hr2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith
  have hA0 : (0 : ℝ) ≤ ‖1 - z‖ := norm_nonneg _
  have hB0 : (0 : ℝ) ≤ ‖1 - z ^ k‖ := norm_nonneg _
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith
  have hnk : ‖1 - z ^ k‖ ≤ (k : ℝ) * ‖1 - z‖ := norm_one_sub_pow_le hz k
  have hzk2 : ‖z ^ k‖ ^ 2 = (‖z‖ ^ 2) ^ k := by
    rw [norm_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hs : 1 - (‖z‖ ^ 2) ^ k ≤ (k : ℝ) * (1 - ‖z‖ ^ 2) :=
    one_sub_pow_le_mul (by positivity) hr2 k
  have hs' : 1 - (‖z‖ ^ 2) ^ k ≤ (k : ℝ) ^ 2 * (1 - ‖z‖ ^ 2) := by
    nlinarith [hs, mul_nonneg (sub_nonneg.mpr hkk) (sub_nonneg.mpr hr2)]
  have hB2 : ‖1 - z ^ k‖ ^ 2 ≤ (k : ℝ) ^ 2 * ‖1 - z‖ ^ 2 := by
    nlinarith [hnk, hB0, hA0, hk0, mul_nonneg hk0 hA0]
  have h1 := hid z
  have h2 := hid (z ^ k)
  rw [hzk2] at h2
  -- clear the two `Re`s FIRST (`linarith` cannot multiply `h1` by the `k²` in the goal)
  have hgoal : 2 * (1 - (z ^ k).re) ≤ (k : ℝ) ^ 2 * (2 * (1 - z.re)) := by
    have e1 : 2 * (1 - (z ^ k).re) = 1 - (‖z‖ ^ 2) ^ k + ‖1 - z ^ k‖ ^ 2 := by linarith [h2]
    have e2 : 2 * (1 - z.re) = 1 - ‖z‖ ^ 2 + ‖1 - z‖ ^ 2 := by linarith [h1]
    rw [e1, e2]
    linarith [hs', hB2]
  linarith [hgoal]

/-- **C1 — the `k`-fold power inequality on `pretDistSq`.**  For 1-bounded `f g : ℕ → ℂ`,
`𝔻(f^k, g^k; x)² ≤ k²·𝔻(f, g; x)²`.

Termwise from `one_sub_re_pow_le` at `z = f(p)·conj g(p)`, using
`f(p)^k·conj(g(p)^k) = (f(p)·conj g(p))^k`.  NOTE this does not iterate the landed
`pretDist_triangle` — see the file header for why iteration fails for data that vanish
somewhere (which `λ·χ̄` does, at `p | q`). -/
theorem pretDistSq_pow_le (f g : ℕ → ℂ) (x : ℝ) (k : ℕ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) :
    pretDistSq (fun n => f n ^ k) (fun n => g n ^ k) x
      ≤ (k : ℝ) ^ 2 * pretDistSq f g x := by
  unfold pretDistSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_filter] at hp
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
  have hzb : ‖f p * (starRingEnd ℂ) (g p)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (hf p) (norm_nonneg _) (hg p)
  have hcomb : f p ^ k * (starRingEnd ℂ) (g p ^ k)
      = (f p * (starRingEnd ℂ) (g p)) ^ k := by
    rw [map_pow, mul_pow]
  change (1 - (f p ^ k * (starRingEnd ℂ) (g p ^ k)).re) / (p : ℝ)
      ≤ (k : ℝ) ^ 2 * ((1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ))
  rw [hcomb]
  have hkey := one_sub_re_pow_le hzb k
  have hnn : (0 : ℝ) ≤ (k : ℝ) ^ 2 * (1 - (f p * (starRingEnd ℂ) (g p)).re)
      - (1 - ((f p * (starRingEnd ℂ) (g p)) ^ k).re) := by linarith
  have hdiv := div_nonneg hnn hppos.le
  have hsplit : ((k : ℝ) ^ 2 * (1 - (f p * (starRingEnd ℂ) (g p)).re)
        - (1 - ((f p * (starRingEnd ℂ) (g p)) ^ k).re)) / (p : ℝ)
      = (k : ℝ) ^ 2 * ((1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ))
        - (1 - ((f p * (starRingEnd ℂ) (g p)) ^ k).re) / (p : ℝ) := by ring
  rw [hsplit] at hdiv
  linarith

/-- **C1 (sqrt form) — `𝔻(f^k, g^k; x) ≤ k·𝔻(f, g; x)`.**  The square root of
`pretDistSq_pow_le`; this is the shape the multiplicative pretentious triangle is usually
quoted in. -/
theorem pretDist_pow_le (f g : ℕ → ℂ) (x : ℝ) (k : ℕ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) :
    pretDist (fun n => f n ^ k) (fun n => g n ^ k) x ≤ (k : ℝ) * pretDist f g x := by
  unfold pretDist
  calc Real.sqrt (pretDistSq (fun n => f n ^ k) (fun n => g n ^ k) x)
      ≤ Real.sqrt ((k : ℝ) ^ 2 * pretDistSq f g x) :=
        Real.sqrt_le_sqrt (pretDistSq_pow_le f g x k hf hg)
    _ = (k : ℝ) * Real.sqrt (pretDistSq f g x) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg k)]

/-! ## C2 — the character-power identity `(λ·χ̄)^k = χ₀` -/

/-- **The `λ·χ̄` datum.**  `f(n) = λ(n)·conj χ(n)`, the `f`-side instantiation of `pretDistSq`
that turns `𝔻(λ, χ·n^{it}; X)` into `𝔻(λ·χ̄, n^{it}; X)` (an EXACT identity: for any `g`,
`f·conj(g·χ) = (f·χ̄)·conj g`). -/
noncomputable def lamChi {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  fun n => lam n * (starRingEnd ℂ) (χ (n : ZMod q))

/-- **The principal-character datum `χ₀`.**  `χ₀(n) = 1` if `(n, q) = 1`, else `0`. -/
noncomputable def chiPrin (q : ℕ) : ℕ → ℂ :=
  fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q)

/-- **The twist transfer (EXACT).**  `𝔻(f, χ·n^{it}; X)² = 𝔻(f·χ̄, n^{it}; X)²` — moving the
character from the `g`-side (the MRT quality shape `M(g;X,W) = inf_{χ,t} 𝔻(g, χ n^{it}; X)²`)
to the `f`-side, where this file's power machinery lives.  Pure per-prime algebra
(`conj(χ·g) = χ̄·conj g`), no hypotheses. -/
theorem pretDistSq_chi_twist {q : ℕ} (χ : DirichletCharacter ℂ q) (f g : ℕ → ℂ) (X : ℝ) :
    pretDistSq f (fun n => χ (n : ZMod q) * g n) X
      = pretDistSq (fun n => f n * (starRingEnd ℂ) (χ (n : ZMod q))) g X := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hmul : f p * (starRingEnd ℂ) (χ (p : ZMod q) * g p)
      = f p * (starRingEnd ℂ) (χ (p : ZMod q)) * (starRingEnd ℂ) (g p) := by
    rw [map_mul, mul_assoc]
  change (1 - (f p * (starRingEnd ℂ) (χ (p : ZMod q) * g p)).re) / (p : ℝ)
      = (1 - (f p * (starRingEnd ℂ) (χ (p : ZMod q)) * (starRingEnd ℂ) (g p)).re) / (p : ℝ)
  rw [hmul]

/-- The `λ·χ̄` datum in the MRT shape: `𝔻(λ, χ·n^{it}; X)² = 𝔻(λ·χ̄, n^{it}; X)²`. -/
theorem pretDistSq_lam_chi_twist {q : ℕ} (χ : DirichletCharacter ℂ q) (t X : ℝ) :
    pretDistSq lam (fun n => χ (n : ZMod q) * costwist t n) X
      = pretDistSq (lamChi χ) (costwist t) X :=
  pretDistSq_chi_twist χ lam (costwist t) X

/-- The `λ·χ̄` datum is 1-bounded (`DirichletCharacter.norm_le_one`; note it is `0`, not
unimodular, at `p | q`). -/
theorem norm_lamChi_le {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖lamChi χ n‖ ≤ 1 := by
  unfold lamChi lam
  rw [norm_mul, Complex.norm_conj, norm_neg, norm_one, one_mul]
  exact DirichletCharacter.norm_le_one χ _

/-- `χ₀` is real-valued (`0` or `1`), so conjugation fixes it. -/
theorem chiPrin_conj (q n : ℕ) : (starRingEnd ℂ) (chiPrin q n) = chiPrin q n := by
  unfold chiPrin
  by_cases h : IsUnit ((n : ℕ) : ZMod q)
  · rw [MulChar.one_apply h]; simp
  · rw [MulChar.map_nonunit _ h]; simp

/-- **C2 — the character-power identity.**  If `k` is even (so `λ(p)^k = 1`), `k ≠ 0`, and
`χ^k = 1` (e.g. `k = 2·orderOf χ`), then `(λ·χ̄)^k = χ₀` POINTWISE — exactly, including at the
primes `p | q` where both sides vanish. -/
theorem lamChi_pow {q : ℕ} (χ : DirichletCharacter ℂ q) {k : ℕ} (hk : k ≠ 0)
    (hke : Even k) (hχk : χ ^ k = 1) (n : ℕ) :
    lamChi χ n ^ k = chiPrin q n := by
  unfold lamChi lam chiPrin
  rw [mul_pow, hke.neg_one_pow, one_mul, ← map_pow, ← MulChar.pow_apply' χ hk, hχk]
  exact chiPrin_conj q n

/-- The `n^{it}` twist raised to the `k`-th power is the `n^{ikt}` twist. -/
theorem costwist_pow (t : ℝ) (k n : ℕ) :
    costwist t n ^ k = costwist ((k : ℝ) * t) n := by
  unfold costwist
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-! ## C3 — the `p | q` correction -/

/-- **The `p | q` deficit** `∑_{p | q, p ≤ X} 1/p` — the ONLY price of replacing the principal
character `χ₀` by the constant datum `1`.  At the door `q ≤ W`, so this is `O(loglog W)`. -/
noncomputable def primeDivSum (q : ℕ) (X : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p ∣ q), (1 : ℝ) / (p : ℝ)

/-- **C3 — the `p | q` correction (HONEST constant `1`).**
`𝔻(χ₀, n^{ib}; X)² ≥ 𝔻(1, n^{ib}; X)² − ∑_{p | q, p ≤ X} 1/p`.

Per prime: at `p ∤ q` the two data agree exactly (`χ₀(p) = 1`); at `p | q` the `χ₀` term is
`1/p` and the constant-`1` term is `(1 − cos(b·log p))/p`, so the defect is EXACTLY
`cos(b·log p)/p ≥ −1/p`.  (The design note's `2/p` is a valid but loose majorant; `1/p` is
what the per-prime algebra gives.) -/
theorem pretDistSq_chiPrin_ge (q : ℕ) (b X : ℝ) :
    pretDistSq (fun _ => 1) (costwist b) X - primeDivSum q X
      ≤ pretDistSq (chiPrin q) (costwist b) X := by
  have hpds : primeDivSum q X
      = ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
          (if p ∣ q then (1 : ℝ) / (p : ℝ) else 0) := by
    unfold primeDivSum
    rw [← Finset.filter_filter, Finset.sum_filter]
  rw [hpds]
  unfold pretDistSq
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_filter] at hp
  have hprime : Nat.Prime p := hp.2
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hre : ((1 : ℂ) * (starRingEnd ℂ) (costwist b p)).re = Real.cos (b * Real.log p) := by
    rw [one_mul, Complex.conj_re, costwist_re]
  have hcos := Real.neg_one_le_cos (b * Real.log p)
  by_cases hdvd : p ∣ q
  · have hnu : ¬ IsUnit ((p : ℕ) : ZMod q) := by
      rw [ZMod.isUnit_prime_iff_not_dvd hprime]; exact not_not_intro hdvd
    have hz : chiPrin q p = 0 := MulChar.map_nonunit _ hnu
    change (1 - ((1 : ℂ) * (starRingEnd ℂ) (costwist b p)).re) / (p : ℝ)
        - (if p ∣ q then (1 : ℝ) / (p : ℝ) else 0)
      ≤ (1 - (chiPrin q p * (starRingEnd ℂ) (costwist b p)).re) / (p : ℝ)
    rw [if_pos hdvd, hz, hre, zero_mul, Complex.zero_re]
    have heq : (1 - (0 : ℝ)) / (p : ℝ)
          - ((1 - Real.cos (b * Real.log p)) / (p : ℝ) - 1 / (p : ℝ))
        = (1 + Real.cos (b * Real.log p)) / (p : ℝ) := by ring
    have hnn : (0 : ℝ) ≤ (1 + Real.cos (b * Real.log p)) / (p : ℝ) :=
      div_nonneg (by linarith) hppos.le
    linarith [heq, hnn]
  · have hu : IsUnit ((p : ℕ) : ZMod q) := (ZMod.isUnit_prime_iff_not_dvd hprime).mpr hdvd
    have hone : chiPrin q p = 1 := MulChar.one_apply hu
    change (1 - ((1 : ℂ) * (starRingEnd ℂ) (costwist b p)).re) / (p : ℝ)
        - (if p ∣ q then (1 : ℝ) / (p : ℝ) else 0)
      ≤ (1 - (chiPrin q p * (starRingEnd ℂ) (costwist b p)).re) / (p : ℝ)
    rw [if_neg hdvd, hone]
    linarith

/-! ## C4 — the H1 exit -/

/-- **C4 — the H1 exit (`chi_floor_of_order`).**  For a Dirichlet character `χ` mod `q`, any
even `k ≠ 0` with `χ^k = 1` (the intended `k = 2·orderOf χ`), any `X ≥ e` and any real `t` on
the extreme range `|k·t| ≥ 1`:

  `loglog X − (3/4)loglog(|kt|+3) − 5·logloglog(|kt|+16) − C − ∑_{p|q, p≤X} 1/p`
      `≤ k²·𝔻(λ·χ̄, n^{it}; X)²`,

with a UNIFORM constant `C` (inherited verbatim from `dist_one_floor_pow`) — uniform in `q`,
`χ`, `k`, `X` and `t`.  This is ROUTE A's H1: no `χ`-power region is used, only the landed
`ζ`-side floor at frequency `b = k·t` (which has NO upper cap on `|b|`), the `k`-fold power
inequality, the character-power identity, and the `p | q` deficit. -/
theorem chi_floor_of_order :
    ∃ C : ℝ, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (k : ℕ) (X t : ℝ),
      k ≠ 0 → Even k → χ ^ k = 1 → Real.exp 1 ≤ X → 1 ≤ |(k : ℝ) * t| →
        Real.log (Real.log X)
            - (3 / 4) * Real.log (Real.log (|(k : ℝ) * t| + 3))
            - 5 * Real.log (Real.log (Real.log (|(k : ℝ) * t| + 16)))
            - C - primeDivSum q X
          ≤ (k : ℝ) ^ 2 * pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨C, hC⟩ := dist_one_floor_pow
  refine ⟨C, fun q χ k X t hk hke hχk hX hkt => ?_⟩
  have hf1 : ∀ n, ‖lamChi χ n‖ ≤ 1 := norm_lamChi_le χ
  have hg1 : ∀ n, ‖costwist t n‖ ≤ 1 := fun n => le_of_eq (costwist_norm t n)
  have hpow := pretDistSq_pow_le (lamChi χ) (costwist t) X k hf1 hg1
  have he1 : (fun n => lamChi χ n ^ k) = chiPrin q := funext (lamChi_pow χ hk hke hχk)
  have he2 : (fun n => costwist t n ^ k) = costwist ((k : ℝ) * t) := funext (costwist_pow t k)
  rw [he1, he2] at hpow
  have hC3 := pretDistSq_chiPrin_ge q ((k : ℝ) * t) X
  have hC1 := hC X ((k : ℝ) * t) hX hkt
  linarith

/-- **C4 (divided form).**  The same floor with the `1/k²` in front of the bracket — the shape
the quality infimum `M(g; X, W)` consumes directly. -/
theorem chi_floor_of_order_div :
    ∃ C : ℝ, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (k : ℕ) (X t : ℝ),
      k ≠ 0 → Even k → χ ^ k = 1 → Real.exp 1 ≤ X → 1 ≤ |(k : ℝ) * t| →
        (Real.log (Real.log X)
            - (3 / 4) * Real.log (Real.log (|(k : ℝ) * t| + 3))
            - 5 * Real.log (Real.log (Real.log (|(k : ℝ) * t| + 16)))
            - C - primeDivSum q X) / (k : ℝ) ^ 2
          ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨C, hC⟩ := chi_floor_of_order
  refine ⟨C, fun q χ k X t hk hke hχk hX hkt => ?_⟩
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := Nat.pos_of_ne_zero hk
    exact_mod_cast this
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ hk2]
  have h := hC q χ k X t hk hke hχk hX hkt
  linarith

/-- **The `k = 2·orderOf χ` instantiation.**  For `q ≠ 0` the character group is finite, so
`orderOf χ > 0`; `k = 2·orderOf χ` is even, nonzero, and kills `χ`.  The gate `1 ≤ |k·t|` is
exactly CHI-CHECK's H1 range `|t| ≥ 1/(2·ord χ)`. -/
theorem chi_floor_orderOf :
    ∃ C : ℝ, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (X t : ℝ), q ≠ 0 →
      Real.exp 1 ≤ X → 1 ≤ |((2 * orderOf χ : ℕ) : ℝ) * t| →
        (Real.log (Real.log X)
            - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
            - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
            - C - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2
          ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨C, hC⟩ := chi_floor_of_order_div
  refine ⟨C, fun q χ X t hq hX hkt => ?_⟩
  haveI : NeZero q := ⟨hq⟩
  have hord : 0 < orderOf χ := MulChar.orderOf_pos χ
  have hk : 2 * orderOf χ ≠ 0 := by omega
  have hke : Even (2 * orderOf χ) := ⟨orderOf χ, by ring⟩
  have hχk : χ ^ (2 * orderOf χ) = 1 := by
    rw [Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  exact hC q χ (2 * orderOf χ) X t hk hke hχk hX hkt

/-- **The H1 exit in the MRT quality shape.**  The same floor, stated on
`𝔻(λ, χ·n^{it}; X)²` (the object the quality infimum `M(λ; X, W)` ranges over) via the exact
twist transfer `pretDistSq_lam_chi_twist`. -/
theorem chi_floor_orderOf_twisted :
    ∃ C : ℝ, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (X t : ℝ), q ≠ 0 →
      Real.exp 1 ≤ X → 1 ≤ |((2 * orderOf χ : ℕ) : ℝ) * t| →
        (Real.log (Real.log X)
            - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
            - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
            - C - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2
          ≤ pretDistSq lam (fun n => χ (n : ZMod q) * costwist t n) X := by
  obtain ⟨C, hC⟩ := chi_floor_orderOf
  refine ⟨C, fun q χ X t hq hX hkt => ?_⟩
  rw [pretDistSq_lam_chi_twist χ t X]
  exact hC q χ X t hq hX hkt

end Salt.MR
