/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The M-boundary map: what separates the crack from twins (nodes MB-2/MB-3)

The MB-1 sweep (`docs/exploration/s3-a3-design.md`, `MB-1 — ADJUDICATED`) found
that the proven crack (log-Chowla-2) runs on **dilation invariance, twice**, and
that complete multiplicativity enters through **one** mechanism (the collapse
identity), which consumes only `λ(p)² = 1` — never the sign `λ(p) = −1`.  This
file lands the two kernel-checked deliverables that make that map precise:

* **`dilation_forces_log`** — the crown.  Exact dilation covariance
  `w(qn) = w(n)/q` **forces** the harmonic weight `w(n) = w(1)/n`.  Logarithmic
  averaging is not a convenience; it is the *unique* weighting compatible with
  the multiplicative change of variables at the heart of the entropy argument.
  The companion `approx_covariance_not_unique` is the honest caveat: only the
  *exact* covariance pins `w` down — bounded multiplicative oscillation survives.

* **`completelyMult_pm_one_collapse`** — the collapse engine of Prop 2.6 for the
  whole real completely-multiplicative `±1` class, exhibiting that the sign is
  inert (only `f(p)² = 1` is used).

* **`collapseCharacterization_candidate`** — the candidate biconditional
  (collapse `⟺` complete multiplicativity, for `±1` weights), stated as a `Prop`
  with the converse marked OPEN.  The MB-23 numeric hunt (GF(2) linear algebra,
  see `scratchpad/mb_hunt.py`) found NO finite counterexample: with the natural
  normalization `f(1) = 1`, collapse and complete multiplicativity have the same
  `𝔽₂` solution space for every `N ≤ 80` (exhaustively for `N ≤ 14`).  The lone
  extra collapse dimension is the degenerate `f(1) = −1` freedom that collapse
  never constrains.  The hunt therefore shifts the evidence toward the converse
  being TRUE, while it remains OPEN at the infinite level.
-/
import Mathlib

namespace Salt.Entropy.Chowla

/-! ### MB-2 — the dilation-covariance uniqueness lemma (the crown) -/

/-- **Why the logarithm is there.**  The dilation covariance `w(qn) = w(n)/q` —
the property `dilation_error_div` shows the log-Chowla argument consumes (Tao's
Lemma 2.5 change of variables) — forces the harmonic weight up to scale.
Logarithmic averaging is not a convenience; it is the *unique* weighting
compatible with the multiplicative change of variables at the heart of the
entropy argument.  Under natural (uniform) averaging this covariance fails
constitutively — the first formally-localized obstruction to removing the log
from log-Chowla (see the MB-1 boundary map, `docs/exploration/s3-a3-design.md`).

The proof is a one-line specialization: read the covariance at `q := n, n := 1`,
so `w(n) = w(n · 1) = w(1)/n`. -/
theorem dilation_forces_log (w : ℕ → ℝ)
    (hcov : ∀ q n, 1 ≤ q → 1 ≤ n → w (q * n) = w n / (q : ℝ)) :
    ∀ n, 1 ≤ n → w n = w 1 / (n : ℝ) := by
  intro n hn
  simpa using hcov n 1 hn le_rfl

/-- The witness for `approx_covariance_not_unique`: the harmonic weight `1/n`
reweighted by a bounded, non-constant multiplicative factor (`1` at `n = 1`,
else `2`).  Its harmonic content `w(n)·n` stays in `[1,2]`, so it obeys the
dilation covariance up to a bounded factor in `[1/2, 2]`, yet it is not `c/n`. -/
private noncomputable def boundedWeight (n : ℕ) : ℝ :=
  (if n = 1 then (1 : ℝ) else 2) / (n : ℝ)

/-- **The honest crown is the EXACT form.**  Approximate covariance does NOT pin
`w` down: there is a weight whose harmonic content `w(n)·n` stays trapped in
`[1,2]` — hence `w(qn)` and `w(n)/q` agree up to a bounded multiplicative factor
in `[1/2, 2]`, the "approximate dilation covariance" — yet `w` is provably *not*
proportional to `1/n`.  The canonical smooth witness is `w(n) = (1 + sin(log n))
/ n`; we realize the same phenomenon with a simple bounded non-constant factor.
Only the exact covariance `w(qn) = w(n)/q` (`dilation_forces_log`) is rigid. -/
theorem approx_covariance_not_unique :
    ∃ w : ℕ → ℝ,
      (∀ n, 1 ≤ n → 1 ≤ w n * (n : ℝ) ∧ w n * (n : ℝ) ≤ 2) ∧
      ¬ ∃ c : ℝ, ∀ n, 1 ≤ n → w n = c / (n : ℝ) := by
  refine ⟨boundedWeight, ?_, ?_⟩
  · intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have key : boundedWeight n * (n : ℝ) = (if n = 1 then (1 : ℝ) else 2) := by
      rw [boundedWeight, div_mul_cancel₀ _ hnR]
    rw [key]
    constructor <;> · split_ifs <;> norm_num
  · rintro ⟨c, hc⟩
    have h1 := hc 1 le_rfl
    have h2 := hc 2 (by norm_num)
    have hw1 : boundedWeight 1 = 1 := by rw [boundedWeight, if_pos rfl, Nat.cast_one, div_one]
    have hw2 : boundedWeight 2 = 1 := by
      rw [boundedWeight, if_neg (by norm_num : ¬ ((2 : ℕ) = 1))]; norm_num
    rw [hw1] at h1
    rw [hw2] at h2
    norm_num at h1 h2
    linarith

/-! ### MB-3 — the collapse engine for the completely-multiplicative ±1 class -/

/-- **The collapse engine of Prop 2.6** for the whole real completely-multiplicative
`±1` class.  For `f` completely multiplicative with `f(p) ∈ {±1}` on primes,
`f(pN)·f(pN+p) = f(N)·f(N+1)`: both left arguments carry the factor `p`
(`pN + p = p(N+1)`), and `f(p)² = 1` erases it.  The sign `λ(p) = −1` is INERT —
the spine's collapse consumes only `λ(p)² = 1` — so the crack's multiplicative
mechanism belongs to the family containing `λ`, real Dirichlet characters, and
their twists (the MB-1 headline: `liouville_prime` has zero proof-term uses). -/
theorem completelyMult_pm_one_collapse (f : ℕ → ℝ)
    (hCM : ∀ a b, f (a * b) = f a * f b)
    (hpm : ∀ p, p.Prime → f p = 1 ∨ f p = -1) :
    ∀ p N, p.Prime → f (p * N) * f (p * N + p) = f N * f (N + 1) := by
  intro p N hp
  have hpp : p * N + p = p * (N + 1) := by ring
  rw [hpp, hCM p N, hCM p (N + 1)]
  have hsq : f p * f p = 1 := by
    rcases hpm p hp with h | h <;> rw [h] <;> norm_num
  have hcalc : f p * f N * (f p * f (N + 1)) = (f p * f p) * (f N * f (N + 1)) := by ring
  rw [hcalc, hsq, one_mul]

/-! ### The open wall — collapse `⟺` complete multiplicativity? -/

/-- **The candidate characterization (converse OPEN).**  For a real `±1` weight
`f`, is the p-collapse identity `f(pN)·f(pN+p) = f(N)·f(N+1)` (all primes `p`,
all `N`) EQUIVALENT to complete multiplicativity?

* The backward direction (`← `, complete multiplicativity `⟹` collapse) is
  `completelyMult_pm_one_collapse` — PROVEN.
* The forward direction (`→ `, collapse `⟹` complete multiplicativity) is OPEN.
  The MB-1 reframing: collapse is *pair-correlation dilation-invariance*, which a
  priori constrains only pair-correlations of `f`, not its values — the wall the
  house expected.  **But the MB-23 numeric hunt found no finite counterexample**
  (`scratchpad/mb_hunt.py`): over `𝔽₂` (writing `f = (−1)^g`, collapse and
  complete multiplicativity are LINEAR systems) the two solution spaces coincide
  for every `N ≤ 80` once `f(1) = 1` is imposed, and exhaustive search confirms
  it for `N ≤ 14`.  The single extra collapse dimension is precisely the
  degenerate `f(1) = −1` freedom (a genuine multiplicative function has
  `f(1) = 1`).  Finite-level equivalence for *all* `N` would prove the infinite
  converse; the hunt verifies it through `N = 80` but does not settle it.

This `def` is the frozen open-wall statement (MB-4 raw material), not a theorem;
the biconditional is asserted, never proved. -/
def collapseCharacterization_candidate : Prop :=
  ∀ f : ℕ → ℝ, (∀ n, 1 ≤ n → f n = 1 ∨ f n = -1) →
    ((∀ p N : ℕ, p.Prime → f (p * N) * f (p * N + p) = f N * f (N + 1))
      ↔ (∀ a b : ℕ, f (a * b) = f a * f b))

end Salt.Entropy.Chowla
