/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Chowla.CircleMethod

/-!
# S7 ARC — `bigXi_arc`: the major-arc localisation of `Ξ_H` (transcription + opening stones)

This file opens rung **S7** of the MR-gate freeze (`docs/exploration/mr-freeze.md`,
line 17).  The frozen row, verbatim:

> S7 ARC (C 2500; exponents STAGED-GATED): bigXi_arc: xi in Xi_H (threshold
> eps^2/log H, CircleMethod.lean:36-45) => xi/H near a/q, q <= log^{B5}H;
> contrapositive Vinogradov (LS/Vaughan + ExpSum vdC); transcribe Tao pp.24-25
> FIRST.

## The source (Tao, arXiv:1509.05422, pp. 24–25)

`Ξ_H` is Tao's large-spectrum set (`Salt/Entropy/Chowla/CircleMethod.lean:40-45`,
at the Liouville instantiation `a = 1`, `c_p = 1`, where the `η ∈ ℤ/aℤ` twist
collapses):

  `Ξ_H = {ξ ∈ ℤ/Hℤ : ε²/log H ≤ ‖S_H(−ξ/H)‖}`,
  `S_H(α) = ∑_{p ∈ 𝒫_H} (1/p) e(αp)`,  `𝒫_H = {p prime : ε²H/2 < p ≤ ε²H}`.

Tao's Lemma 3.5 (p. 25) bounds `|Ξ_H| = O_{a,h,ε}(1)` through a restriction
theorem.  **Remark 3.6 (p. 25) is the S7 statement**: in the Liouville case
`g₁ = g₂ = λ` one has `c_p = 1`, so `S_H(α)` is a genuine (weighted) exponential
sum over primes, handled by *Vinogradov's estimates* (Iwaniec–Kowalski §13.5);
and then, in Tao's own words,

> "one can compute `Ξ_H` fairly explicitly; it basically consists of those
> frequencies `ξ` which are 'major arc' in the sense that `ξ/H` is close to a
> rational `a/q` of bounded denominator `q`."

Remark 3.6 also records *why* this rung is worth its 2500 lines: it lets the
heavy exponential-sum estimates of [17, Lemma 2.2, Theorem 2.3] be replaced by
the simpler [17, Theorem A.1] — exactly the license the MR-gate freeze cites at
`chowla.txt:743-750` for the Ξ-restricted door.

## A-1 — the transcription, and the two transcription decisions (declared, not silent)

The frozen row is prose; two things it leaves open had to be *carried*, never
*chosen*, so that iron rule 1 is respected when the staging pins them:

1. **`B₅` is a parameter, not a numeral.**  The row says "exponents
   STAGED-GATED" and `mr-freeze.md:49` forbids the S7 exponent freeze
   pre-staging.  So `BigXiArc` takes `B₅ : ℝ` as an argument; nothing numeric is
   pinned here.  `bigXiArc_mono` shows the target can only *weaken* as `B₅`
   grows, so a staged pin at any larger exponent is free.
2. **"near" is the standard major-arc radius `(log H)^{B₅}/H`** (`arcRadius`),
   i.e. the single exponent the card names is used for both the denominator cap
   and the radius.  This is the classical Vinogradov major-arc shape and — the
   decisive consistency check — it is *exactly* what Dirichlet's approximation
   theorem at order `⌈H/(log H)^{B₅}⌉` produces (`exists_large_den_of_minor`
   below).  Any other radius the staging prefers re-instantiates the target for
   free through `nearRat_mono`.

The denominator cap is kept as a **real** bound `(q : ℝ) ≤ (log H)^{B₅}` — the
card's `q <= log^{B5}H` byte-for-byte, with no floor inserted.

Binder order (the `∃`-binder-position check): `B₅` is absolute (a parameter of
the definition), `ε` is universally quantified outermost, and the threshold
`H₀` is chosen *after* `ε` — it must be, because the membership threshold
`ε²/log H` is `ε`-dependent and the Vinogradov saving has to beat it.

## A-3 — what lands tonight (all sorry-free, all standalone)

* `nearRat_mono`, `nearRat_neg`, `nearRat_zero` — the arc-predicate frame.
  `nearRat_neg` is load-bearing, not cosmetic: `Ξ_H`'s threshold is stated at
  `−ξ.val/H` while the frozen target speaks at `ξ/H`, and the sign has to be
  crossed somewhere.
* `exists_dirichlet_approx` — Dirichlet's theorem in arc coordinates, and
  `nearRat_of_pos`: every frequency is major at radius `1/(Q+1)`.  This is the
  *exhaustiveness* of the arc cover, the frame the minor-arc argument sits on.
* `exists_large_den_of_not_nearRat` / `exists_large_den_of_minor` — **THE
  opening stone**: "not major" is converted into a Dirichlet approximant whose
  denominator *exceeds* `(log H)^{B₅}`, which is precisely the hypothesis
  Vinogradov's estimate consumes.  The second is the same statement at the arc
  datum, with the order `⌈H/(log H)^{B₅}⌉` chosen so the radius matches.
* `mem_bigXi_iff`, `not_mem_bigXi_of_norm_lt`, `norm_expSum_le_sum`,
  `threshold_le_sum_inv_of_mem` — the `Ξ_H` interface.  The first and third are
  verbatim transplants of `Salt/Entropy/Chowla/CircleMethod.lean:351-361` and
  `:371-375`, which are `private` there and hence unusable from here.
* `primeWindow_bounds`, `inv_p_le_of_mem`, `le_inv_p_of_mem`,
  `norm_expSum_le_card` — the dyadic weight normalisation `1/p ≍ 1/(ε²H)`, the
  frame ladder rung L1 needs to strip the `1/p` weight.
* `bigXiArc_of_minorArc` — **the reduction**: the frozen target follows from the
  single analytic obligation `MinorArcBound`.  After this stone S7 is *entirely*
  the minor-arc estimate; no bookkeeping remains on the `Ξ_H` side.
* `nearRat_arc_zero` — the `ξ = 0` instance of the target, discharged outright.
* `bigXiArc_mono` — the staged-gate robustness stone.

The file is deliberately **not** wired into `Salt/MR/All.lean` yet: `BigXiArc`
has no consumer until S9 (the major-arc reduction) exists.

## The remaining ladder (enumerated for the morning)

The obligation `MinorArcBound B₅` is all that is left, and it splits:

* **L1 `expSum_partial_summation`** [B, ~200] — strip the `1/p` weight: Abel
  summation turns `S_H(α) = ∑_{p ∈ 𝒫_H} (1/p) e(αp)` into
  `(1/(ε²H))·∑_{p ≤ ε²H} e(αp)` plus a controlled remainder, using that `𝒫_H`
  is the *dyadic* window `(ε²H/2, ε²H]` so `1/p ≍ 1/(ε²H)` throughout.
* **L2 `vonMangoldt_to_primes`** [B, ~250] — pass to `∑_{n ≤ N} Λ(n) e(αn)`
  (the shape every source states); the prime-power defect is `O(√N log N)`.
* **L3 `vaughan_identity`** [C, ~600] — Vaughan's identity: the Type I / Type II
  bilinear decomposition of `Λ` at parameters `U, V`.  No mathlib support; the
  Möbius/divisor bookkeeping is the bulk.
* **L4 `typeI_bound`** [B/C, ~350] — the Type I sums against the linear-phase
  geometric series; consumes `‖∑_{m ≤ M} e(αm)‖ ≤ min(M, 1/(2‖α‖))`.
* **L5 `typeII_bound`** [C, ~500] — the Type II sums by Cauchy–Schwarz and the
  large-sieve/Weyl differencing already present in `Salt/ExpSum/` (the row's
  "LS/Vaughan + ExpSum vdC"); this is the risk stone.
* **L6 `vinogradov_minor`** [C, ~350] — assembly at the Dirichlet approximant
  supplied by `exists_large_den_of_minor`: `q > (log H)^{B₅}` gives the
  `N/√q` saving, i.e. `‖∑ Λ(n)e(αn)‖ ≪ N (log N)^4 / (log H)^{B₅/2}`.
* **L7 `minorArcBound_holds`** [B, ~250] — the exponent bookkeeping that turns
  L6 into `‖S_H(α)‖ < ε²/log H`, **pinning `B₅`**.  STAGED-GATED: this is the
  one rung that may not fire before the exponent freeze is unblocked.

Estimate for the remainder: ~2500 lines, matching the frozen row's price.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## A-2 — the arc objects -/

/-- **The major-arc (near-rational) predicate.**  `NearRat Q r α` says the
frequency `α` lies within `r` of a rational `a/q` whose denominator obeys
`q ≤ Q`.  The cap `Q` is a **real** number, so that the frozen card's
`q <= log^{B5}H` transcribes with no floor inserted. -/
def NearRat (Q r α : ℝ) : Prop :=
  ∃ (a : ℤ) (q : ℕ), 0 < q ∧ (q : ℝ) ≤ Q ∧ |α - (a : ℝ) / (q : ℝ)| ≤ r

/-- **The denominator cap** `(log H)^{B₅}` of the frozen row. -/
def arcDen (B₅ : ℝ) (H : ℕ) : ℝ := Real.log (H : ℝ) ^ B₅

/-- **The major-arc radius** `(log H)^{B₅}/H` — the reading of "near" declared in
the module header.  It is the radius Dirichlet approximation at order
`⌈H/(log H)^{B₅}⌉` delivers (`exists_large_den_of_minor`). -/
def arcRadius (B₅ : ℝ) (H : ℕ) : ℝ := arcDen B₅ H / (H : ℝ)

/-! ## A-1 — the frozen statement, transcribed

`BigXiArc B₅` **is** the frozen row `bigXi_arc`.  Nothing below may adjust it
(iron rule 1); the two carried parameters are declared in the module header. -/

/-- **S7 ARC — `bigXi_arc`, the FROZEN statement** (`mr-freeze.md:17`):

> `bigXi_arc`: `ξ ∈ Ξ_H` (threshold `ε²/log H`) ⟹ `ξ/H` near `a/q`,
> `q ≤ log^{B₅}H`.

Every element of the large-spectrum set `Ξ_H` is a major-arc frequency: `ξ/H`
lies within `(log H)^{B₅}/H` of a rational with denominator at most
`(log H)^{B₅}`.  `H₀` depends on `ε` (it must: the membership threshold
`ε²/log H` is `ε`-dependent); `B₅` is absolute and STAGED-GATED. -/
def BigXiArc (B₅ : ℝ) : Prop :=
  ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
    ∀ ξ ∈ bigXi eps H,
      NearRat (arcDen B₅ H) (arcRadius B₅ H) ((ξ.val : ℝ) / (H : ℝ))

/-- **The minor-arc obligation** — the single analytic input of S7, and after
`bigXiArc_of_minorArc` the *only* thing between the corpus and `BigXiArc`.
This is the "contrapositive Vinogradov" of the frozen row: off the major arcs
the weighted prime exponential sum drops below the `Ξ_H` threshold.  Its proof
is the ladder L1–L7 enumerated in the module header. -/
def MinorArcBound (B₅ : ℝ) : Prop :=
  ∀ eps : ℚ, 0 < eps → ∃ H₀ : ℕ, ∀ H : ℕ, ∀ [NeZero H], H₀ ≤ H →
    ∀ α : ℝ, ¬ NearRat (arcDen B₅ H) (arcRadius B₅ H) α →
      ‖expSum eps H α‖ < (eps : ℝ) ^ 2 / Real.log (H : ℝ)

/-! ## Stone 1 — the arc-predicate frame -/

/-- `NearRat` is monotone in both the denominator cap and the radius: enlarging
either can only add major-arc frequencies. -/
theorem nearRat_mono {Q Q' r r' α : ℝ} (hQ : Q ≤ Q') (hr : r ≤ r')
    (h : NearRat Q r α) : NearRat Q' r' α := by
  obtain ⟨a, q, hq, hqQ, hd⟩ := h
  exact ⟨a, q, hq, hqQ.trans hQ, hd.trans hr⟩

/-- **The sign seam.**  `NearRat` is invariant under `α ↦ −α` (send `a ↦ −a`).
This is what lets the `Ξ_H` threshold, which is stated at `−ξ.val/H`
(`CircleMethod.lean:45`), meet the frozen target, which is stated at `ξ/H`. -/
theorem nearRat_neg {Q r α : ℝ} : NearRat Q r (-α) ↔ NearRat Q r α := by
  constructor
  · rintro ⟨a, q, hq, hqQ, hd⟩
    refine ⟨-a, q, hq, hqQ, ?_⟩
    have hrw : α - ((-a : ℤ) : ℝ) / (q : ℝ) = -(-α - (a : ℝ) / (q : ℝ)) := by
      push_cast
      ring
    rw [hrw, abs_neg]
    exact hd
  · rintro ⟨a, q, hq, hqQ, hd⟩
    refine ⟨-a, q, hq, hqQ, ?_⟩
    have hrw : -α - ((-a : ℤ) : ℝ) / (q : ℝ) = -(α - (a : ℝ) / (q : ℝ)) := by
      push_cast
      ring
    rw [hrw, abs_neg]
    exact hd

/-- **The trivial arm.**  `α = 0` is major on every arc system with cap `≥ 1`
and nonnegative radius (take `a/q = 0/1`).  Together with `ZMod.val_zero` this
is the `ξ = 0` instance of the frozen target — recall `0 ∈ Ξ_H` always
(`MRTDoor.lean:106`), so this arm is never vacuous. -/
theorem nearRat_zero {Q r : ℝ} (hQ : 1 ≤ Q) (hr : 0 ≤ r) : NearRat Q r 0 :=
  ⟨0, 1, Nat.one_pos, by simpa using hQ, by simpa using hr⟩

/-! ## Stone 2 — Dirichlet's theorem in arc coordinates (the frame) -/

/-- **Dirichlet approximation, arc form.**  For every `α` and every order
`Q ≥ 1` there is `a/q` with `0 < q ≤ Q` and `|α − a/q| ≤ 1/(q(Q+1))`.

This is mathlib's `Real.exists_int_int_abs_mul_sub_le` divided through by `k`;
the `1/(q(Q+1))` shape (rather than the weaker `1/(Q+1)`) is the one the
minor-arc extraction needs, since the `q` in the denominator is what makes the
radius match `arcRadius`. -/
theorem exists_dirichlet_approx (α : ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ (a : ℤ) (q : ℕ), 0 < q ∧ q ≤ Q ∧
      |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * ((Q : ℝ) + 1)) := by
  obtain ⟨j, k, hk0, hkQ, h⟩ := Real.exists_int_int_abs_mul_sub_le α hQ
  have htn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0.le
  have hk0' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast htn
  have hQ1 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  refine ⟨j, k.toNat, by omega, by omega, ?_⟩
  rw [hcast]
  -- `|α − j/k| ≤ 1/(k(Q+1))`, from `|kα − j| ≤ 1/(Q+1)` after dividing by `k`.
  have habs : |(k : ℝ) * α - (j : ℝ)| = |α - (j : ℝ) / (k : ℝ)| * (k : ℝ) := by
    have hfac : (k : ℝ) * α - (j : ℝ) = (α - (j : ℝ) / (k : ℝ)) * (k : ℝ) := by
      field_simp
    rw [hfac, abs_mul, abs_of_pos hk0']
  rw [le_div_iff₀ (mul_pos hk0' hQ1)]
  calc |α - (j : ℝ) / (k : ℝ)| * ((k : ℝ) * ((Q : ℝ) + 1))
      = (|α - (j : ℝ) / (k : ℝ)| * (k : ℝ)) * ((Q : ℝ) + 1) := by ring
    _ = |(k : ℝ) * α - (j : ℝ)| * ((Q : ℝ) + 1) := by rw [habs]
    _ ≤ (1 / ((Q : ℝ) + 1)) * ((Q : ℝ) + 1) := mul_le_mul_of_nonneg_right h hQ1.le
    _ = 1 := by field_simp

/-- **The arc cover is exhaustive**: at order `Q ≥ 1` *every* frequency is major
with radius `1/(Q+1)`.  This is the frame fact — the major/minor dichotomy is a
dichotomy of radii, not of frequencies. -/
theorem nearRat_of_pos (α : ℝ) {Q : ℕ} (hQ : 0 < Q) :
    NearRat (Q : ℝ) (1 / ((Q : ℝ) + 1)) α := by
  obtain ⟨a, q, hq, hqQ, hd⟩ := exists_dirichlet_approx α hQ
  refine ⟨a, q, hq, by exact_mod_cast hqQ, hd.trans ?_⟩
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ1 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  refine one_div_le_one_div_of_le hQ1 ?_
  nlinarith

/-! ## Stone 3 — the minor-arc extraction (THE opening stone)

The contrapositive direction the frozen row calls for: *not major* is turned
into a Dirichlet approximant whose denominator **exceeds** the cap.  That
large-denominator approximant is exactly the hypothesis Vinogradov's estimate
consumes, so this stone is the handoff point between the arc bookkeeping (done)
and the analysis (ladder L1–L7). -/

/-- **Minor-arc extraction, general form.**  If `α` is not major at cap `Q` and
radius `r`, and the Dirichlet order `Q'` is fine enough that `1/(Q'+1) ≤ r`,
then the order-`Q'` Dirichlet approximant of `α` has denominator `> Q`. -/
theorem exists_large_den_of_not_nearRat {Q r α : ℝ} {Q' : ℕ}
    (hQ' : 0 < Q') (hr : 1 / ((Q' : ℝ) + 1) ≤ r) (hnot : ¬ NearRat Q r α) :
    ∃ (a : ℤ) (q : ℕ), Q < (q : ℝ) ∧ q ≤ Q' ∧
      |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * ((Q' : ℝ) + 1)) := by
  obtain ⟨a, q, hq, hqQ', hd⟩ := exists_dirichlet_approx α hQ'
  refine ⟨a, q, ?_, hqQ', hd⟩
  by_contra hcon
  push Not at hcon
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ1 : (0 : ℝ) < (Q' : ℝ) + 1 := by positivity
  have hsmall : 1 / ((q : ℝ) * ((Q' : ℝ) + 1)) ≤ r := by
    refine le_trans (one_div_le_one_div_of_le hQ1 ?_) hr
    nlinarith
  exact hnot ⟨a, q, hq, hcon, hd.trans hsmall⟩

/-! ### The arc datum: positivity of the cap and the radius -/

/-- `1 ≤ log H` once `H ≥ 3` (since `e < 3`).  The window floor under every
statement in this file. -/
theorem one_le_log_of_three_le {H : ℕ} (hH : 3 ≤ H) : 1 ≤ Real.log (H : ℝ) := by
  have h3 : (3 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  refine (Real.le_log_iff_exp_le (by linarith)).mpr ?_
  have he := Real.exp_one_lt_d9
  linarith

/-- The denominator cap is `≥ 1` for `H ≥ 3` and `B₅ ≥ 0`. -/
theorem one_le_arcDen {B₅ : ℝ} (hB : 0 ≤ B₅) {H : ℕ} (hH : 3 ≤ H) :
    1 ≤ arcDen B₅ H :=
  Real.one_le_rpow (one_le_log_of_three_le hH) hB

/-- The major-arc radius is positive for `H ≥ 3` and `B₅ ≥ 0`. -/
theorem arcRadius_pos {B₅ : ℝ} (hB : 0 ≤ B₅) {H : ℕ} (hH : 3 ≤ H) :
    0 < arcRadius B₅ H := by
  have hden := one_le_arcDen hB hH
  have hH3 : (3 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  exact div_pos (by linarith) (by linarith)

/-- The denominator cap is monotone in the exponent (base `log H ≥ 1`). -/
theorem arcDen_mono {B₅ B₅' : ℝ} (hBB : B₅ ≤ B₅') {H : ℕ} (hH : 3 ≤ H) :
    arcDen B₅ H ≤ arcDen B₅' H :=
  Real.rpow_le_rpow_of_exponent_le (one_le_log_of_three_le hH) hBB

/-- The major-arc radius is monotone in the exponent. -/
theorem arcRadius_mono {B₅ B₅' : ℝ} (hBB : B₅ ≤ B₅') {H : ℕ} (hH : 3 ≤ H) :
    arcRadius B₅ H ≤ arcRadius B₅' H := by
  have hH3 : (3 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  exact div_le_div_of_nonneg_right (arcDen_mono hBB hH) (by linarith)

/-- **Minor-arc extraction at the arc datum.**  If `α` is not major for the
window `H` at exponent `B₅`, then `α` has a Dirichlet approximant `a/q` with

  `(log H)^{B₅} < q ≤ ⌈H/(log H)^{B₅}⌉`  and  `|α − a/q| ≤ (log H)^{B₅}/(qH)`.

The order `⌈H/(log H)^{B₅}⌉` is chosen exactly so that Dirichlet's radius
`1/(q(Q'+1))` lands inside `arcRadius` — which is *why* `(log H)^{B₅}/H` is the
right reading of "near" in the frozen row.  This is the shape Vinogradov's
estimate consumes (ladder rung L6). -/
theorem exists_large_den_of_minor {B₅ : ℝ} (hB : 0 ≤ B₅) {H : ℕ} (hH : 3 ≤ H)
    {α : ℝ} (hnot : ¬ NearRat (arcDen B₅ H) (arcRadius B₅ H) α) :
    ∃ (a : ℤ) (q : ℕ), arcDen B₅ H < (q : ℝ) ∧
      q ≤ ⌈(H : ℝ) / arcDen B₅ H⌉₊ ∧
      |α - (a : ℝ) / (q : ℝ)| ≤ arcDen B₅ H / ((q : ℝ) * (H : ℝ)) := by
  have hden : 1 ≤ arcDen B₅ H := one_le_arcDen hB hH
  have hH3 : (3 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  have hdpos : (0 : ℝ) < arcDen B₅ H := by linarith
  set Q' : ℕ := ⌈(H : ℝ) / arcDen B₅ H⌉₊ with hQ'def
  have hceil : (H : ℝ) / arcDen B₅ H ≤ (Q' : ℝ) := Nat.le_ceil _
  have hQ'pos : 0 < Q' := by
    rw [hQ'def]
    exact Nat.ceil_pos.mpr (div_pos hHpos hdpos)
  have hQ1 : (0 : ℝ) < (Q' : ℝ) + 1 := by positivity
  -- The order is fine enough: `1/(Q'+1) ≤ (log H)^{B₅}/H = arcRadius`.
  have hfine : 1 / ((Q' : ℝ) + 1) ≤ arcRadius B₅ H := by
    have hstep : (H : ℝ) / arcDen B₅ H ≤ (Q' : ℝ) + 1 := by linarith
    have hpos : (0 : ℝ) < (H : ℝ) / arcDen B₅ H := div_pos hHpos hdpos
    have hinv := one_div_le_one_div_of_le hpos hstep
    rw [one_div_div] at hinv
    exact hinv
  obtain ⟨a, q, hlarge, hqQ', hd⟩ := exists_large_den_of_not_nearRat hQ'pos hfine hnot
  refine ⟨a, q, hlarge, hqQ', hd.trans ?_⟩
  -- `1/(q(Q'+1)) ≤ (log H)^{B₅}/(qH)`, since `Q'+1 ≥ H/(log H)^{B₅}`.
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℝ) ≤ arcDen B₅ H := hdpos.le
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hstep : (H : ℝ) ≤ ((Q' : ℝ) + 1) * arcDen B₅ H := by
    rw [div_le_iff₀ hdpos] at hceil
    linarith
  nlinarith [hqpos, hdpos]

/-! ## Stone 4 — the `Ξ_H` interface (verbatim transplants)

`Salt/Entropy/Chowla/CircleMethod.lean` keeps its `Ξ_H` membership lemma and its
trivial `S_H` bound `private` (`:351`, `:371`), so both are re-derived here — the
proofs are the source proofs byte-for-byte. -/

/-- **`Ξ_H` membership** (transplant of the `private` `CircleMethod.lean:371-375`):
`ξ ∈ Ξ_H` iff the exponential sum at `−ξ/H` clears the threshold `ε²/log H`. -/
theorem mem_bigXi_iff {eps : ℚ} {H : ℕ} [NeZero H] {ξ : ZMod H} :
    ξ ∈ bigXi eps H ↔
      (eps : ℝ) ^ 2 / Real.log (H : ℝ) ≤ ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ := by
  unfold bigXi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The contrapositive entry**: a sub-threshold exponential sum evicts `ξ` from
the large spectrum.  This is the door through which every minor-arc estimate
reaches `Ξ_H`. -/
theorem not_mem_bigXi_of_norm_lt {eps : ℚ} {H : ℕ} [NeZero H] {ξ : ZMod H}
    (h : ‖expSum eps H (-(ξ.val : ℝ) / (H : ℝ))‖ < (eps : ℝ) ^ 2 / Real.log (H : ℝ)) :
    ξ ∉ bigXi eps H := fun hξ => absurd (mem_bigXi_iff.mp hξ) (not_le.mpr h)

/-- **The trivial bound** (transplant of the `private` `CircleMethod.lean:351-361`):
`‖S_H(α)‖ ≤ ∑_{p ∈ 𝒫_H} 1/p`, each phase having modulus one. -/
theorem norm_expSum_le_sum {eps : ℚ} {H : ℕ} [NeZero H] (α : ℝ) :
    ‖expSum eps H α‖ ≤ ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℝ)) := by
  unfold expSum
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hone : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((p : ℕ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((p : ℕ) : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero]
  rw [hone, mul_one]

/-- **The trivial arm of the threshold**: membership in `Ξ_H` forces the
threshold `ε²/log H` below the total prime mass `∑_{p ∈ 𝒫_H} 1/p`.  (By the
prime number theorem that mass is `≍ 1/log H`, so the threshold is a *constant
proportion* `≍ ε²` of the trivial bound — this is why `Ξ_H` is a genuine
large-spectrum set and Tao's Lemma 3.5 is not vacuous.) -/
theorem threshold_le_sum_inv_of_mem {eps : ℚ} {H : ℕ} [NeZero H] {ξ : ZMod H}
    (hξ : ξ ∈ bigXi eps H) :
    (eps : ℝ) ^ 2 / Real.log (H : ℝ) ≤ ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℝ)) :=
  (mem_bigXi_iff.mp hξ).trans (norm_expSum_le_sum _)

/-! ## Stone 5 — the prime-window normalisation (the frame of ladder rung L1)

`𝒫_H` is the **dyadic** window `(ε²H/2, ε²H]` (`PrimeWindow.lean:26`), so every
weight `1/p` occurring in `S_H(α)` is within a factor `2` of `1/(ε²H)`.  That is
exactly what lets rung L1 strip the weight by partial summation and reduce to the
unweighted prime exponential sum `∑_{p ≤ ε²H} e(αp)` that Vinogradov's estimates
speak about. -/

/-- The window bounds `ε²H/2 < p ≤ ε²H`, transported from `ℚ` to `ℝ`. -/
theorem primeWindow_bounds {eps : ℚ} {H p : ℕ} (hp : p ∈ primeWindow eps H) :
    (eps : ℝ) ^ 2 * (H : ℝ) / 2 < (p : ℝ) ∧ (p : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
  obtain ⟨hle, _, hlt⟩ := mem_primeWindow.mp hp
  refine ⟨by exact_mod_cast hlt, ?_⟩
  have hnn : (0 : ℚ) ≤ eps ^ 2 * (H : ℚ) := by positivity
  have h1 : ((p : ℕ) : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
    le_trans (by exact_mod_cast hle) (Nat.floor_le hnn)
  exact_mod_cast h1

/-- The window is populated by *positive* integers (a consequence of the lower
window bound, not of primality). -/
theorem pos_of_mem_primeWindow {eps : ℚ} (heps : 0 < eps) {H p : ℕ} (hH : 0 < H)
    (hp : p ∈ primeWindow eps H) : (0 : ℝ) < (p : ℝ) := by
  have hlow := (primeWindow_bounds hp).1
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hden : (0 : ℝ) < (eps : ℝ) ^ 2 * (H : ℝ) := by positivity
  linarith

/-- **The weight is `≍ 1/(ε²H)`, upper half**: `1/p ≤ 2/(ε²H)` on the window. -/
theorem inv_p_le_of_mem {eps : ℚ} (heps : 0 < eps) {H p : ℕ} (hH : 0 < H)
    (hp : p ∈ primeWindow eps H) :
    1 / (p : ℝ) ≤ 2 / ((eps : ℝ) ^ 2 * (H : ℝ)) := by
  have hlow := (primeWindow_bounds hp).1
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hden : (0 : ℝ) < (eps : ℝ) ^ 2 * (H : ℝ) := by positivity
  rw [div_le_div_iff₀ (pos_of_mem_primeWindow heps hH hp) hden]
  linarith

/-- **The weight is `≍ 1/(ε²H)`, lower half**: `1/(ε²H) ≤ 1/p` on the window. -/
theorem le_inv_p_of_mem {eps : ℚ} (heps : 0 < eps) {H p : ℕ} (hH : 0 < H)
    (hp : p ∈ primeWindow eps H) :
    1 / ((eps : ℝ) ^ 2 * (H : ℝ)) ≤ 1 / (p : ℝ) :=
  one_div_le_one_div_of_le (pos_of_mem_primeWindow heps hH hp) (primeWindow_bounds hp).2

/-- **The trivial bound, normalised**: `‖S_H(α)‖ ≤ 2|𝒫_H|/(ε²H)`.  This is
`norm_expSum_le_sum` with the dyadic weight bound applied termwise — the shape
in which rung L1 hands the sum to the unweighted theory. -/
theorem norm_expSum_le_card {eps : ℚ} (heps : 0 < eps) {H : ℕ} [NeZero H] (α : ℝ) :
    ‖expSum eps H α‖ ≤ 2 * ((primeWindow eps H).card : ℝ) / ((eps : ℝ) ^ 2 * (H : ℝ)) := by
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  refine (norm_expSum_le_sum α).trans ?_
  calc ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℝ))
      ≤ ∑ _p : primeWindow eps H, (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) :=
        Finset.sum_le_sum (fun p _ => inv_p_le_of_mem heps hH p.2)
    _ = 2 * ((primeWindow eps H).card : ℝ) / ((eps : ℝ) ^ 2 * (H : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]
        ring

/-! ## Stone 6 — THE REDUCTION

After this stone the frozen target is *exactly* the minor-arc estimate: no
bookkeeping remains on the `Ξ_H` side. -/

/-- **`bigXi_arc` from the minor-arc estimate.**  The contrapositive of the
frozen row: if the weighted prime exponential sum drops below the `Ξ_H`
threshold off the major arcs, then every large-spectrum frequency is major.

The sign seam is `nearRat_neg`: the threshold lives at `−ξ.val/H`, the target at
`ξ.val/H`. -/
theorem bigXiArc_of_minorArc {B₅ : ℝ} (h : MinorArcBound B₅) : BigXiArc B₅ := by
  intro eps heps
  obtain ⟨H₀, hH₀⟩ := h eps heps
  refine ⟨H₀, ?_⟩
  intro H _ hle ξ hξ
  by_contra hcon
  have hneg : ¬ NearRat (arcDen B₅ H) (arcRadius B₅ H) (-(ξ.val : ℝ) / (H : ℝ)) := by
    rw [neg_div, nearRat_neg]
    exact hcon
  exact absurd (mem_bigXi_iff.mp hξ) (not_le.mpr (hH₀ H hle _ hneg))

/-- **The `ξ = 0` instance of the frozen target**, unconditionally.  Recall
`0 ∈ Ξ_H` always (`MRTDoor.lean:106`), so the target's first instance is never
vacuous — and it is discharged with no analysis at all, `0` being `0/1`. -/
theorem nearRat_arc_zero {B₅ : ℝ} (hB : 0 ≤ B₅) {H : ℕ} (hH : 3 ≤ H) :
    NearRat (arcDen B₅ H) (arcRadius B₅ H) (((0 : ZMod H).val : ℝ) / (H : ℝ)) := by
  rw [ZMod.val_zero]
  simpa using nearRat_zero (one_le_arcDen hB hH) (arcRadius_pos hB hH).le

/-- **Staged-gate robustness**: the frozen target only *weakens* as the exponent
grows, so a staged pin at any exponent above a proven one is free.  This is the
insurance the "exponents STAGED-GATED" clause of the frozen row asks for. -/
theorem bigXiArc_mono {B₅ B₅' : ℝ} (hBB : B₅ ≤ B₅') (h : BigXiArc B₅) :
    BigXiArc B₅' := by
  intro eps heps
  obtain ⟨H₀, hH₀⟩ := h eps heps
  refine ⟨max H₀ 3, ?_⟩
  intro H _ hle ξ hξ
  have hle₀ : H₀ ≤ H := le_trans (le_max_left _ _) hle
  have hH3 : 3 ≤ H := le_trans (le_max_right _ _) hle
  exact nearRat_mono (arcDen_mono hBB hH3) (arcRadius_mono hBB hH3) (hH₀ H hle₀ ξ hξ)

end Salt.MR

end
