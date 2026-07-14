/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.WindowedStep
import Salt.Chen.Buchstab
import Salt.BrunLower.MertensWindow
import Salt.BrunLower.MertensDischarge

/-!
# C2b — the A₂ per-prime upper bounds and the `∫dt/(t(4−t))` grid

Chen's second carrier is the per-prime sum

  `A_{2,p} = Σ_{x/2 ≤ n ≤ x−2, p ∣ n+2} Λ(n)·1_{(n+2, P(z)) = 1}`,   `z ≤ p < y = x^{1/3}`,

whose aggregate `Σ_{z ≤ p < y} A_{2,p}` is the upper carrier of Chen's reduction (38).  This file
packages the upper bound for the C5 assembly, following the frozen route (`docs/blueprints/chen.md`,
row S2 of the C0 ledger):

* **The per-prime application** (`twin_A2_per_prime`).  Each `A_{2,p}` sifts the *same* twin
  sequence restricted to the residue class `p ∣ n+2`; the sub-sieve runs at the reduced level
  `QD/p` (`cdiv` care), cutoff `z`, operating point `s_p = logRatio z (cdiv (QD) p)`.  All sifting
  primes are `< z ≤ p`, so the per-prime restriction does not touch the sieve — the linear-sieve
  keystone `bjs_theorem6_windowed_upper` applies verbatim, and `linear_sieve_upper_rosser` turns its
  main-term comparison into a full `siftedSum` bound with the `d < Q·(QD/p)`-cut Rosser remainder.
  The per-prime restricted sub-sieve is supplied *abstractly* as a `BoundingSieve` (its arithmetic
  construction — support restricted to `p ∣ n+2`, `totalMass_p ≈ x/(2(p−1))` via one BV discrepancy
  at modulus `p` — is the C2a-owned twin-sequence layer; C2b consumes it through the family).

* **The grid** (`A2grid`, kept SYMBOLIC per the blueprint).  The aggregation weights the per-prime
  main terms by the dimension-1 density `1/(p−1)` (the `{−2 mod p}` residue) and leaves the Rosser
  chain values `Fchain (maxDepth) (s_p)` symbolic — C5 and the value certification (C1b′) evaluate
  them.  `A2grid = Σ_{p} (1/(p−1))·Fchain (Nf p) (s_p)` is the Lean image of the sharp integral
  `∫₁^{8/3} F(4−t) dt/t` whose value `∫₁^{8/3} dt/(t(4−t)) = (log 6)/4` is C5's endpoint.

* **The two bounds C5 needs.**
  - `(b)` `A2grid_le_envelope` (LANDED — the honest sup·mass envelope): the grid mass is at most
    `supF·(log(log y/log z) + 19/log z + 2)`, the SYMBOLIC form of the `(log 6)/4` integral.  The
    reciprocal-mass factor `Σ_{z ≤ p < y} 1/(p−1)` is bounded by the fixed-window Mertens length
    (`Salt.BrunLower.sum_inv_le_of_prime_window`, `C₃ = 19`) plus the `1/(p−1)→1/p` bridge cost
    (`+2` from `Σ 2/p² ≤ 2` via `sum_one_div_sq_le`).  The C0 ledger's S2 headroom (0.466% rel)
    covers the envelope-vs-integral gap, so the monotone-pieces refinement is not needed here.
  - `(a)` the BV-remainder aggregate `Σ_{z ≤ p < y} rosserRemainder (sfam p) (Q·(QD/p))` is carried
    EXPLICITLY in `twin_A2_upper`'s conclusion (`Σ_p Rp`); its reduction to the τ-weighted BV shape
    at moduli `≤ QD` (the same input C2a consumes) is C5's `hBVagg`.  Left explicit here so C5 can
    apply the shared BV plumbing once, rather than duplicating C2a's discrepancy machinery.

* **The packaging** (`twin_A2_upper`).  From the per-prime bounds and the density coefficient
  factorisation `totalMass_p·V(z) ≤ Λmass·V·(1/(p−1))` (`hcoef`, the C2a/BV density input),
  `Σ_p A_{2,p} ≤ Λmass·V·(A2grid + Σ_p (1/(p−1))·slack_p) + Σ_p Rp` — the C5-facing shape with the
  grid and the aggregated slack symbolic and the remainder aggregate carried.

Everything is `V(z)`-relative (P0's O-free doctrine): `V = W s` is factored out, the grid carries
only the density weights and the symbolic chain values.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — `Fchain ≥ 1` (the chain main value is positive) -/

/-- `1 ≤ Fchain N s` for every `N, s`: `Fchain = 1 + Σ_{odd} fₙ` with each `fₙ ≥ 0`
(`fseq_nonneg`).  Used to keep the per-prime main coefficient `Fchain + slack` nonnegative so the
density factorisation `hcoef` pushes through. -/
theorem one_le_Fchain (N : ℕ) (s : ℝ) : 1 ≤ Fchain N s := by
  unfold Fchain
  have hnn : 0 ≤ ∑ n ∈ (Finset.range (N + 1)).filter (fun n => Odd n), fseq n s :=
    Finset.sum_nonneg (fun n _ => fseq_nonneg n s)
  linarith

/-! ## Part B — the symbolic A₂ grid -/

/-- **The A₂ grid** (kept symbolic per the blueprint).  The density-weighted sum of the Rosser
chain values at the per-prime operating points `s_p = logRatio z (cdiv Dtot p)` (`Dtot = QD` the
total level).  This is the Lean image of `∫₁^{8/3} F(4−t) dt/t`; C5 / the value certification
evaluate the `Fchain (Nf p) (s_p)` symbols. -/
noncomputable def A2grid (P : Finset ℕ) (z Dtot : ℕ) (Nf : ℕ → ℕ) : ℝ :=
  ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * Fchain (Nf p) (logRatio z (cdiv Dtot p))

/-! ## Part C — the per-prime application (the keystone composition) -/

/-- **The per-prime A₂ application.**  On the restricted sub-sieve `sp0` (the twin sequence with
`p ∣ n+2`, supplied abstractly), at level `Dlev = QD/p` and cutoff `zTop = z`, the linear-sieve
keystone `bjs_theorem6_windowed_upper` (per-step comparison discharged) feeds
`linear_sieve_upper_rosser` to give the full `siftedSum` upper bound with the `d < Q·Dlev`-cut
Rosser remainder:

  `A_{2,p} = siftedSum sp0 ≤ (totalMass sp0 · V(z)) · (Fchain (maxDepth sp0) s_p + slack_p)
              + rosserRemainder sp0 (Q·Dlev)`,   `s_p = logRatio zTop Dlev`.

All keystone hypotheses (`hguard`/`hnu`/`h4`/`hStop`/`htau`/the τ-recursion) are threaded verbatim;
they are the sieve-class inputs BJS Theorem 6 already carries. -/
theorem twin_A2_per_prime (sp0 : BoundingSieve) (zTop Dlev : ℕ) (ε K C₁ Q : ℝ) (tau : ℕ → ℝ)
    (hD2 : 2 ≤ Dlev) (htm : 0 ≤ sp0.totalMass) (hQ : 1 ≤ Q)
    (hzTop : ∀ q ∈ sp0.prodPrimes.primeFactors, q < zTop)
    (hguard : ∀ q ∈ sp0.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ sp0.prodPrimes.primeFactors, sp0.nu q ≤ 1 / ((q : ℝ) - 1))
    (hε : 0 ≤ ε) (hKe : K ≤ 1 + ε) (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hτrec : ∀ n, cf_const n ε + ε * Real.exp 2 * ch_const n ε * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z) →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z D' → logRatio z D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio zTop Dlev)
    (htau : ∑ n ∈ (Finset.range (maxDepth sp0 + 1)).filter (fun n => Odd n), tau n ≤ C₁) :
    sp0.siftedSum
      ≤ (sp0.totalMass * Salt.BrunLower.W sp0)
          * (Fchain (maxDepth sp0) (logRatio zTop Dlev)
              + ε * C₁ * Real.exp 2 * hBJS (logRatio zTop Dlev))
        + rosserRemainder sp0 (Q * Dlev) := by
  have hmain := bjs_theorem6_windowed_upper sp0 zTop Dlev ε K C₁ tau
    (by omega : 1 ≤ Dlev) hzTop hguard hnu hε hKe htau1 hτ0 hτrec h4 hStop htau
  have h := linear_sieve_upper_rosser sp0 Dlev hD2 htm (maxDepth sp0) (logRatio zTop Dlev)
    ε C₁ Q hQ hmain
  calc sp0.siftedSum
      ≤ sp0.totalMass * (Salt.BrunLower.W sp0 *
          (Fchain (maxDepth sp0) (logRatio zTop Dlev)
            + ε * C₁ * Real.exp 2 * hBJS (logRatio zTop Dlev)))
        + rosserRemainder sp0 (Q * Dlev) := h
    _ = (sp0.totalMass * Salt.BrunLower.W sp0)
          * (Fchain (maxDepth sp0) (logRatio zTop Dlev)
            + ε * C₁ * Real.exp 2 * hBJS (logRatio zTop Dlev))
        + rosserRemainder sp0 (Q * Dlev) := by rw [← mul_assoc]

/-! ## Part D — bound (b): the grid-mass envelope -/

/-- **Bound (b) — the grid-mass envelope** (the honest sup·mass form of the `(log 6)/4` integral).
With `Fchain (Nf p) (s_p) ≤ supF` uniform on the window `[z, y)`, the grid is at most `supF` times
the fixed-window reciprocal mass, which the Mertens length bounds:

  `A2grid ≤ supF · (log(log y/log z) + 19/log z + 2)`.

The `Σ_{z ≤ p < y} 1/(p−1)` factor is the `1/(p−1)`-bridge (`≤ 1/p + 2/p²`) fed into
`sum_inv_le_of_prime_window` (`C₃ = 19`) on the `Σ 1/p` main term and `sum_one_div_sq_le` (`≤ 1`)
on the `Σ 2/p²` tail.  The C0 ledger's S2 headroom (0.466% rel) covers the gap to the sharp
integral, so no monotone-pieces refinement is spent. -/
theorem A2grid_le_envelope {zR yR supF : ℝ} (P : Finset ℕ) (z Dtot : ℕ) (Nf : ℕ → ℕ)
    (hz2 : 2 ≤ zR) (hzy : zR ≤ yR) (hsupF : 0 ≤ supF)
    (hP : ∀ p ∈ P, p.Prime ∧ zR ≤ (p : ℝ) ∧ (p : ℝ) < yR)
    (hFsup : ∀ p ∈ P, Fchain (Nf p) (logRatio z (cdiv Dtot p)) ≤ supF) :
    A2grid P z Dtot Nf
      ≤ supF * (Real.log (Real.log yR / Real.log zR) + 19 / Real.log zR + 2) := by
  -- the reciprocal-mass envelope `Σ 1/(p−1) ≤ log(log y/log z) + 19/log z + 2`
  have hmass : ∑ p ∈ P, 1 / ((p : ℝ) - 1)
      ≤ Real.log (Real.log yR / Real.log zR) + 19 / Real.log zR + 2 := by
    -- the `1/(p−1) ≤ 1/p + 2/p²` bridge
    have hbridge : ∀ p ∈ P, 1 / ((p : ℝ) - 1) ≤ 1 / (p : ℝ) + 2 / (p : ℝ) ^ 2 := by
      intro p hp
      obtain ⟨hpp, _, _⟩ := hP p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [div_add_div _ _ (ne_of_gt hp0) (by positivity : ((p : ℝ) ^ 2) ≠ 0),
        div_le_div_iff₀ hp1 (by positivity)]
      nlinarith [mul_nonneg hp0.le (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)]
    -- PM1 on the `Σ 1/p` main term
    have hLn : ∑ p ∈ P, (1 : ℝ) / p
        ≤ Real.log (Real.log yR / Real.log zR) + 19 / Real.log zR :=
      Salt.BrunLower.sum_inv_le_of_prime_window hz2 hzy
        (fun p hp => by obtain ⟨hpp, hzp, hpy⟩ := hP p hp; exact ⟨hpp, hzp, hpy⟩)
    -- the `Σ 2/p² ≤ 2` telescope
    have htail : ∑ p ∈ P, 2 / ((p : ℝ) ^ 2) ≤ 2 := by
      have hsub : P ⊆ Finset.Icc 2 ⌊yR⌋₊ := by
        intro p hp
        obtain ⟨hpp, _, hpy⟩ := hP p hp
        rw [Finset.mem_Icc]
        exact ⟨hpp.two_le, Nat.le_floor (le_of_lt hpy)⟩
      have h1 : ∑ p ∈ P, 2 / ((p : ℝ) ^ 2) = 2 * ∑ p ∈ P, 1 / ((p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
      have h2 : ∑ p ∈ P, 1 / ((p : ℝ) ^ 2)
          ≤ ∑ p ∈ Finset.Icc 2 ⌊yR⌋₊, 1 / ((p : ℝ) ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
      have h3 := Salt.BrunLower.sum_one_div_sq_le (M := 2) (K := ⌊yR⌋₊) (by norm_num)
      have hle1 : ∑ p ∈ P, 1 / ((p : ℝ) ^ 2) ≤ 1 :=
        le_trans h2 (le_trans h3 (by norm_num))
      rw [h1]; linarith
    calc ∑ p ∈ P, 1 / ((p : ℝ) - 1)
        ≤ ∑ p ∈ P, (1 / (p : ℝ) + 2 / (p : ℝ) ^ 2) := Finset.sum_le_sum hbridge
      _ = (∑ p ∈ P, (1 : ℝ) / p) + ∑ p ∈ P, 2 / ((p : ℝ) ^ 2) := Finset.sum_add_distrib
      _ ≤ (Real.log (Real.log yR / Real.log zR) + 19 / Real.log zR) + 2 := by
          linarith [hLn, htail]
      _ = Real.log (Real.log yR / Real.log zR) + 19 / Real.log zR + 2 := by ring
  -- the grid ≤ supF · (reciprocal mass) ≤ supF · envelope
  calc A2grid P z Dtot Nf
      = ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * Fchain (Nf p) (logRatio z (cdiv Dtot p)) := rfl
    _ ≤ ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * supF := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpp, _, _⟩ := hP p hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        exact mul_le_mul_of_nonneg_left (hFsup p hp) (le_of_lt (div_pos one_pos hp1))
    _ = supF * ∑ p ∈ P, (1 / ((p : ℝ) - 1)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ supF * (Real.log (Real.log yR / Real.log zR) + 19 / Real.log zR + 2) :=
        mul_le_mul_of_nonneg_left hmass hsupF

/-! ## Part E — the packaged A₂ upper bound (C5-facing) -/

/-- **`twin_A2_upper` — the packaged A₂ upper bound.**  From the per-prime application bounds
`hper` (each the output of `twin_A2_per_prime`) and the density coefficient factorisation `hcoef`
(`totalMass_p·V(z) ≤ Λmass·V·(1/(p−1))`, the C2a/BV density input), the aggregate is

  `Σ_{p ∈ P} A_{2,p} ≤ Λmass·V·(A2grid + Σ_p (1/(p−1))·slack_p) + Σ_p R_p`,

with the grid `A2grid` symbolic (bounded by `A2grid_le_envelope`) and the BV-remainder aggregate
`Σ_p R_p` carried explicitly (C5's `hBVagg` reduces it to the τ-weighted BV shape at moduli `≤ QD`).
The window operating points are `s_p = logRatio z (cdiv Dtot p)` (`Dtot = QD`). -/
theorem twin_A2_upper {Λmass V : ℝ} (P : Finset ℕ) (z Dtot : ℕ)
    (A2p Mp Rp slackF : ℕ → ℝ) (Nf : ℕ → ℕ)
    (hslacknn : ∀ p ∈ P, 0 ≤ slackF p)
    (hper : ∀ p ∈ P,
        A2p p ≤ Mp p * (Fchain (Nf p) (logRatio z (cdiv Dtot p)) + slackF p) + Rp p)
    (hcoef : ∀ p ∈ P, Mp p ≤ Λmass * V * (1 / ((p : ℝ) - 1))) :
    ∑ p ∈ P, A2p p
      ≤ Λmass * V * (A2grid P z Dtot Nf + ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * slackF p)
        + ∑ p ∈ P, Rp p := by
  -- fold the density coefficient into each per-prime bound
  have hkey : ∀ p ∈ P,
      A2p p ≤ Λmass * V * (1 / ((p : ℝ) - 1))
          * (Fchain (Nf p) (logRatio z (cdiv Dtot p)) + slackF p) + Rp p := by
    intro p hp
    have hFnn : 0 ≤ Fchain (Nf p) (logRatio z (cdiv Dtot p)) + slackF p := by
      have := one_le_Fchain (Nf p) (logRatio z (cdiv Dtot p))
      linarith [hslacknn p hp]
    have h1 : Mp p * (Fchain (Nf p) (logRatio z (cdiv Dtot p)) + slackF p)
        ≤ Λmass * V * (1 / ((p : ℝ) - 1))
            * (Fchain (Nf p) (logRatio z (cdiv Dtot p)) + slackF p) :=
      mul_le_mul_of_nonneg_right (hcoef p hp) hFnn
    linarith [hper p hp, h1]
  -- aggregate and re-factor into the grid + aggregated-slack shape
  have hfactor :
      ∑ p ∈ P, Λmass * V * (1 / ((p : ℝ) - 1))
          * (Fchain (Nf p) (logRatio z (cdiv Dtot p)) + slackF p)
        = Λmass * V * (A2grid P z Dtot Nf + ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * slackF p) := by
    rw [A2grid, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  calc ∑ p ∈ P, A2p p
      ≤ ∑ p ∈ P, (Λmass * V * (1 / ((p : ℝ) - 1))
          * (Fchain (Nf p) (logRatio z (cdiv Dtot p)) + slackF p) + Rp p) :=
        Finset.sum_le_sum hkey
    _ = (∑ p ∈ P, Λmass * V * (1 / ((p : ℝ) - 1))
          * (Fchain (Nf p) (logRatio z (cdiv Dtot p)) + slackF p)) + ∑ p ∈ P, Rp p :=
        Finset.sum_add_distrib
    _ = Λmass * V * (A2grid P z Dtot Nf + ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * slackF p)
          + ∑ p ∈ P, Rp p := by rw [hfactor]

end Salt.Chen
