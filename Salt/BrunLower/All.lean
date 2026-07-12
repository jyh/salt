/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BrunLower.Defs
import Salt.BrunLower.LowerMoebius
import Salt.Tactic.AuditAxioms

/-!
# The both-sided Brun sieve rung (`p0`) — aggregate import

Design: `docs/blueprints/p0.md`.  The **possibility-side keystone** of the twin
ladder: the block-truncated Brun sieve of Halberstam–Richert, *A new look at Brun's
sieve*, Mém. SMF **25** (1971) 97–106, Théorème 2 — the tool that will deliver
`Ω(n(n+2)) ≤ 20` for infinitely many `n` (`docs/blueprints/p0.md` §P1).  Fixed-depth
Bonferroni cannot serve this (flags #15); the feasible-λ window and block offset are
those of the primary source read at page-image level, `Λ = 2λ/A` general and offset
`2b − ν + 2n − 1` exact (flags #16).

## Landed (nodes B0 + B1)

`Defs` (B0): the ladder `zLev`/`bigLambda` with the bottom `z_r = 2` and the
minimal-`r` characterisation (2.14); the block predicate `chi` (`χ_ν`, (2.10),
restricted-count form) and its structural rules (2.1)–(2.4) `chi_one`,
`chi_dvd_closed`, `chi_prime`, `chi_add_smaller_prime`; the density product `W`.
`LowerMoebius` (B1): `IsLowerMoebius` and the lower-bound sieve inequalities
`siftedSum_ge_sum_of_lowerMoebius` / `siftedSum_ge_mainSum_errSum_of_lowerMoebius`
— the exact sign-flipped dual of mathlib's upper Selberg plumbing (upstreamable).

**Note (block predicate, load-bearing).** `chi` is the *restricted-count* reading of
(2.10): `∀ n ≥ 1`, `#{p ∣ d : z_n ≤ p} ≤ 2b−ν+2n−1`.  The naive "all-of-`d`" reading
is not divisor-closed (fails (2.2)); the divisibility-window form is recovered only as
the one-way consequence `chi_imp_windowed`.  See `Defs`'s module docstring.
-/

-- Build-time axiom audit: a stray axiom in the `p0` carriers fails `lake build` here.
open Salt.Tactic in
#audit_axioms Salt.BrunLower.zLev_zero Salt.BrunLower.zLev_antitone
  Salt.BrunLower.zLev_le_two_iff Salt.BrunLower.exists_zLev_le_two
  Salt.BrunLower.zLev_minLevel_le_two Salt.BrunLower.exp_minLevel_ge
  Salt.BrunLower.bigOmegaGe_eq_card_iff Salt.BrunLower.chi_imp_windowed
  Salt.BrunLower.chi_one Salt.BrunLower.chi_dvd_closed Salt.BrunLower.chi_prime
  Salt.BrunLower.chi_add_smaller_prime Salt.BrunLower.W_pos
  Salt.BrunLower.siftedSum_ge_sum_of_lowerMoebius
  Salt.BrunLower.siftedSum_ge_mainSum_errSum_of_lowerMoebius
