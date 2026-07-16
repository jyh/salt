/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.FiniteRange
import Salt.Entropy.Mathlib.MeasureDirac
import Salt.Entropy.Mathlib.MeasureReal
import Salt.Entropy.Mathlib.UniformOn
import Salt.Entropy.Mathlib.ConditionalProbability
import Salt.Entropy.Mathlib.SetCard
import Salt.Entropy.Mathlib.MeasureProd
import Salt.Entropy.Mathlib.LebesgueBasic
import Salt.Entropy.Mathlib.LebesgueCountable
import Salt.Entropy.Mathlib.KernelComp
import Salt.Entropy.Mathlib.KernelDisintegration
import Salt.Entropy.Measure
import Salt.Entropy.Kernel.Basic
import Salt.Entropy.ConsumerTest
import Salt.Tactic.AuditAxioms

/-!
# The entropy library (sprint-3 A-R1) — aggregate import

The discrete Shannon entropy library, ported from the PFR project
(github.com/teorth/pfr, commit a177b2e4, Apache-2.0 — see
`LICENSE-PFR-Apache-2.0` and the per-file attribution headers) per
`docs/exploration/s3-a1-design.md` and its gate verdict.  Wave 1
(scaffolding + patch residues) landed 2026-07-17; waves extend this
file as they land (Measure → kernel glue → Basic → Kernel).

Consumer target: the entropy toolkit (3.1)–(3.7) of Tao,
arXiv:1509.05422 (the entropy decrement argument, rung A-R2).
-/

-- Build-time axiom audit: a stray axiom in the entropy track fails
-- `lake build` here.
open Salt.Tactic in
#audit_axioms FiniteRange.real_full FiniteRange.null_of_compl
  MeasureTheory.Measure.dirac_real_apply'
  MeasureTheory.Measure.prod_real_singleton
  ProbabilityTheory.uniformOn_real_singleton
  ProbabilityTheory.cond_real_apply
  ProbabilityTheory.measureEntropy_le_log_card
  ProbabilityTheory.measureEntropy_dirac
  ProbabilityTheory.measureEntropy_prod
  ProbabilityTheory.measureMutualInfo_nonneg
  ProbabilityTheory.Kernel.entropy_compProd
  ProbabilityTheory.Kernel.chain_rule
  ProbabilityTheory.Kernel.disintegration
  ProbabilityTheory.Kernel.condKernel_prod_ae_eq
