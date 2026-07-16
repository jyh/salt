# S3-A-R1 DESIGN FREEZE — the entropy library port (Salt.Entropy)

**Status: FROZEN (house, 2026-07-17 ~15:10) — PENDING GATE.**
The freeze ADOPTS VERBATIM the A-R0 recon's §5 spec (ledger ~14:50;
the recon report is the authoritative annex): port PFR's clean
Shannon core (PFR/ForMathlib/Entropy/: Measure → Basic →
Kernel/Basic → Kernel/MutualInfo, ~4k lines, Apache-2.0, attribution
preserved) into Salt/Entropy/, keeping PFR's names and notation
(Hm[·], H[X ; μ], H[X | Y ; μ], I[X : Y ; μ], I[X : Y | Z ; μ]) and
the scaffolding typeclasses (FiniteRange, FiniteSupport).

Frozen API (= the paper's (3.1)–(3.7), PFR names): chain_rule;
condEntropy_le_entropy; entropy_pair_le_add; mutualInfo_nonneg +
mutualInfo_eq_entropy_sub_condEntropy; condMutualInfo_nonneg +
conditional-pair subadditivity; entropy_le_log_card; entropy_nonneg;
entropy_comp_le; measureEntropy_dirac/prod.

Wave 1 (4 executors, per the recon): W1-1 scaffolding typeclasses
vs current mathlib kernels; W1-2 Measure.lean defs +
nonneg/zero/dirac; W1-3 measureEntropy_le_log_card + prod; W1-4
Kernel/Basic front half. Per-node acceptance: lake build + axiom
audit + THE CONSUMER TEST (a Scratch-level derivation of one
Section-3 inequality must stay compiling each wave — the port aims
at Lemma 3.1, not PFR's downstream).

Case space (III.3‴): mathlib-version drift per file × the
PFR-local scaffolding dependencies × the Ruzsa/group layer
EXCLUSION boundary (droppable, must not leak in) × notation
collisions (μH[d] Hausdorff) × license/attribution headers.

Gate charge: (1) verify the PFR source files' actual current
content vs the recon's inventory (fetch raw files; the port list
complete, the exclusion boundary clean); (2) the consumer test's
target inequality chosen and its API needs covered by the frozen
list; (3) mathlib-drift risk per file (which kernels/typeclasses
moved since PFR's mathlib pin); (4) license/attribution
correctness; (5) the wave-1 cut is genuinely parallel (no
same-file collisions).

## GATE VERDICT (2026-07-17 ~16:30): GO-WITH-AMENDMENTS — applied

S3-A1-GATE (≈ 67k / 19 tools; PFR pinned at commit a177b2e4, drift
LOW — one rc from salt's v4.32). Four amendments, binding:

- **A1 (dependency closure).** The freeze's "no hidden intra-PFR
  deps" was FALSE: true closure ≈ 4,935 lines incl. six
  PFR.Mathlib.* patch residues + two ForMathlib helpers. RULING:
  the FROZEN-SUBSET port — the ~9 frozen lemmas + transitive
  closure; Uniform (311) + ConditionalIndependence (295) DROPPED
  (unreachable from the frozen API); the Disintegration/Comp patch
  subset (948+207, the kernel chain_rule's path) KEPT and re-tiered
  C.
- **A2 (drift).** LOW, one-rc; header conversion = class-A
  `import Mathlib`; the kernel-glue nodes are C, the rest honest B.
- **A3 (attribution).** No inline headers exist upstream —
  attribution CONSTRUCTED per the gate's verbatim header block
  (PFR contributors, Apache-2.0, commit pin, modification notice)
  + LICENSE-PFR-Apache-2.0 copy in Salt/Entropy/.
- **A4 (the wave re-cut).** W1-2/W1-3 collided in Measure.lean;
  the corrected cut: W1-1 FiniteRange ∥ W1-P patch residues →
  W1-2 the WHOLE of Measure.lean (one executor) ∥ W1-3 the kernel
  disintegration glue (C) → wave 1.5 Kernel/Basic. Parallelism
  ceiling 2 lanes (the DAG, not the throttle, sets the width).
- Consumer test pinned to the R.V.-level (3.1)/(3.5)/(3.7) triple
  (Basic.lean-only path — stays green before the kernel nodes).

DISPATCH: W1-1+W1-P combined into one executor (house call — both
small, sequential, saves a slot); W1-2 ∥ W1-3 on its landing.
