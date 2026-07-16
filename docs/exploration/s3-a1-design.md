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
