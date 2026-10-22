# salt

A formal mathematics project in Lean 4 / mathlib. **Objective: a machine-checked
proof of the Twin Prime Conjecture.**
<!-- claim-check: not-a-claim: states the objective; nothing is claimed achieved here, and the paragraphs below say what is -->

The conjecture is open, and the known method class (sieve theory) provably cannot
close it — Polymath8b showed gaps ≤ 6 is optimal for sieve-theoretic arguments even
under the generalized Elliott–Halberstam conjecture. So the project runs two layers:

1. **The ladder (formalization spine).** Formalize the known frontier, bottom-up:
   Brun's theorem → Siegel–Walfisz and the large sieve (the two axioms the
   existing Lean Bombieri–Vinogradov formalization declared; by the 2026-08-17
   survey only Siegel–Walfisz remained one, rows 2 and 7) → unconditional B–V → GPY →
   Maynard–Tao ("gaps ≤ 600", then Polymath8b's 246) → the conditional results
   (EH → 12, GEH → 6) → the parity obstruction itself. Some rungs have public
   formalizations elsewhere (Lean Bombieri–Vinogradov modulo a Siegel–Walfisz
   axiom; AxiomMath's PrimeGapsLib for Maynard–Tao),
   so the README makes no priority claim for the ladder. Dated, per-rung priority
   statements are in `docs/priority-survey-2026-08-11.md` and its 2026-08-17
   re-run, `docs/priority-survey-2026-08-17-delta.md`; neither has been re-run
   since. The corpus is meant to be useful even if the summit is never reached.
2. **The hunt (research layer).** A barrier atlas (precise statements of why each
   known approach fails), a reduction DAG of candidate statements, and systematic
   <!-- claim-check: not-a-claim: a published human proof in the literature, not a machine-verification claim -->
   search on the live routes: function-field transfer (Sawin–Shusterman proved the
   conjecture in 𝔽_q[T]), parity-breaking bilinear input for n(n+2), and the
   Chowla-program gap (Liouville/log-averaged → von Mangoldt).

`Salt/Basic.lean` states the target formally (`TwinPrimeConjecture`). The project
succeeds when a theorem of that type exists.

As of 2026-09-07, `Salt/HB/CrownTheorem1.lean` carries a machine-checked proof of
Heath-Brown's dichotomy, `HeathBrownDichotomy = TwinPrimeConjecture ∨ NoSiegelZeros`,
conditional on one open hypothesis: `N7Exit` (Heath-Brown's Lemma 5), which the
theorem takes as a binder and the corpus does not prove. Neither arm of the
dichotomy is decided in this corpus, so this is not a proof of the twin prime
conjecture. The
constants are not effective: the chain uses Siegel's ineffective threshold, and
B2's log-free density constant `n9CB2` is a `Classical.choose`.

*Dated 2026-10-22.* OpenAI's preprints dated 2026-09-30 and 2026-10-01 (published with
Lean sources at `github.com/openai/math` from 2026-10-06) claim that no Dirichlet
L-function has a zero with real part above 7/8, and that there are no Siegel zeros.
The Lean proof of the 7/8 claim was kernel-checked on our machine, 2026-10-22, from
OpenAI's pinned source (`openai/math` 1581d4cbdd69): the full environment of 561,427
declarations replayed by `leanchecker --fresh`, and the theorem depends on the three
standard axioms only (`#print axioms`). The statement was matched by elaboration, not
by OpenAI's comparator; OpenAI's 23 patches to third-party packages were applied as
their build applies them, and their content was not read (mathlib is not patched); and
this checks their Lean proof, not the preprint's argument. The steps of that run are
written down, with two changes, as `scripts/replay_openai_seven_eighths.sh`, which
has not itself been run end to end yet. This repository does not import that proof. It
restates the 7/8 statement over its own mathlib as `DirichletSevenEighths` and proves
that it implies `NoSiegelZeros` (`noSiegelZeros_of_sevenEighths`, in
`Salt/TwinBar/SevenEighthsClaim.lean`). Whether OpenAI's mathlib (`d13f23b7`) and this
repository's define the L-function identically has not been checked yet, so OpenAI's
theorem does not discharge `DirichletSevenEighths` here. If `DirichletSevenEighths`
holds, it decides the `NoSiegelZeros` arm: the dichotomy then holds outright, without
the `N7Exit` binder (`N7Exit` itself stays open), and says nothing about twin primes.

## Trust policy

- Everything on `main` compiles: `lake build` kernel-checks every proof.
- No `sorry` on `main`.
- No axioms beyond mathlib's standard three (`propext`, `Quot.sound`,
  `Classical.choice`); in particular **no `native_decide`** — numerical
  certificates (e.g. Maynard-type variational bounds) go through formalized
  interval arithmetic, keeping the trusted base at the kernel.
- Statements are reviewed by humans; proofs are reviewed by the kernel. This is
  what makes large-scale AI-generated proof work safe to accept.

## Development

```sh
# one-time setup
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
lake exe cache get   # download precompiled mathlib (~7 GB)

# build (kernel-checks everything)
lake build
```

## GitHub configuration (template setup, once)

* Settings → Actions → General: check **Allow GitHub Actions to create and
  approve pull requests** (used by the mathlib auto-update workflow).
* Settings → Pages: set **Source** to "GitHub Actions" (used for docs, later).
