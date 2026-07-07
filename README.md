# salt

A formal mathematics project in Lean 4 / mathlib. **Objective: a machine-checked
proof of the Twin Prime Conjecture.**

The conjecture is open, and the known method class (sieve theory) provably cannot
close it — Polymath8b showed gaps ≤ 6 is optimal for sieve-theoretic arguments even
under the generalized Elliott–Halberstam conjecture. So the project runs two layers:

1. **The ladder (formalization spine).** Formalize the known frontier, bottom-up:
   Brun's theorem → Siegel–Walfisz and the large sieve (the two axioms of the
   existing Lean Bombieri–Vinogradov formalization) → unconditional B–V → GPY →
   Maynard–Tao ("gaps ≤ 600", then Polymath8b's 246) → the conditional results
   (EH → 12, GEH → 6) → the parity obstruction itself. Every rung is a first-ever
   formalization; the corpus is a landmark contribution even if the summit is
   never reached.
2. **The hunt (research layer).** A barrier atlas (precise statements of why each
   known approach fails), a reduction DAG of candidate statements, and systematic
   search on the live routes: function-field transfer (Sawin–Shusterman proved the
   conjecture in 𝔽_q[T]), parity-breaking bilinear input for n(n+2), and the
   Chowla-program gap (Liouville/log-averaged → von Mangoldt).

`Salt/Basic.lean` states the target formally (`TwinPrimeConjecture`). The project
succeeds when a theorem of that type exists.

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
