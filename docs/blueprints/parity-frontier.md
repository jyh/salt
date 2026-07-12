# The parity frontier — scoping memo (possibility side)

*Fable, 2026-07-12. User-requested deliverable: the difficulty map of the
parity frontier, post-`twinbar`. Two-scout recon with sources open (Tao
254A Supp. 5, Halberstam–Richert ch. 11, Polymath8b 1407.4897, the
Siegel-zero literature); primary-PDF caveats noted at the end. Feeds the
roadmap (supersedes `next-rung-scoping.md` Rungs 7–8 detail) and the
writeup.*

## Headline findings

1. **"Chen modulo SW" is well-posed, and its analytic input is exactly
   what we already have.** The qualitative Chen (`p, p+2 = P₂` infinitely
   often) needs only PLAIN Bombieri–Vinogradov at level 1/2 — well-
   factorable/BFI beyond-1/2 machinery is an improvement, not a
   requirement (Tao 254A Supp. 5: `D = x^{1/2−ε}`, standard BV). Our
   `SiegelWalfisz`-gated BV chain delivers precisely that shape. The
   entire remaining difficulty is **sieve-combinatorial, not analytic**,
   and parity-consistent (no wall in the way).
2. **The single greenfield keystone for the whole possibility side: a
   LOWER-bound sieve.** Everything we have (SelbergPort, mathlib's
   SelbergSieve, the Maynard weights) is upper-bound Λ² — confirmed by
   source inspection. Two tiers:
   **Tier A** — Brun-style combinatorial both-sided fundamental lemma
   (Bonferroni/Buchstab truncation, loose constants); reuses
   `Salt/Brun`'s M2–M6 inclusion-exclusion; est. ~20–35 nodes.
   **Tier B** — the sharp Rosser–Iwaniec linear sieve (optimal `F(s)`,
   `f(s)` via delay-differential equations + Buchstab iteration); est.
   ~40–70 nodes, genuine C-track. Chen's razor margin
   `log 3 − ½·log 6 ≈ 0.203` sits at `s = 4`, the edge of `f > 0` —
   sharpness is load-bearing, so Chen needs Tier B.
3. **The gate question resolves with a famous caveat.** No conjecture
   with a believed-true (or even undecided-plausible) antecedent is known
   to imply twin primes — EH gives 12, GEH gives 6, parity provably
   floors sieve methods at 6; Chowla/Sarnak live on the Liouville side
   with ZERO partial transfer to von Mangoldt; Dickson/Schinzel/
   Bateman–Horn contain twins (vacuous as gates). **BUT: Heath-Brown
   (1983): infinitely many Siegel zeros ⇒ infinitely many twin primes**
   — a genuine conditional twin-prime theorem whose hypothesis is
   believed FALSE. Kernel-checked it would read: *"twin primes, OR no
   Siegel zeros — at least one."* A live sub-field (three separate
   2021–22 quantitative strengthenings). Formalizing needs
   exceptional-character/L-function machinery the corpus entirely lacks:
   **document as the roadmap's honest gate; do not attempt in an
   automated loop.**

## The possibility ladder (all numbers ESTIMATES; Brun ≈ 27 nodes = 1 unit)

| rung | statement | needs | est. | verdict |
|---|---|---|---|---|
| P0 | both-sided fundamental lemma, Tier A — ⚠️ DESIGN-CORRECTED (P0 recon 2026-07-12): must be the BLOCK-truncated Brun pair (H-R 1971 Thm 2; Rademacher–Tartakovskij lineage) — fixed-depth Bonferroni provably CANNOT serve P1 (tail swamps V(z) at κ=2; K degenerates to loglog). Reuse corrected: M2/CongruenceCounting/Sieve.lean verbatim + Maynard's Mertens (the sleeper find), but M1/M3's Selberg-Λ² core transfers NOTHING — the χ± combinatorial heart is greenfield; mathlib's missing `IsLowerMoebius` is the cheapest structural node. Constants MUST be transcribed from the numdam PDF pre-freeze. | ~15–18 nodes (recon-refined) | the reusable keystone; unlocks P1 |
| P1 | **elementary twin-almost-prime `Ω(n(n+2)) ≤ K`** (pair-form; tuned classical {7,7} ⇒ K=14; accept ≤ 30 as floor — stated in Ω, multiplicity) | P0 only — dimension-2, elementary error (`Στ(d) ≤ D(1+logD)`), Mertens discharges the block-density hyp | ~8–10 nodes on top of P0 (recon-refined) | **the cheapest honest possibility rung** |
| P2 | sharp Rosser–Iwaniec linear sieve (Tier B) | greenfield C-track | ~40–70 nodes | the enabling investment for P3/P4 |
| P3 | `p` prime, `p+2 = P₃`, modulo SW | P2 + the EXISTING gate (no switching needed at P₃) | ~15–25 on top of P2 | first one-sided prime-almost-prime |
| P4 | **CHEN modulo SW** (`p+2 = P₂`) | P2 + the switching principle (~40–60 nodes, C-keystone; bilinear sums structurally adjacent to our Vaughan Type-II) + the 0.203-margin assembly | ~2–3 Maynard-scale cumulative | the capstone; roadmap Rung 7 confirmed feasible-in-principle with our analytics |
| — | Heath-Brown Siegel-zero conditional | L-function/exceptional-character stack (absent) | research-scale | document-don't-attempt; the unique honest gate |

## Attribution/precision guards (for the writeup)
- EH → 12, GEH → 6, parity floor = 6: all Polymath8b (1407.4897); never
  say "6 under EH."
- The Siegel-zero strengthenings: Tao–Teräväinen (2021, asymptotics/
  Goldbach/short intervals) vs the other 2021–22 papers — do not
  conflate; pull primary PDFs before quoting exact statements
  (this recon rested on Tao's expositions + abstracts for the
  paywalled originals).
- "Zero partial transfer" (Liouville → von Mangoldt) is a synthesis of
  the parity-problem framing, not a single quotable theorem — frame it
  as such.
- Chen numerics: `A₁ ≥ (log 3 − o(1))·…` via `f(4)`, `ΣA₂,ₚ ≤ (log 6 +
  o(1))·…` via `F`, switching for `A₃`; margin `log 3 − ½ log 6 > 0`.
