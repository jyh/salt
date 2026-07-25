# HU-SCOPE — the §8.3 interior priced (2026-07-24 night; read-only recon)

*The hU ladder for the seam row's second binder. GO on 6 of 8 stones; the
full report's key content banked here (the agent transcript is ephemeral).*

## 1. THE DEFINITION AUDIT: CLEAN — no statement-tier gate

Uset (Decomp:231) unfolds to "for every j, SOME sub-block is LARGE" —
verbatim MR p.24's 𝒰. The feared thinness-direction mismatch was a
double-negation misreading. §8.3 consumes exactly ONE 𝒰-property (at j = J,
Step 3); everything else is 𝒰-agnostic. Two repairable deviations + one
unrecorded constraint:
- **D1**: our block family = ALL subintervals (⊇ MR's H-log windows) — our
  𝒰 is larger, hU harder; repair = dyadic-refine the witness + union bound
  (cost X^{o(1)}) [B/C, 300–500].
- **D2**: single δ vs MR's v-graded threshold — NOT needed for hU;
  **PIN: δ := P_J^{−α_J}** (the sup of MR's graded threshold) — then a
  future v-graded 𝒰′ ⊆ 𝒰 and today's hU transfers verbatim; the graded
  variant lands later as a NEW def; Tset never re-pinned. (The E_j/𝒯 rows
  need the grading; that lives outside hU.)
- **D3 (the trap)**: Lemma 12's hcoef holds in §8.3 ONLY because the L12
  window sits strictly above every 𝒰-block (Q_J < P_L12). The
  instantiation must carry **Qseq j < P_L12 ∀ j ≤ Jb** or hcoef is FALSE.

## 2. THE VACUITY CATCH: lemma12_meansq is unconditional but USELESS at grade

The landed herr discharge (ramWindowErr_moment_triv — the 2T·windowMass²
trivial-sup row) is kernel-valid and off the needed grade by ≈ X·H·(logX)²
(windowMass is the ℓ¹ mass, no cancellation). MR p.20's actual mechanism:
collect the over/under-count AT THE FREQUENCY LEVEL as Σ d_m/m^s over the
two narrow windows with d_m BOUNDED (because ramare_weight_sum = 1), then
MVT. **U-2a is that restructuring [C, 400–700]; the trivial row gets a
superseded flag when U-2a lands (never deleted).** Naive per-frequency CS
loses (logX)^θ — refused.

## 3. THE STRUCTURAL HEADLINE: hU is NOT independent of hSup

L3-for-R (the pointwise co-factor bound) is NOT B-ladder-suppliable (the
co-factor is dyadic, Ramaré-weighted, 1_S-restricted — the same
object-category wall as SEAM-SCOPE §2). Its Halász core = the hSup frontier
(H-4/H-6) + the partial-summation bridge. Landed helpers: smooth_rough_split
(MultShiu:1280) is the n₁n₂ bijection verbatim; Mertens gives logQ/logP.
Missing besides the shared frontier: the Rankin Q-smooth count [C, 300–500].
**The seam row's two named binders converge on ONE open supply.** U-7 HELD.

## 4. hZ UPGRADED: a genuine socket whose analytic core is LANDED

No unconditional L9 exists (VanDerCorput exports only the small/large-|u|
sockets). hZ cannot be routed around (L9's |𝒯|√T is the mechanism that
beats Q = X^{o(1)}). BUT the middle band 1 ≤ |u| ≤ N² is assembly:
vdC_second_derivative (VdCorput2:140, general) + zeta_block_strip's proof
STOPS ONE STEP EARLY (hlb/hub never use t ≤ 27πU — verified) giving the
all-t block bound ~40–60 ln; then three-range assembly → the socket shape
N/u + √u·log u. **[C, 600–1000, fully parallel, zero design risk.]**

## 5. THE DECISIVE NUMERIC — the ρ question (COUNCIL ITEM, blocks U-9 only)

The balance θ = ρ/3 (reconstruction reproduces MR's 1/48 exactly — verified):
- ρ = 1/(32e) (B4, the un-halved Halász-direct route): ∫_𝒰 exponent
  1/261 ≈ 0.00383 — **PASSES c₀ ≥ 1/500 with margin 1.92×**.
- ρ = 1/(64e) (post-S-3 halving): 1/522 ≈ 0.00192 — **FAILS by 4.2%**
  (and the o(1) loses a loglog here — the miss is real).
**THE LEVER**: S-3's halving comes from MRT A.13/A.14's square root INSIDE
the ball/hSup argument. L3 uses Halász's theorem DIRECTLY (Lemma-1 form,
c = 1/e un-halved). If the halving is route-specific, the L3 arm keeps
1/(32e) and §8.3 passes with margin. **The council must scope S-3: the
re-freeze applies to the BALL leg only; the L3/§8.3 arm keeps the un-halved
grade.** (hsup-design:116's "margin 3–30×" was the BALL's ledger; the §8.3
÷3 was not in it.)
Corners, all pass: 𝒯_L kill margin ~33× at the frozen VK β = 3/4; 𝒯_S → 0;
δ′ = (logX)^{−3} suffices (MR's 100 lavish). **X₀ LOUD**: large_value_count's
hκ30 forces X ≥ exp(30^{3/ρ}) ≈ exp(10^{386}) — finite, existential-posture
harmless, dominates every other threshold, multiplies the door's X₀.

## 6. The ladder + tonight's dispatch

U-1 [B,150] L12-on-subset; **U-2a [C,400–700] the honest herr (WAVE A —
dispatched tonight)**; U-2b [B,150–250]; U-2c [A,~30 with the
support-carries-block-condition pin, else C]; U-3 [C,250–450] the
well-spaced discretization (∃-above-average route, no sup-attainment — 𝒰
is open); U-4 [B/C,300–500] thinness via L8 + D1 adapter (+ the
dpoly = P(1−it) sign catch); U-5 [B,200–300] 𝒯_S (blocked on hZ);
**U-6 [C,600–1000] hZ (WAVE C — dispatched tonight)**; U-7 HELD (shares
the hSup frontier); U-8 [C,400–600] 𝒯_L via the landed halasz_primes_pow +
the 1/v gain (prime_count_Ioc_le + psiTot_pnt supply it [B,150–250]);
U-9 [B/C,300–500] the balance (BLOCKED on the council's ρ ruling).
**Total ≈ 3.5–5.5k C-tier** (the earlier 1–2k estimate was low ~3×).
Waves B (U-3/U-4/U-1, needs the D2/D3 pins ratified) + the rest: post-council.

Refused supplies recorded: lemma12_meansq-as-it-stands for Step 1; the
B-ladder for L3; the landed VanDerCorput for hZ.
