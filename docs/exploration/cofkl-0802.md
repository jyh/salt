# COFK-L — the cofactor ask re-priced at the linear door (2026-08-02)

**VERDICT: TRANSFERS.** DELTA-REF's D1 stands at the predicate level (the
L ask is incomparable to the landed ask — no transport bridge exists),
but it is COSTLESS at the supplier level: the intended supplier was
never written at an anchor.

## 1. The route is anchor-general

Both `S16CofactorSupply_gk` (S16Budget.lean:473) and the L twin
(S13CapGateLinear.lean:897) are OPEN — ⟦RULING 9⟧'s debt is unpaid at
BOTH doors; there is one shared debt, not two. The intended supplier
`RbdSupply.m4_supplier_all_chi` (RbdSupply.lean:190, wrapping
CaseAWide.m4_supplier_complete + VkMidSharp.capFreeFloor3_pieceDatum_vt)
has ~30 binders; EXACTLY ONE reads Pseq/Qseq — the Mertens debit
`Σ_{𝒥⊆Icc 1 J} Σ_p 1/p ≤ D`. Everything else reads the Ramaré band,
never the door blocks. No numeral in the route reads the anchor.

## 2. Why the anchor cancels (kernel-checked probe)

`log Q_j = (j²M)·log P_j` — no A, no G (probe_ratio_general +
probe_loglog_diff, lake-green in scratchpad cofkl/ProbeCofkL.lean).
Fed to CofactorDist.blockWindow_mertens_const:
**D ≤ 2·log M + log 4 + 50 — identical at Adoor and AdoorL** (Mertens
errors IMPROVE at the larger anchor).

## 3. The K-free law + the cushion at the L point

Demand (anchor-free, lever-free):
`loglog X_d > 390·λ₊ + 64·log M + 3944 + 32·K_vt`.
Supply (SocketBaseL verbatim, via hPHheadroom): `μ ≥ e^{λ₊} + log(2.7726ε²)`.
COFK's headline `log H ≥ 128·log M + 3400` is this law's ε-free form.

| point | demand | supply | margin |
|---|---|---|---|
| branch (a) loglogFloor50, M=2^103 | 2.81e4 | 5.18e21 | 1.85e17× (COFK ✓) |
| flat/L, A = 162 | 2.22e5 | 10^225 | **10^219.8×** |
| flat/L, A = 2e30 | 2.70e33 | 10^{2.78e30} | 10^{2.78e30}× |

**The cushion GROWS with the anchor** (demand's only M-term is
64·log M ≈ 102.4A, linear; supply is e^{3.2A}). At A=162 the symbolic
K_vt could be as large as 4.3e223 and the law still clears.

## 4. The bridge question, settled

`s16_cofactorSupply_L_of_gk` is un-mintable-by-transport (the socket
bounds ‖ramR‖, not monotone in the indicator; the block families are
non-nested) — but the bridge is NOT the object to build. The right
object: instantiate the supplier DIRECTLY at
Pseq := calP (AdoorL M) …, Qseq := calQK (AdoorL M) … M, J := 2.
Cost split: the L-vs-landed DELTA is **class A** (two symbol
substitutions backed by the kernel probe) + the debit page (~40-60 ln
class B) + the μ-floor compose (~60-100 ln class B). The BULK (the
ladder bundle Mt/kk/Dd/Xa, TLBlockGates34, the Rbd_grade/Cq_gate
register) is anchor-blind and unbuilt at both doors — the L re-cut
adds ZERO to it.

## 5. Honest holes (banked)

1. **K_vt symbolic and unbounded** at both doors (headroom 4.3e223 at
   A=162 — benign unless doubly-exponential; no effective bound
   attempted anywhere).
2. **The μ-floor/upper-cap collision SURVIVES the linear re-cut**: the
   payer μ ≥ e^{λ₊} collides with DoorFuseFrame.gP1 /
   GRowsZeroGate.p2's caps (at AdoorL: ~1.53e5·e^{1.6A} vs e^{3.2A}).
   Not dangerous today (the floor is a theorem, the caps are hypotheses
   of unattempted frames) — but if a future repair LOWERS μ, the weaker
   supply routes are 140×/422× short at the flat point and RULING 9's
   debt becomes a genuine ask. NEW coupling, worth watching.
3. A is symbolic ≥ 162; the verdict holds uniformly over the range.

## Consequence for the accounting

The two carried predicates are BOTH priced after all: base cap
(kernel-weaker, certified) + cofactor (one shared unbuilt supplier,
anchor-blind bulk, delta class A). The endgame arithmetic from council
v5 stands: corollary → the two predicates → both dischargeable.
