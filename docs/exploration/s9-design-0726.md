# The U1/B₅ design block — sieve family, the B₅ pin, the door floor (2026-07-26)

JYH-ratified same evening ("2 — let's do it now"). Inputs: the S9 refuter
verdicts (s9-freeze-0726.md ⟦REFUTER VERDICTS⟧ — U1, U2, the B₅
inconsistency), DoorFloor.lean :30–90, SeamCalibrationK.lean :60–130 + :380–400,
chi-check-0724.md :80–105, door-road-0724.md :40–100. Fable-tier rulings;
refuter pass dispatched on this block before any consumer fires.

## Ruling D-FAMILY — the §4 port runs 𝒮 at the K-LADDER family

U1's tension resolved in the K-family's favor, with the arithmetic:

- At MRT's Prop 2.4 family (P₁ = W^{200}, Q₁ = H/W³) the 1_𝒮-removal cost
  (MR Lemma 2.2) is log P₁/log Q₁ ≈ 200·B₅·loglog H/log H. At the door floor
  (log H ≈ 10^{49}) that is ≈ 10^{−44} — five orders ABOVE δ₀ ≈ 2·10^{−49}
  and ~17 orders above doorGrade = (log H)^{−5/4} ≈ 10^{−61}. The
  MRT-family port can NEVER satisfy the landed doorGrade-shaped socket
  (budget_head_grade_closed): the complement density dominates the grade at
  every scale. This is structural, not a tuning failure — MRT Thm 1.7's own
  stated rate carries the loglog h/log h term for exactly this reason.
- At the K-ladder family the complement is 2/M with M a FREE KNOB
  (sum_ratioK_le, uniform in Jb): choose M ≥ 8/δ₀ and the complement is
  ≤ δ₀/4 — δ-proportional, below the socket. This is why the K-ladder exists.

Consequences (all in-statement per law #253):
1. M4-1's complement route stands as frozen (card_not_memS_le_sum ∘
   sum_ratioK_le ∘ hsieve) — it was already the K-family; the CROSS-WIRE was
   M4-5's side. M4-5 must apply thm_A2′ with 𝒮 := the K-family blocks, and
   A.2's frame re-verified there. The frame checks, sketched (executor
   formalizes): P₁ ≥ (log Q₁)^{800} — log P₁ = calE·log 2 ≈ 10^{58}·0.69 vs
   800·log(4M·calE) ≈ 800·140 ✓ with ~54 orders; Q₁ ≥ P₁ by construction
   (calQK = calP^{j²M}); Q₁ ≤ exp(√log X₀) and √X ≤ X₀ ≤ X re-verified at
   the port's global X (the S9 repair-round wave states them).
2. **[P₁,Q₁] ⊂ [1,h] becomes THE new floor arm**: log Q_{Jb} ≤ log h, i.e.
   log h ≥ Jb²·M·calE·log 2 ≈ (at Jb = 2, M = ⌈8/δ₀⌉) 4·(8/δ₀)·calE·log 2.
   See D-FLOOR.
3. **A new CalFrameK inhabitant is required at the door's M.** The pinned
   calFrameK_satisfiable (A = 65536, G = 2457600, M = 800) has A_gate_logK
   headroom only to M ≈ e^{48} ≈ 7·10^{20} — the door's M ≈ 4·10^{49}
   OVERFLOWS it (16(log(4M) + log e₂) ≈ 3968 > 1892). Repair: bump A to
   2^{18} (RHS ≈ 7568 ✓) and rescale G to G_gateK (G ≥ 64·Jb²·M/η ≈ 10^{53}).
   M stays SYMBOLIC (⌈8/δ₀⌉₊ — no numeral of that size is ever formed; the
   V9c law). New stone: `calFrameK_satisfiable_door` [B/C, 150–300].

## Ruling D-B₅ — pin B₅ := 12

ARITH-REF's arithmetic: the S7 minor-arc bound ‖S_H(α)‖ ≪ (log H)^{3−B₅/2}
must beat ε²/log H, forcing B₅ > 8 WITH the log-weight gain, B₅ > 10 without.
Pin **B₅ = 12**: does not depend on winning the log-weight refinement, and
the S7 threshold exponent is then (log H)^{4−6} = (log H)^{−2}, giving
threshold log H ≥ (C/ε²)^{1/2} ≈ 10^{49}·√C — the same order as the
campaign's existing inner scales; the staged-gate ∃H₀ in the sealed
BigXiArc/BigXiArcTight absorbs it as data (no wall).

Consequences:
1. **doorGrade stays (log H)^{−5/4}, deliberately weakened.** The port at
   B₅ = 12 delivers W^{−1/4} = (log H)^{−3} ≤ (log H)^{−5/4} — one
   monotonicity line at the S9 exit (M4-9). The landed DoorFloor/H₀door/
   budget_head_grade_closed stay VALID and CONSERVATIVE, untouched. The
   DoorFloor docstring's "S7's B5 = 5" provenance line is corrected to "the
   socket is a deliberate weakening of the port's −B₅/4; B₅ = 12" (maestro
   edit, docstring only, no statement change).
2. **S10a re-instantiation, chi-check's own rule**: 625 = 125·5 → 1500 =
   125·12. New stone: the 1500-variants of regime_W_headroom_of_floor /
   regime_hthr_of_scale / regime_head_W_headroom (RegimeHead's exponent
   included) [B, 150–250]. Prop 2.4's other window arm W ≤ H^{1/250}
   (⟺ 3000·loglog H ≤ log H) is trivial at scale.
3. The mr-freeze S7 row's staged gate stays; the L-ladder brief carries
   B₅ = 12 and the TIGHT radius (the ratified amendment).

## Ruling D-FLOOR — H₀door untouched; the K-demand joins the S11 max as a NEW ARM

U1's flag ("the door floor may need re-derivation") resolves as **no**:
- H₀door(δ₀) remains the valid grade-crossing floor for the doorGrade shape.
- The K-family demand (log h ≥ 4M·calE·log 2 at M = ⌈8/δ₀⌉₊, calE at the new
  inhabitant) is a SEPARATE lower bound on the window — it does not replace
  the grade crossing, it joins it. The S11 compose order (mr-freeze :21)
  already takes floor = max(H0red, H0D3, H0xi, H0^MR, T(eps), H*_A-arm);
  add the arm **H_K := ⌈exp(4·M·calE·log 2)⌉₊-shaped, symbolic**. The
  mechanism is ALREADY LANDED tonight: chowlaRegime_exists_param_head's
  Hlo₀ slot absorbs any floor demand, and the epsFloor device (RegimeHead)
  is the general log-side-to-floor converter. gJoin needs no change (the
  floor rides Hlo₀, not the x-side arms).
- Numerology, one-sided: log H_K ≈ 4·(4·10^{49})·calE·0.69 — with calE at
  A = 2^{18}, G ≈ 10^{53}: calE = A·G·4^{Jb−1}-shaped ≈ 10^{59} ⟹
  log H_K ≈ 10^{109}. The final x ≈ exp(exp(10^{109})-ish) — the campaign's
  towers grow one story; everything stays shape-level, no numeral formed,
  no landed statement moves. (The U2 constant rides along: M4-6 demands
  M(λχ̄;X′) ≥ 5·log W per S8's E(M) = exp(−M/2) convention — λ's supply
  (1/3−ε)·loglog X ≫ 5·12·logloglog-scale ✓ with absurd headroom.)

## The repair-round consequences for the M4 ladder (the re-freeze spec)

M4-0 loses the q ∣ H clause and the exact-denominator route entirely; the
split runs at the S7 approximant's q ≤ (log H)^{12} via BigXiArcTight. NEW
M4-0′ = MRT (4.2) IBP [C, 300–450]. M4-5 restated per the refuter (h := H′/d₀
∀H′ ∈ [0,H], trivial branch below H·d₀/W³, the six named A.2 side conditions,
𝒮 at the K-family per D-FAMILY, the thm_A2′ interface WRITTEN OUT — s8-freeze
wave-5 to be told to match). M4-6 at 5·log W (U2). New stones:
calFrameK_satisfiable_door, the S10a 1500-variants. Band re-priced ≈
3900–6200. The re-frozen ladder issues as s9-freeze-0726.md AMENDMENT A after
this block's refuter pass returns clean.
