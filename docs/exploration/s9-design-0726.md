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

## ⟦AMENDMENT A⟧ — the refuter repairs + the HSIEVE verdict (folded same
evening; verdicts: FAMILY-REF REPAIR-THEN-FIRE, B5-REF REPAIR-THEN-FIRE;
full structured verdicts in the wf_7056afa8 journal)

**D-FAMILY, corrected and re-grounded.** My numbers were wrong at the door
floor (log H₀door = δ₀^{−4/5} ≈ 9·10^{38}, NOT 10^{49} — I confused δ₀^{−1}
with log H; density there ≈ 2.4·10^{−34}, ~15 orders above δ₀). And the
"NEVER/structural" claim was FALSE against the socket: budget_head_grade_closed
takes ANY δ ≤ δ₀ at a free floor, and the MRT-family density clears δ₀ at
log H ≳ 1.5·10^{54} — floors are free, so the MRT family is NOT excluded.
THE HONEST GROUNDS (the ruling STANDS on these): (i) the K-family removal
bound is landed, kernel-checked, and constant-free (sum_ratioK_le /
eq28_clears_of_M) — the MRT family would need its Lemma 2.2 constant made
explicit + a new δ₀-keyed floor; (ii) at EQUAL H the MRT density never beats
(log H)^{−5/4} (ratio ≥ 1.3·10^4 on every admissible regime); (iii) with the
containment correction below the two floor arms are the same order anyway.
Citation fixed: MRT Lemma 2.2 = 1503.05121v3 p. 8 (density); MR 1501.04585v4
p. 6 (sieve bound).

**The inhabitant is PARAMETRIC — the fixed-A stone was unprovable.** δ₀'s
only exposed property is 0 < δ₀ (SpineFinal's existential; 2·10^{−49} is a
SHAPE per chi-check), so A_gate_logK's LHS ~ 32·log M against a fixed-A RHS
is a catch-#253 corner. RULING: `calFrameK_satisfiable_door (M) (hM : 1 ≤ M)`
at `Adoor M := 2^18 * (Nat.log 2 M + 1)`, `G := 3072*M` — closes uniformly in
M (LHS ~ 768·log M, RHS ~ 1.8·10^5·log₂ M); every other gate checked clean.
Re-priced [B/C, 300–450]. THE MARGIN-HYGIENE LAW (standing): no stone in this
design pins a numeral that is a function of δ₀.

**The containment corrected — H_K shrinks 54 orders.** MRT A.2 / MR Thm 3
demand only [P₁,Q₁] ⊂ [1,h], i.e. Q₁ ≤ h: log h ≥ M·A·log 2 (level-1), NOT
the top-block containment (my Jb²·M·calE₂ was the Q_{Jb} ≤ h misreading).
H_K := ⌈exp(M·Adoor M·log 2)⌉₊-shaped, log H_K ≈ 10^{55}-order at the door's
M (post-C-rescale, below). Also corrected: log P₁ = A·log 2 (calE_one — my
10^{58} was level-2); the (log Q₁)^{40/η} check is a SUFFICIENCY EXAMPLE at
40/η = 480 (η = 1/12), not an obligation — the K-family meets (A.1)/(A.2)
directly via levelGates_calibratedK; the load-bearing P₁-demand is A.2's
error term, absurd room. calE = A·G^{j−1}·(j!)² (not 4^{j−1}-shaped).

**THE TRUNCATION LICENSE (U-A, ruled).** MRT p. 21 chooses J maximal with
Q_j ≤ exp(√log X₀) — at our enlarged x that J is ~10^{106}, while the landed
K-apparatus pins Jb = 2. RULING: the port consumes OUR thm_A2′, stated at
the K-family Jb = 2 — MRT's J-maximality is THEIR proof device, not our
obligation. Our 𝒮 (two bands) is a SUPERSET of theirs, so the density side
only improves; the A.2-proof side (the T/U decomposition reaching X/h) is
exactly what the landed K-exponent campaign certified at Jb = 2 (calQK's
j²M-exponent; seam_row_calibratedK; the N-UNIFORM kernel exits
lemma14_contour_kernel supplying the hMsup reach at Tcut = 2^N(X/h₁) — the
gap closes at every N). The write-up says "an 𝒮 of MR's shape at Jb = 2"
(consistent with the eq26 round's U-4). Stone-4's wave brief must confirm
the frame reach explicitly — the one caveat carried.

**M4-9 re-specified (the "one monotonicity line" was three).** Exit at
δ := doorGrade R.Hlo; (i) antitone-in-H (the doorGrade_anti shape); (ii) the
delivered grade is C_MRT·(log H)^{−11/4}·loglog H (MRT 2.3's prefactor
(log H)^{1/4}·loglog H — U-C; note the doorGrade shape is deliverable only
for B₅ > 6, further retiring the B₅ = 5 provenance); (iii) the IN-STATEMENT
gate C_MRT·loglog R.Hlo ≤ (log R.Hlo)^{3/2} (law #253 — the constant-
absorption margin IS the content of the weakening; at B₅ = 5 the gap was
ZERO). Still [B, 150–250].

**The B₅ = 12 pin SURVIVED** (B5-REF R-1 UNFOUNDED, kernel-certified
monotone: a bigger cap is strictly easier — bigXiArc_mono). My threshold
algebra corrected: log H₀(S7) ≥ C/ε² (not the square root; the ∃H₀-inside-∀ε
absorbs it; do not quote 10^{49}·√C forward — it conflated ε with δ₀).

**The FULL 1500-sweep site list** (my three-lemma list was short):
log_scale_threshold (DoorFloor :180 — 625→1500, 6250000→36000000, 2500→6000;
the proof shape survives with √36000000 = 6000 exactly);
regime_hthr_of_scale (:200); regime_W_headroom_of_H0door (:214 — its
δ₀ ≤ 6250000^{−5/4} numeral moves to 36000000^{−5/4} ≈ 3.6·10^{−10}, ~39
orders of δ₀-headroom); regime_W_headroom_of_floor (DoorDischarge :42);
regime_head_W_headroom (RegimeHead :358 + its 6250000^{−5/4}); NEW [A] stone
for Prop 2.4's second arm W ≤ H^{1/250} (⟺ 3000·loglog H ≤ log H — was
unpriced); LandauL1's three in-statement w = 5 sites (door_L1_absorbed :244,
door_L1_debit_absorbed :371, chi_floor_real_door :436) — PARAMETRIC-w
variants appended (logq_absorbed is already w-general); chi-check :52's
Route-A H1 x-floor re-derived at B₅ = 12 + U2's 5·log W: loglog X ≥
960·(log H)^{24}·loglog H — one-sided, a gJoin/Hlo₀ arm, free by
regimeEnlargeX; mr-freeze rows S9/S10 (annotated this commit); the sieveW
docstring (corrected this commit — the VALUE stays (log H₊)⁵: it is the
A-arm HEIGHT parameter, decoupled from the port's W; MRT's M(g;X,Q) needs
only Q ≥ 1, so it overserves; gJoin unchanged — FAMILY-REF R-4 verified the
Hlo₀ mechanism kernel-settled end to end). All variants ADDITIVE (new
lemmas; landed ones untouched).

**U2 rider corrected**: the supply coefficient is (1/4−ε)·loglog X (the
landed s5_spec/chi_floor_real_door shape; 1/3 was MRT's θ = 2/3 number we do
not have). And the M4-6 supply is the TWISTED q-uniform floor — it routes
through LandauL1's interface (chi_floor_real_door), so M4-6 inherits the
L1LowerEffective PRODUCTION residual (odd-χ FE [C, ~400] the cheapest;
even-χ open). Recorded as an explicit dependency of the S9 arc.

**THE HSIEVE VERDICT (same evening): ALREADY OWNED — the flag was stale.**
typical_density_le (TypicalDensity.lean :859, landed 2026-07-19,
kernel-checked [propext, Classical.choice, Quot.sound]) IS MR Lemma 2.2,
unconditional, C = 2·e^{19/log 2} + 1 ≈ 1.6·10^{12}; the blockOmega bridge
and the Mertens window are also landed (mathlib has NO Mertens; ours does,
3345 ln). The constant costs ONLY a linear M-rescale — M := ⌈8C/δ₀⌉-shaped —
absorbed by the parametric inhabitant (at M ≈ 3.2·10^{61}: LHS ≈ 4416, still
under even the fixed 2^18 RHS). A weaker SHAPE (second-moment) would NOT
work (forces log M ≈ 1/δ₀ — the frame goes symbolic); the true
log P/log Q power is required and owned. THE WIRING LADDER HS-1..HS-6
[B, 480–910]: the C-parametric eq28 variants (additive), card_blockfree_le
extraction, the three analytic gates at the K-family (hreg FREE on the
small-h branch — name the branch), the j-sum composition, the Pseq/Qseq pin
(the cross-wire trap: NOTHING in the hsieve binder ties MemS's free Pseq to
calP — pin at instantiation), the window generality via M4-8's dyadic split.
Do NOT chase the literal (1+1/100) — the K-ladder's M-pin is where the
constant is designed to be absorbed. Eight new traps banked in the scoper's
report (n = 0 / half-open endpoint +1; Nat.sqrt vs Real.sqrt; the ∃-C
wrapper stone so both consumers share one constant; the door-normalization
log ω absorption into M — verify at instantiation).
