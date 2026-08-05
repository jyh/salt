# N4b DESIGN FREEZE v3 — HB Lemma 7 at the multiplicative mandate
### 2026-08-05, Fable design block (Sancho). v1 REFUTED (4 refuters:
### R1 HOLD / R2 HOLD / R3 REPAIR-THEN-FIRE / R4 HOLD — full verdicts
### in the session ledger); v2 folds every repair. Status: FROZEN
### pending the delta pass (R1′/R2′ below).

## v1 → v2 changelog (the refuters' scoreboard)

1. **Height law replaced (R1 fatal, R3 unassigned)**: fixed
   efHeight q deletes HB's power saving; the log-F tail diverges.
   v2 uses the GENERAL-T landed family at the growing height
   **T(y) := (log(q·y) + 2)⁴**, three ranges (§2).
2. **A3 is a hard prerequisite (R1-U1, R4-U1)**: the packaged
   `psi_sharp_at_efHeightM` is vacuous (its efMultTotal·(y/T) term
   exceeds y); with the crude count, NO h rescues it. W0 lands the
   batching ∑_{|γ|≤T} m_ρ/|ρ| ≪ (log qT)² first.
3. **A4 β₀-isolation owed (R2 fatal)**: hreal is unsatisfiable at
   β₀ (it is IN the box); the erase-split + erased spend land in W0;
   hreal′ restated over the erased box.
4. **hN rides EXPLICITLY; TAU-SHARP queued (R2 fatal, R4 fatal)**:
   the pinned artillery (c ≤ 2^{−250}, k = 14) makes hN an
   η ≥ 2²⁵⁰·(log q)¹³-grade threshold — q-growing, which the N11
   door (Cor 2's absolute C⁽¹⁾) cannot deliver. RULING: N4b ships
   with hN as a NAMED SYMBOLIC binder (honest, non-silent); a new
   node **TAU-SHARP** (re-audit the 680-vs-104 exponent slack and
   the KEβ constant stack to make hN's threshold ABSOLUTE) is
   queued as the road's gate before N11. The "η at the constant
   threshold is trivially forgiving" claim is DELETED — this block
   proves nothing at bounded η and says so.
5. **Multiplicity ruled (R2-U4)**: no simplicity binder. (L1)/(L2)
   carry m := zeroMult χ β₀ explicitly; the cancellation survives
   with (m·ηL) throughout (F² ∝ (mηL)^{−2} against (L′/L)² ∝
   (mηL)²).
6. **(L1) at HB's grade (R3)**: additive form; W4 divides.
7. **Lp convention ruled (R2-R-2d, R4-U2)**: the campaign's
   Lemma-3 parameter is **Lp := 2·log q** (hCR is unsatisfiable at
   Lp = log q). Every wave statement names which L it uses; η is
   defined against 1−β₀ only (L-free).
8. **Binder set consolidated (§4)**: hηq (η ≤ q, Davenport — it
   ALSO supplies hceil and hellL), hsmall (z₀(log η)^{−1/2} ≤ 1,
   the exponentiation guard, HB's own side condition), hα (α < z),
   window edges per-wave (LOWER x ≥ q^{250} in W2; UPPER x ≤ q^{500}
   in W3), the split-point X quantified separately from Theorem 1's
   x (R4's two-roles finding).
9. **Supply table re-homed at the bytes (R2)**: every row corrected
   (§3); the "composition step" stated as wave work, not landed.
10. **W0 prerequisite wave added (R2-U2 writer-slot collisions)**:
    five small stones in their home files, explicit in-place
    authorizations, before W1–W4 touch anything.

## 0. The objects

With m := zeroMult χ (β₀ : ℂ), η := ((1−β₀)·log q)^{−1}, L := log q,
Lp := 2L, z₀ := L/log z:

- **(L1)** |L′/L(1,χ) − m·ηL| ≤ K₁·L·(log η)^{−1/2}
- **(L2)** κS₁ = x 𝔖 C(α) (m·ηL)^{−2} · (1 + δ), |δ| ≤
  K₂·z₀·(log η)^{−1/2}, under hsmall.

## 1. Binder set (named once, carried per §4)

hord (Re ρ ≤ β₀ on the box; T-BAL-UNORDERED), hreal′ (real box
zeros OTHER than β₀ obey the ceiling), hN (symbolic repulsion-live
regime: 0 ≤ log(1/(1−β₀)) − log(1/c) − k·log(log Q+2) at the
artillery's own (b,c,k) — EXPLICIT in every statement; TAU-SHARP
retires it to an absolute constant), hηq (log η ≤ L), hsmall
(z₀(log η)^{−1/2} ≤ 1), hα ((α:ℝ) < z), hz (3 ≤ z ≤ q^{1/3}),
hsep (the well-spacing dodge of `psi_sharp` genre — supplied in W2
via the ∃T′ trick, EFSharpZeros.lean:842 pattern).

## 2. The route (three ranges, growing height)

For the (4.11)-analog on Σ_{u<n≤v} χ(n)Λ(n)/n, v ≥ u ≥ x ≥ q^{250}:

- **Range A, u ∈ [x, Y₁]**, Y₁ := exp(10·L·log L/c₀) (c₀ =
  zero_free_region_all's constant): EF at height T(u) = (log(qu)+2)⁴
  via `psi_explicit_sharpM` (general T, OWN de-smoothing step
  h(u) ≍ u·√(log u)/(log qu)² — NOT the packaged h = y/efHeight),
  the erased zero-sum spend (W0's A4) bounded by the A3-batched
  harmonic sum × u^{β̄}, β̄ = repulsionCeiling at Q(u) = q(T(u)+2)
  (`boxZeros_re_le_of_repulsion`, TauExt.lean:259, general T, off
  `dh_repulsion_tall`).
- **Range B, u > Y₁**: the classical zero-free region
  (`zero_free_region_all`) as the fallback ceiling:
  u^{β−1} ≤ exp(−c₀·log u/log Q(u)) — closes the far tail with no
  density input. (Jutila remains a non-dependency; flags 19844's
  N2 warning is respected — N2's q-only packaging is NOT reopened,
  the general-T family is consumed instead.)
- **Budget page (delta-R1′ verifies)**: relative EF error at T(u)
  with optimal h and A3 in hand is ≲ (log u)^{1/2}/(log qu) ≤
  (log qu)^{−1/2}; through the two partial summations the log-F
  tail is ∫_x^∞ (log t)^{−3/2} dt/t < ∞-grade, total
  O((log x)^{−1/2}) = O(L^{−1/2}) ≤ O(z₀(log η)^{−1/2}) under hηq.
  Range-B tail: exp(−c₀ log u/log Q(u)) summed from Y₁ is
  O(L^{−10})-grade by Y₁'s choice. The β̄-spend on Range A: the
  ceiling at Q(u) ≤ Q(Y₁) keeps 1−β̄ ≥ (N-numerator)/(680·log Q(Y₁))
  with log Q(Y₁) = L(1+o(1)) + 4log log(...) — the R1-R2 regime
  arithmetic REDONE at the growing height, target
  u^{β̄−1} ≤ η^{−θ}-grade with θ ≥ 250/700 on Range A under hN.

## 3. Supplies — re-homed at the bytes (R2's corrections applied)

| supply | where (byte-checked by R2) | role |
|---|---|---|
| `dh_repulsion_tall` | TBalTall.lean:2081 | the height-free contract |
| `boxZeros_re_le_of_repulsion` (general T) / `_at_efHeight` | TauExt.lean:259 / TBalTall.lean:2199 | the ceiling; the ∃-obtain-then-feed composition is WAVE WORK, stated in briefs |
| `efZeroSumM_spend_le` (general T) / `_at_efHeight` | DensityCrude.lean:371 / :403 | the spend (N2's deliverable, NOT EFSharp's) |
| `zeroCountM_efHeight_le` / `efZeroSumM_norm_le` (Z-general) | DensityCrude.lean:289 / :352 | the counts |
| `psi_explicit_sharpM` (T, h free) + `psi_explicit_sharpM_of_riesz_residues` (σ free) + `psi1_contour_shift_finsetM` outputs | EFSharpMult.lean:968 / (σ-general variant) / contour stack | the EF; the packaged `psi_sharp_at_efHeightM` is NOT used (vacuous — R1-U1/R4-U1) |
| `pretenseSum_le_differenced` | TwistedMertens.lean:646 | the χ(p)=1 kill for (4.7) — NOT the S2−S1 packaging |
| `hbCoreRate_at_hb_optimum_absorbed` | Lemma3Uncond.lean:116 | the absorbed rate feeding the composite (W0-v) |
| `LFunction_partialFraction` / `_remainder_diff` | PartialFractions.lean:245 / BCSup.lean:229 (admits 1 ≤ σ) | W1's s = 1 machinery |
| `mertens_third` via EulerLink | Salt/Mertens/Third.lean:743 / SW/EulerLink.lean:62 | (4.6); ∃C existential + ℕ-indexed — W4 owes the re-indexing |
| `mertens_second_sharp` (+′) / `mertensB` | Mertens/Second.lean:216 / Third.lean:679 / PrimePower.lean:148 | W3's (4.7) bridging (the "Mertens handles the rest" identity) |
| `zero_free_region_all` | (used at TBalTall.lean:2093) | Range B's fallback ceiling |

## 4. The waves

- **W0 — PREREQUISITES** (five stones, HOME files, explicit
  in-place authorizations; nothing else fires until W0 seals):
  (i) A4 erase-split of `efZeroSumM` (class A;
  EFSharpMult.lean, Finset.add_sum_erase at :140-142's def);
  (ii) the ERASED spend ‖efZeroSumM (box.erase β₀)‖ ≤ count·y^β̄
  (class B; DensityCrude.lean, re-run :403-427 off :352);
  (iii) **A3 batching** ∑_{ρ∈box} m_ρ/‖ρ‖ ≪ (log qT)² (class B/C;
  DensityCrude.lean; dyadic split of the count — if the
  unit-interval count is not derivable from the landed stack, FLAG,
  do not grind);
  (iv) the σ = 1 binder relaxation of `neg_re_logDeriv_differenced`
  (class A/B; TwistedMertens.lean; per R2's recipe: hσ1 → hβσ +
  separate hσ′1 — the body survives verbatim);
  (v) `pretenseSum_unconditional_absorbed` (class B, ~50 ln;
  Lemma3Uncond.lean; re-run :84-102's discharge against
  `pretenseSum_le_differenced` instead of hb_lemma3_final).
- **W1 — (L1)** additive grade, at s = 1 via W0-iv, m explicit
  (new Salt/HB/Lemma7L.lean).
- **W2 — the (4.11)-analog** at the §2 three-range design; carries
  hsep, the LOWER edge q^{250} ≤ x, hord/hreal′/hN; m-weighted
  main term m·(1−β₀)^{−1}(v^{β₀−1}−u^{β₀−1}) (new
  Salt/HB/Lemma7EF.lean).
- **W3 — the F computation**: (4.7) via W0-v at the SPLIT POINT X,
  ∀X quantified with q^{250} ≤ X ≤ q^{500} (R4's two-roles repair —
  never bound to Theorem 1's x); the Mertens-second bridging row;
  the integral with the honest t₀-constant note (the O(η^{−1}log η)
  error's constant is ≥ 500 — state the explicit constant, don't
  hide the window exponent); UPPER edge consumed here (twice
  internally: the integral's t₀ and the Rankin N^{1/Lp} ≤ e^{250}
  at Lp = 2L) (new Salt/HB/Lemma7F.lean).
- **W4 — the assembly**: (4.4) (needs hα) + (4.5) + (4.6)
  (mertens_third re-indexing) + W3 → (L2); the F² exponentiation as
  an explicit Real.exp bound under hsmall — no informal
  O-absorption (new Salt/HB/Lemma7.lean).

## 5. Delta pass (before W0 fires)

- **R1′**: re-run the budget attack against §2's three-range page
  at the growing height — the A3-batched EF ledger, the Range-A/B
  seam at Y₁, the redone regime arithmetic, all corners.
- **R2′**: byte-check §3's re-homed table + W0's five recipes
  (files, line anchors, class estimates) + the binder set's
  self-consistency (does hηq really supply hceil AND hellL at
  Lp = 2L?).

## 6. Queued nodes minted by this block

- **TAU-SHARP** (the road's N11 gate): shrink the artillery's
  (b, c, k) so hN's threshold is an absolute constant — re-audit
  the 680-vs-104 slack and the KEβ = 16·(328+240)·627⁹ stack.
  Priced by R2 as the alternative to a q-growing η demand that the
  Cor-2 door cannot meet.
- **(L1)-additive note for N6**: Lemma 5's A′(p) ≪ B log p wants
  the additive precision — (L1) is shipped additive (v2 §0), so no
  re-derivation owed. Recorded so it is not re-found as a defect.


---

# v3 DELTA (2026-08-05 evening) — the delta pass verdicts folded
### R1′/R2′ both REPAIR-THEN-FIRE. Where v3 conflicts with v2 above,
### v3 GOVERNS. Wave briefs quote v3.

## D1. The EF socket route (replaces v2 §2's Range-A EF sentence and
## the psi_explicit_sharpM supply row — R1′-1, R2′-1a)

`psi_explicit_sharpM` is VACUOUS at every (T, h) — its de-smoothing
term rides the collapsed count (rel(B)·rel(C) = 948·log u·log qT,
T-free and h-free). The A3 batching was the WRONG TOOL for that term
(no 1/‖ρ‖ weight exists there); A3's role is the ZERO SUM only.
Route instead:
- fire `psi_sharp_of_riesz_bounds` (Salt/SW/EFSharp.lean:322 — the
  order-blind socket, A₁/A₂ free) directly on the two
  `psi1_contour_shift_finsetM` outputs (EFSharpMult.lean:235),
  A_i := −efRieszSumM χ Z (y or y+h);
- bound the difference quotient ‖(𝓡_M(y+h) − 𝓡_M(y))/h‖ DIRECTLY:
  (y+h)^{ρ+1} − y^{ρ+1} = ∫_y^{y+h} (ρ+1)t^ρ dt gives the per-zero
  bound m_ρ·h·(y+h)^{β̄}/‖ρ‖ — then the A3 batching applies (W0-vii);
- β₀'s residue split off first (W0-i), its own difference quotient
  by the single-zero Taylor bound (cost ≈ h·y^{β₀−1}, negligible);
- **h := u/√T(u)** (NOT u·√(log u)/(log qu)²);
- **T(u) := (log(qu) + 2)⁶** (6th power — the pointwise EF error
  becomes ε(t) ≍ (log qt)^{−2}, dt/t-summable outright, retiring the
  composite-only subtlety of D3 with margin; T is free in the
  contour stack, this costs nothing).

## D2. The regime binder (replaces hN's role — R1′-2)

- **hN+ : log(1/(1−β₀)) ≥ 2·(log(1/c) + k·log(log Q(Y₁)+2))** — the
  quantitative form; θ ≥ 0.18-grade uniformly follows, and the
  consumer needs only L·η^{−θ} → 0 (HB's (4.11) tolerates ANY A > 0;
  250/700 was over-claimed and is retired).
- The honest grade: log(1/c) ≥ 631.6 — the binding arm is
  (c₀/KErho)⁸, KErho = 16·636·627⁹, c₀ = 1/126848
  (ZeroFreeReal.lean:604) — NOT the 2^{−250} arm. hN+ ⟺
  η ≳ e^{1264+26·log L}-grade. **TAU-SHARP re-scoped accordingly: the
  KErho arm is the target, and k must go to 0, not merely shrink.**
- hN+ ∧ hηq is empty below q ≈ e^{250}: said aloud so no executor
  reads the pair as a contradiction.
- The Range-A ledger stated honestly: u^{β̄−1} ≤ (e^{632}·L^{13}/η)^θ
  — the prefactor rides EXPLICITLY; consumers check against that
  form, never against a bare η^{−θ}.

## D3. W2's deliverable (replaces the standalone (4.11) — R1′-U2,
## R2′-unassigned-2)

No uniform-error (4.11) exists at slowly-growing heights. **W2
delivers the log-weighted composite Σ_{n>X} χ(n)Λ(n)/(n log n)
directly** (the (4.12)-form, which is what W3 consumes anyway),
integrating the EF error against dt/(t log t). At T(u) = (log qu)⁶
the ledger closes with ∫_x^∞ (log t)^{−2}-grade margin.

## D4. Range B re-cut (R1′-2iv, R1′-U1)

- **Y₁ := exp(20·L·log L/c₀)** (decay L^{−20} beats the growing-height
  count prefactor for L ≳ 300);
- the erased spend exits through the **A3 harmonic form** (prefactor
  ≍ log(qT)·log T), NOT the count form — W0-ii is restated
  accordingly (keep Σ m_ρ/‖ρ‖ BEFORE the a-collapse:
  norm_sum_le + per-term ‖y^ρ/ρ‖ ≤ y^{β̄}/‖ρ‖);
- the tail grade stated with its constant: ≈ 1.27e5·L^{−19}-grade
  (the freeze's own explicit-constant discipline);
- `zero_free_region_all` (decl ZeroFreeReal.lean:605; obtained at
  TBalTall.lean:2089) covers ONLY complex zeros (side condition
  χ² ≠ 1 ∨ Im ρ ≠ 0; our χ is real) — hreal′ is carried height-free
  at the repulsion ceiling (the stronger of the two), one binder
  suffices.

## D5. hsep DEMOTED (Captain-visible — R1′-U4, R2′-unassigned-1)

The ∃T′ dodge is docstring prose (EFSharpZeros.lean:41-42, :842-843),
NOT a landed lemma; and no landed count can pigeonhole the width-2
zero-free band the contour socket demands (the unit-window count
gives gaps of width ~1/log, not 2). **hsep rides as a NAMED SYMBOLIC
binder** exactly as hN+ does. Two road nodes minted:
- **HSEP-GAP** (scout first): price whether
  `psi1_contour_shift_finsetM`'s +2 box margin is load-bearing in its
  proof — if the socket restates at a δ-margin (δ ≍ 1/log qT), the
  landed unit-window count `efMultTotal_halfbox_le`
  (EFSharpMult.lean:1075) discharges hsep by pigeonhole in [T₀,T₀+1].
  Read-only scout, then class B/C wave if viable.
- **N2-DENSITY** (the fallback and the road's eventual asset): Jutila
  Thm 1, N(σ,T,χ) ≪ (qT)^{(5/2)(1−σ)} — which ALSO reopens HB's
  original power-height route (T = y^{1/3}), where hsep discharges by
  pigeonhole against the density count and the whole polylog
  apparatus simplifies. Research-tier; the flags-19844 warning
  honored.
**N4b ships conditional on TWO named binders (hN+, hsep), both
explicit, both queued for retirement.** This is the v6-riders
pattern applied to the road: land the object, name the debt.

## D6. W0 — THE PREREQUISITE WAVE, v3 list (all recipes byte-verified
## by R2′; classes confirmed)

In-place authorizations: EFSharpMult.lean, DensityCrude.lean,
TwistedMertens.lean, Lemma3Uncond.lean, flags.md. Sequential, one
executor.
- (i) the β₀ erase-split of efZeroSumM — Finset.add_sum_erase at the
  :140-142 def; the corpus pattern at TwistedMertens.lean:404-408.
  Class A. ✔ verified
- (ii) the A3-BATCHED erased spend (v3 form, per D4): the :356-365
  body with the a-division deleted, + the subset-monotonicity
  one-liner. Class A/B. ✔ recipe corrected
- (iii) A3 batching Σ m_ρ/‖ρ‖ ≪ log(qT)·log T (sharper than the v2
  claim): `efMultTotal_halfbox_le` (EFSharpMult.lean:1075) + the
  fibring of DensityCrude.lean:100-176 (Finset.sum_fiberwise_of_maps_to)
  + `harmonic_floor_le_one_add_log` (in use at Goldbach/Final.lean:143).
  Class B. ✔ verified derivable, NO new analytic input
- (iv) the σ = 1 relaxation, CORRECTED recipe: hσ1 : 1 < σ →
  **hσ1 : 1 ≤ σ** (NOT hβσ) + NEW binder hσ'1 : 1 < σ'; drop the .le
  at :445; hdβ closes from hσ1 + hβ1. IN THE SAME STONE retain the
  multiplicity: hβterm (:417-433) becomes the m-equality and the
  conclusion carries −(m/(σ−β₀)) + m/(σ'−β₀) (proof SHORTENS:
  hmono/hm1 drop). Class A/B. ✔ recipe corrected at the bytes
- (v) `pretenseSum_unconditional_absorbed`: the :84-102 export feeds
  `pretenseSum_le_differenced` verbatim — the closing line is
  literally `exact pretenseSum_le_differenced χ N hσ1 hσ2 hlt hσ'2
  hβ1 hβZ hmβ hr0 hσr hσ'r hfloor hSinv hrem`. ~50 ln, class B.
  ✔ verified verbatim
- (vi) un-collapse `efRieszSumM_diff_sub_efZeroSumM_le` to the
  per-zero form Σ m_ρ·h·y^{ρ.re−1} (the proof already proves it at
  :884-897; the collapse is only :900-901) + restate the two
  downstream forms un-collapsed. Class A, ~15 ln + 2 restatements.
- (vii) the direct 𝓡_M difference-quotient bound via
  ∫_y^{y+h}(ρ+1)t^ρ dt → per-zero m_ρ·h·(y+h)^{β̄}/‖ρ‖. Class B.

## D7. (L1) one-sided (R2′-2iv)

The landed differencing yields the UPPER side only; (L1) is restated
one-sided (Re(−L′/L(1,χ)) bounded by the m·ηL main term + the rate),
which is all HB's p.200 consumer uses; recorded in §6 for N6. The
lower side, if ever needed, is a separate stone (Σ m_ρ(1−Re ρ)/|1−ρ|²
off the DH floor) — NOT in W0.

## D8. Byte-exactness sweep (R1′-U3, R2′-1b-e)

Base heights: the box is (T+2) so the ceiling base is q(T(u)+4) —
briefs say +4, never +2. `boxZeros_re_le_at_efHeight` (exact name).
`psi_explicit_sharpM_of_riesz_residues` at :914 (σ-general — but see
D1: not the route). `zeroCountM_le` (DensityCrude.lean:188) added as
the general-T count row. EulerLink decl at :57. The w/left-edge
budget rows added: w ≲ 1/(count) forced by hsep's σ-half, B ≍ L₄/w,
and the left-edge term forces σ₀ = 1 − Θ(log L/L) — checked
compatible with β₀ ∈ box under hN+ and with hσ₀w. hηq spelled ONE
way: hηq : log η ≤ L.


## D9. HSEP-GAP SCOUT VERDICT (2026-08-05 late): RESTATEMENT-VIABLE
### — D5 amended; hsep is dischargeable with NO unlanded analytic input

The width-2 band is an ARTIFACT of the hZall/hZsep asymmetry, not
structural. The scout's byte-priced recipe (class A/B, ~40-50 ln
across 3 declarations, generalize-in-place so the old statement is
a one-line corollary):

- ONE hypothesis change at the socket (EFSharpMult.lean:240
  HEAD-relative): hZall gains the disjunct `ρ ∈ Z ∨ T + w ≤ |ρ.im|`;
  two proof-site repairs (:328 rcases ~4 ln; :644-651 by_cases ~10
  ln via Complex.abs_im_le_norm — works uniformly for all edges).
  The +2 reach (the 3/2 Borel–Carathéodory ball in
  MaxModulus.lean:89-101) stays — it was never the problem.
- Re-instantiate psi_explicit_sharpM (+ the at_efHeight and the
  EFSharpZeros twin if consumed) at the box-exact Z := boxZeros …
  T; the ceiling base IMPROVES q(T+4) → q(T+2) (D8's +4 note
  relaxes).
- The residual demand is a width-2w band + a width-2w σ-strip, and
  BOTH pigeonhole off LANDED counts (efMultTotal_halfbox_le for the
  Im-half; zeroCountM_le for the σ-half, which BINDS:
  w ≍ 1/(L·T·log qT)) via a pure Finset midpoint argument — no
  measure theory, no density theorem. hsep then RETIRES as a proved
  step, not a binder.
- Downstream D1 route survives with ZERO constant changes
  (psi_sharp_of_riesz_bounds is Z-agnostic; the spend/ceiling rows
  are T-free).

**THE ONE OPEN CHECK (budget, not structure)**: the σ-half's w
forces B ≍ T·log³(qT) in efShiftError's edge terms; at
T(u) = (log qu)⁶ that is polylog, but the LEFT-EDGE term
B·x^{σ₀+1}·π/σ₀ must be re-priced at that B (the D8 row). Assigned
to the W2 brief as a MANDATORY pre-proof ledger row; if it fails,
raise the T-exponent (T is free) until it closes and record the
final exponent.

**Sequencing**: the HSEP-GAP stone is W0.5 — fires the moment W0
releases the EFSharpMult writer slot; W2 consumes the restated
socket. N2-DENSITY remains minted as the road's asset (the
power-height route), no longer N4b's dependency.


## D10. W1 LANDED (f94cedb) — two notes for W4's consumption

- (L1) landed in the SHARP direction: m·ηL − Re(L′/L(1,χ)) ≤
  K₁·L·(log η)^{−1/2} (the D7 prose's minus-sign reading would have
  been the trivial direction). W4 quotes `hb_L1_one_sided`
  (Lemma7L.lean:231): conclusion
  Re(−L′/L(1)) ≤ −(m·ηL) + (1604 + 2m + 8Cs)·L/√(log η).
  K₁ = Lemma 3's constant + one m; NO hN+/hord/hreal′/hsep on W1
  (the route never touches the artillery ceiling) — the binder is
  the DH floor + Sinv pair, discharged the Lemma-3 way.
- PROCESS (for every parallel brief henceforth): concurrent
  executors share the lake build dir — transient olean vanishing
  and Scratch.lean collisions occurred. Rule: each executor uses
  Scratch<NODE>.lean (unique), tolerates transient build breakage
  from the neighbor by re-running, and judges only its OWN final
  full build.
