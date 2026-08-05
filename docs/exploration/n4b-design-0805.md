# N4b DESIGN FREEZE v2 — HB Lemma 7 at the multiplicative mandate
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
