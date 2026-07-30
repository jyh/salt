/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetGChi
import Salt.MR.PortClose

/-!
# USetGChiTS — the GRADED `𝒯_S` exit and THE FIBREWISE GRADED A3 (stones ⟦ii-5⟧, ⟦ii-6⟧)

`docs/blueprints/flags.md` ⟦C2-SCOPE lands⟧ / ⟦THE THRESHOLD WALL⟧ / ⟦RELIFT-A lands⟧ and
`docs/exploration/a4-bridge-freeze-0730.md` v2.3, ratified as **council ruling C2** on the
morning of 2026-07-30 (the graded fibrewise re-lift); dispatched as the second-bank wave
**RELIFT-B** (items ⟦ii-5⟧ + ⟦ii-6⟧ on top of RELIFT-A's `USetGChi`), together with the
⟦K-5⟧ gate-compatibility check recorded in §0 below.

## What this file is

`USetGChi.lean` (RELIFT-A) re-lifted the `𝒰`-set, its thinness and its razor to the GRADED
threshold.  What was still owed was the pair of consumers that turn that razor into A3's
window mean square:

* **⟦ii-5⟧ (§1)** the `𝒯_S` branch exit at the graded pair set — the χ-analogue of the flat
  `HalaszIntegersChiClose.usetChi_TS_branch_exit_repinned`, with `UsetGChi` in place of
  `UsetChi` and `thinBundleGChi` in place of `thinBundleChi`.  **The `φ(q)`-graded Halász row
  (`halaszIntegersChi_phi`) is LEVEL-AGNOSTIC** — it quantifies over arbitrary coefficients and
  per-fibre well-spaced pair sets and says nothing about any partition — so the whole engine
  (`TSChi_branch_meansq_phi`, `phi_debit_level_repin`) re-instantiates VERBATIM.  What changes
  is only the `𝒰`-membership genre and the identity of the bundle in `hbudget`.
* **⟦ii-6⟧ (§2–§4)** THE C2 DELIVERABLE: the fibrewise family re-cut of the three single-`A`
  statements at the ratified pair spelling
  `𝔄 : Set (DirichletCharacter ℂ q × ℝ)` with fibrewise measurability.  Per C2-SCOPE's
  Finding A3-2, `usetChi_integral_to_branches` is the ONLY place in the corpus where a single
  `A : Set ℝ` is fixed across the characters; the two `PortClose` composes inherit it.  All
  three are re-cut here at the family binder — **additively**: nothing landed is touched.

Purely additive: this file introduces no new estimate.  Every rung is a composition of landed
theorems, and the two flat statements it mirrors keep standing unmodified.

## §0 — ⟦THE K-5 CHECK⟧ the graded gate set against the socket's floor and G1–G4

C2-SCOPE booked one refuter check at execution (K-5): *are the graded re-lift's gates jointly
satisfiable alongside the socket's uniform floor `T₀ ≤ T` and the four `q`-vs-`T` gates
G1–G4?*  **VERDICT: COMPATIBLE**, with the regime exhibited below; no two gates clash.  Three
findings ride with the verdict, all stated honestly.

### The four log scales, and which gate speaks which

* **`log(qT)`** — the graded count/height (`hκ30Q`, `hLL5`, `hQT`, `hBT`, `hκ30`), the
  socket's decay denominator, and the razor's `(qT)^{2α_Jb}`;
* **`log(5T+1)`** — the socket's four gates G1–G4, and nothing else;
* **`L ≥ log(qT)`** — the `𝒯_L` kill's own scale (`hTL`, `hLe`, `hWL`, `hlogV`, `hgate`);
* **`log X`** — the `𝒯_S` level `ε_Q`, the modulus gate `q ≤ (log X)^{12}`, and the razor's
  debit and budget.

None is ever substituted for another in any statement below (law #253, and the discipline
`USetGChi`'s header states).  `log(5T+1)` and `log(qT)` are comparable but NOT equal, and the
verdict below never uses one for the other.

### THE REGIME EXHIBITED — the x-scale door instantiation

Fix a modulus `q`.  Take `s` (which will be `loglog(5T+1)`) at least

  `s ≥ max( 8·log(2·10⁸·q) , 8 + log(20000(5000q+8104))/100 , (4/3)·log M , 4000 )`,

where `M = max(Kq·log(q(e^{e^100}+3)), q^{1/16}/Ks, 1)` is `PortNonVacuous`'s own witness
datum, and put

* `T := (exp(exp s) − 1)/5`, so `log(5T+1) = exp s` and `loglog(5T+1) = s`.  This is
  literally `gates_jointly_satisfiable`'s witness, so `T₀ ≤ T` and **G1–G4 hold outright**;
* `X := T` — MR Step 0's majorant `T ≤ X` at equality (`hTX`, `hX0`, `hL0`);
* the §8.3 door pins: `θ := θ₂₉₃ = 1/(32(3e+1)) ≈ 1/293`, `H_Jb = H₈₃ X θ₂₉₃ = (log X)^θ`,
  `P_Jb = P₈₃ X θ = exp((log X)^{1−θ})`, `Q_Jb ≤ Q₈₃ X = exp(log X/loglog X)`;
* the graded exponent of the door family `α_Jb = 7/48`, the razor's `η := 1/12`, the two
  absorption exponents `ε = ε' := 1/1000`;
* the branch data `ε_Q := (log X)^{−106}`, `V := (log X)^{106}`, and **`L := (log(qT))^{11/10}`**
  (see FINDING 2 — the exponent `11/10` is forced, and it is free).

At that point every gate of the combined list is satisfied:

* `1 ≤ T`, `1 < qT`, `1 ≤ log(qT)`, `5 ≤ loglog(qT)`, `e^{40} ≤ log X`, `e ≤ log X`,
  `2/ε ≤ loglog X` — all are `s ≥ 4000` (`log X ≈ e^s ≥ e^{4000}`);
* `2 ≤ H_Jb`: `(log X)^{1/293} ≥ 2` needs `log X ≥ 2^{293} ≈ 1.6·10^{88}` — i.e. `s ≥ 203` ✓;
* `3 ≤ P_Jb ≤ Q_Jb`: the landed P-3 gate `pin_P83_le_Q83`, `loglog X ≤ (log X)^θ`, holds from
  `log X ≥ (4/θ²)^{1/θ} ≈ 10^{1626}`, i.e. `s ≥ 3743` ✓ (this is what pins `s ≥ 4000`);
* `Q_Jb ≤ qT` and the X₀ law `30 ≤ log(qT)/log Q_Jb`: `log Q₈₃ = log X/loglog X`, so the ratio
  is `≥ loglog X ≈ s ≥ 4000 ≫ 30` ✓;
* `0 ≤ α_Jb ≤ 1/4 − η` and `2α_Jb ≤ 1/2` and `α_Jb ≤ 1`: `7/48 = 0.1458… ≤ 1/4 − 1/12 = 1/6`
  ✓, `7/24 ≤ 1/2` ✓.  **This is ⟦THE THRESHOLD WALL⟧'s inequality with the killing factor
  removed**: the wall's bridge asked `α_Jb·(log Q_Jb/log P_Jb) ≤ 1/4 − η` — false by
  `3.5·M ≈ 6.6·10^{62}` — while the graded razor asks `α_Jb ≤ 1/4 − η` alone, because the
  exact-`α` collapse inside `ramQChi_graded_count` makes the height power exactly
  `(qT)^{2α_Jb}`.  The re-lift's own gate is the one that holds;
* `2η ≤ 1` ✓ and the landed exit floor `2η ≥ 1/500` (`USetPins.c0_le_exit_exponent`):
  `2η = 1/6` ✓;
* the debit `q^{2α_Jb} ≤ X^ε` by `charDebit_le_rpow` at `q ≤ (log X)^{12}`, `2α_Jb ≤ 1/2`,
  `ε ≥ 1/1000`, `e^{40} ≤ log X` ✓ (~378 orders of margin, as landed);
* the budget `thinBundleGChi(qT, VJ, H_Jb, P_Jb, Q_Jb)·X^{1−2η+ε} ≤ M`: the bundle is
  `|ramI| · 1680 · VJ² · exp(2(log qT/log P_Jb)·loglog qT)` with `|ramI| ≤ 2(log X)^{1+θ}`,
  `VJ² ≤ X^{ε'}` and `(log qT/log P_Jb)·loglog qT ≈ (log X)^θ·loglog X = o(log X)`, so the
  left side is `X^{1−2η+ε+ε'+o(1)}` against `M ≥ X^{1−1/loglog X}`; the demand is
  `2η > ε + ε' + 1/loglog X + o(1)`, i.e. `1/6 > 0.002 + 0.00025 + o(1)` ✓ — **two orders of
  margin**;
* the per-`j` block gates and the socket-price gate — see FINDING 2.

### FINDING 1 — G1 is the binding MODULUS cap; it nests inside the port's, it does not clash

`vkStripConst q = 5000q`, so G1 reads `8·log(2·10⁸ q) ≤ loglog(5T+1)`, i.e.

  `q ≤ (log(5T+1))^{1/8} / (2·10⁸)`.

The port's own conductor window is `q ≤ (log X)^{12}`.  Both are UPPER bounds on `q`; the
combined system runs in the intersection, which is the G1 one (strictly tighter at `T ≤ X`),
and it is nonempty at every height in the regime above.  **What is NOT available is the full
conductor window `q ≍ (log X)^{12}` together with MR Step 0's `T ≤ X`**: there
`8 log q ≈ 96 loglog X` while `loglog(5T+1) ≤ loglog(5X+1)`, so G1 fails.  That is a property
of the FLAT A3 exactly as much as of the graded one — `usetChi_window_meansq_gated` carries
the same `hTX`, the same `hqlog` and the same G1 — so the graded re-lift neither creates nor
cures it.  It is recorded here because K-5 asked for the walk, and it is the honest reading of
`PortNonVacuous`'s own "G1 is the binding gate".

### FINDING 2 — the `φ(q)` repayment is NOT free against `hlogV`; `L` pays it, and can

The `𝒯_L` branch carries `hlogV : log V ≤ 100·log L` while the `φ(q)` repayment re-pins the
level to `ε_Q = (log X)^{−106}`, i.e. `V = (log X)^{106}`.  At the MINIMAL choice
`L = log(qT)` this reads `106·loglog X ≤ 100·loglog X` — **false**.  The repair is free and it
is a choice of `L`, not a weakening: with `L = (log qT)^κ` the two live gates are

  `hlogV`  ⟹  `κ ≥ 106/100 = 1.06`,
  `hgate` (`420·L^{7/4}(log L)^5 ≤ cs·(log ramQbase)^2`, at `log ramQbase ≥ log P₈₃ =
  (log X)^{1−θ}`)  ⟹  `κ < 8(1−θ)/7 = 1.1389…`,

so `κ ∈ [1.06, 1.1389)` — nonempty, and `κ = 11/10` sits inside with the exponent margin
`2(1−θ) − 7κ/4 = 0.0682 > 0` (the polylog `420(log L)^5/cs` is beaten by `(log X)^{0.068}`
for `s` large).  This too is a pre-existing feature of the flat compose (same `hlogV`, same
`hVδ` at `(log X)^{−106}`), surfaced by the walk rather than introduced by the re-lift.

### FINDING 3 — the graded re-lift DECOUPLES two levels the flat one conflated

In the flat compose a single `V` serves both the thinness level (through
`hVα : log V ≤ α·log P_Jb` and `hVinv : V⁻¹ ≤ δ/K₀`) and the `𝒯_L` threshold (through
`hV1`/`hVδ`).  At the graded threshold the thinness level is the block datum `VJ` (with
`hVJ : ∀ v ∈ ramI, exp(α_Jb v/H_Jb) ≤ VJ`, concretely `VJ = Q_Jb^{α_Jb}`), and it is a
DIFFERENT object from the branch threshold `V`.  Hence `hVα`, `hVinv`, `hδ0` and `δ` itself
disappear from the family statements below, and the joint feasible region is strictly larger
than the flat one — the re-lift removes a coupling rather than adding a constraint.  The two
binders `VJ` and `V` are both in-statement and are never identified.

**So: COMPATIBLE.  No pair of gates in the combined list is in conflict; the binding
constraint of the whole system is G1's modulus cap (FINDING 1), and the only forced choice the
graded side makes is `κ ≥ 53/50` on `L` (FINDING 2).**

## ⟦THE BINDER ENUMERATION⟧ (the PORT-AUDIT lesson: no under-counted residue lists)

Each family theorem's docstring below enumerates EVERY binder it carries, in named groups.
The headline count for the deliverable `usetGChi_window_meansq_gated_family` is:
**the graded `𝒰`-package (21) + the per-`j` block gates (7) + the ambient height/scale gates
(13) + `Rbd` (2) + the Lemma-12 row `E` (2) + the socket floor `T₀ ≤ T` and G1–G4 (5) + the
`𝔄`-package (3) + the well-formedness binders (8)** — see §4 for the itemisation.  Nothing is
absorbed and nothing is left implicit.

## Sign convention (CATCH #B ∘ N1)

Inherited unchanged: `ramQ`/`ramR`/`ramMain` and every branch set are at `σ = 1`; the single
crossing to `dpolyChi`'s `n^{+it}` happens inside the landed `ramRChi_sq_sum_phi`.  **This
file performs no negation and no reflection anywhere.**

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 eq (21), pp. 16–17 (Lemma 9), pp. 27–29
(§8.3); KMT §6 (Lemmas 6.2/6.5); `docs/exploration/a4-bridge-freeze-0730.md` v2.3.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §1 — ⟦ii-5⟧ the `𝒯_S` branch exit at the GRADED pair set -/

/-- **⟦ii-5⟧ — U-5 AT THE GRADED THRESHOLD, `φ(q)`-graded row, UNCONDITIONAL.**  The graded
twin of `HalaszIntegersChiClose.usetChi_TS_branch_meanvalue_phi`: once the GRADED razor's
budget clears the co-factor length (`thinBundleGChi·X^{1−2η+ε} ≤ M`), the `𝒯_S` branch is
priced at `5128·φ(q)·ε_Q²·M·(1 + log 2T)·(co-factor mass)`.  The Halász term has vanished —
that is what the graded `𝒰`-thinness bought — and the razor's own character debit rode inside
the exponent `ε` (`charDebit_le_rpow`).  The remaining `φ(q)` is repaid by
`usetGChi_TS_branch_exit_repinned`.

⟦WHAT IS REUSED VERBATIM AND WHY⟧ `TSChi_branch_meansq_phi` — hence `halaszIntegersChi_phi`,
the `φ(q)`-graded Lemma 9 — is **level-agnostic**: it quantifies over an arbitrary coefficient
sequence and an arbitrary per-fibre well-spaced pair set and mentions no partition at all.  So
the branch engine does not know that the threshold moved from the flat `δ` to MR (21)'s graded
one, and it re-instantiates unchanged.  The ONLY graded input is `hU`/`hbudget`.

⟦THE BINDERS⟧ (i) the graded `𝒰`-package: `f`, `hf1`, `Pseq`, `Qseq`, `Hseq`, `αseq`, `J`,
`Jb`, `hJb1`, `hJbJ`, `hH2`, `hα0`, `VJ`, `hVJ`, `hP3`, `hPQ`, `hQT`, `hκ30`, `hU`;
(ii) the razor exponents: `η`, `X`, `ε`, `hα`, `hη2`, `hTX`, `hX0`, `hdebit`, `hbudget`;
(iii) the ambient height gates: `T`, `hT1`, `hqT`, `hLL5`; (iv) the pair set: `ℰ`, `hws`,
`hsub`; (v) the branch datum: `H`, `N`, `Xd`, `P`, `Q`, `j`, `M`, `b`, `cf`, `εQ`, `hM`.
Note `δ`, `hδ0`, `hV`, `hVinv` and `hVα` of the flat twin are ABSENT (FINDING 3). -/
theorem usetGChi_TS_branch_meanvalue_phi (q : ℕ) [NeZero q] (f : ℕ → ℂ)
    (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb)
    (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetGChi q f Pseq Qseq Hseq αseq J)
    (η X ε : ℝ) (hα : αseq Jb ≤ 1 / 4 - η) (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) (hX0 : 0 < X)
    (hdebit : (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε)
    (H : ℝ) (N Xd P Q j M : ℕ) (b cf : ℕ → ℂ) (εQ : ℝ)
    (hM : ramRrange H N Xd j ⊆ Finset.Icc 1 M)
    (hbudget : thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
        * X ^ (1 - 2 * η + ε) ≤ (M : ℝ)) :
    ∑ r ∈ TsetSmallChi q H P Q j cf εQ ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 cf) j r.2‖ ^ 2
      ≤ 5128 * (q.totient : ℝ) * εQ ^ 2 * (M : ℝ) * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  have hbranch := TSChi_branch_meansq_phi q H N Xd P Q j M b cf hM εQ T hT1 ℰ hws hsub
  have hkill := UsetGChi_thin_sqrt_kill_absorbed q f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ
    hH2 hα0 T VJ hT1 hqT hP3 hPQ hQT hκ30 hLL5 hVJ ℰ hws hsub hU η X ε hα hη2 hTX hX0 hdebit
  have hcnt : (ℰ.card : ℝ) * Real.sqrt T ≤ (M : ℝ) := le_trans hkill hbudget
  have hφ1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
    have h := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast h
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  refine hbranch.trans ?_
  have hbr : (q.totient : ℝ) * (M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T
      ≤ 2 * ((q.totient : ℝ) * (M : ℝ)) := by nlinarith [hcnt, hφ1, hM0]
  have hstep : 2564 * ((q.totient : ℝ) * (M : ℝ) + (ℰ.card : ℝ) * Real.sqrt T)
        * (1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
      ≤ 5128 * (q.totient : ℝ) * (M : ℝ) * (1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) := by
    have hcoef : (0 : ℝ) ≤ 2564 * ((1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hbr hcoef]
  nlinarith [mul_le_mul_of_nonneg_left hstep (sq_nonneg εQ)]

/-- **⟦ii-5⟧ — THE GRADED `𝒯_S` EXIT, RE-PINNED, AT THE `q = 1` GRADE, UNCONDITIONAL.**

At the port's modulus gate `q ≤ (log X)^{12}` and the branch level `ε_Q = (log X)^{−106}`,

  `Σ_{𝒯_S} ‖Q_{j,H}·R_{j,H}(χ̄, 1+it)‖² ≤ 5128·(log X)^{−200}·M·(1 + log 2T)·(co-factor mass)`

on the GRADED pair set — byte-for-byte the flat exit
`HalaszIntegersChiClose.usetChi_TS_branch_exit_repinned`, and byte-for-byte MR's own `q = 1`
grade (`USetThinTS.uset_TS_branch_meanvalue` at `ε = (log X)^{−100}`).  The `φ(q)` debit page
(`phi_debit_level_repin`: `φ(q)·ε_Q² ≤ (log X)^{12}·(log X)^{−212} = (log X)^{−200}`) is
character- AND partition-blind, so it is reused verbatim — the graded threshold costs the
branch exit nothing at all.

⟦THE BINDERS⟧ exactly those of `usetGChi_TS_branch_meanvalue_phi` with `εQ` REMOVED (it is
pinned to `(log X)^{−106}` in-statement) and two added: `hL0 : 0 < log X` and
`hqlog : q ≤ (log X)^{12}`, the modulus gate the repayment is charged to. -/
theorem usetGChi_TS_branch_exit_repinned (q : ℕ) [NeZero q] (f : ℕ → ℂ)
    (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb)
    (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetGChi q f Pseq Qseq Hseq αseq J)
    (η X ε : ℝ) (hα : αseq Jb ≤ 1 / 4 - η) (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) (hX0 : 0 < X)
    (hdebit : (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε)
    (hL0 : 0 < Real.log X) (hqlog : (q : ℝ) ≤ (Real.log X) ^ 12)
    (H : ℝ) (N Xd P Q j M : ℕ) (b cf : ℕ → ℂ)
    (hM : ramRrange H N Xd j ⊆ Finset.Icc 1 M)
    (hbudget : thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
        * X ^ (1 - 2 * η + ε) ≤ (M : ℝ)) :
    ∑ r ∈ TsetSmallChi q H P Q j cf ((Real.log X) ^ (-106 : ℝ)) ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 cf) j r.2‖ ^ 2
      ≤ 5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * T))
          * ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 := by
  have hraw := usetGChi_TS_branch_meanvalue_phi q f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ
    hH2 hα0 T VJ hT1 hqT hP3 hPQ hQT hκ30 hLL5 hVJ ℰ hws hsub hU η X ε hα hη2 hTX hX0 hdebit
    H N Xd P Q j M b cf ((Real.log X) ^ (-106 : ℝ)) hM hbudget
  refine hraw.trans ?_
  have hrepin := phi_debit_level_repin q X hL0 hqlog
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hlog : (0 : ℝ) ≤ 1 + Real.log (2 * T) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith)
    linarith
  have hmass : (0 : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun m _ => by positivity)
  have hcoef : (0 : ℝ) ≤ 5128 * ((M : ℝ) * ((1 + Real.log (2 * T))
      * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2))) := by
    have h1 : (0 : ℝ) ≤ (1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2) :=
      mul_nonneg hlog hmass
    have h2 : (0 : ℝ) ≤ (M : ℝ) * ((1 + Real.log (2 * T))
        * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)) :=
      mul_nonneg hM0 h1
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hrepin hcoef]

/-! ## §2 — ⟦ii-6⟧ THE FIBREWISE FAMILY BRIDGE: continuous → discrete, per fibre

C2-SCOPE's Finding A3-2: `USetChiTS.usetChi_integral_to_branches` is the **only** place in the
corpus where one `A : Set ℝ` is fixed across all characters — the discrete level is already
pair-native in eight files, and the continuous side is fibrewise everywhere else.  This
section re-cuts that single pinch at the ratified pair spelling.  It is a RESTATEMENT at a
more general binder, added beside the flat one: `usetChi_integral_to_branches` is untouched
and remains the `𝔄 = (characters) × A` special case. -/

set_option maxHeartbeats 800000 in
-- Same cause as the flat twin: the composition threads the eq-(16) decomposition, the
-- per-character discretisation and the pair-level branch split through one another, and the
-- unifier needs room for the composed `ramMain`/`spoly` expressions at twisted data.
/-- **⟦ii-6⟧ — U-9b AT THE FIBREWISE FAMILY BINDER.**  For a pair set
`𝔄 : Set (DirichletCharacter ℂ q × ℝ)` whose every character fibre is measurable and whose
ordinates lie in `[−T,T]`, with branch bounds `Sb j`, `Lb j` valid for EVERY per-fibre
well-spaced pair set drawn **from `𝔄` itself**:

  `Σ_χ ∫_{𝔄_χ} ‖Σ_{n≤N} χ̄(n)aₙ/n^{1+it}‖² ≤ 4·|I|·Σ_{j∈I} (Sb j + Lb j) + 2E`,
  `𝔄_χ := {t | (χ,t) ∈ 𝔄}`.

The three factors are the landed ones: `2·|I|` the eq-(16) Cauchy–Schwarz across blocks
(`meansq_on_subset_of_decomp`, character-blind, applied at the fibre `𝔄_χ` of each `χ`), the
extra `2` the even/odd parity halving of `wellspaced_discretize` (also per fibre), and `E` the
`χ`-SUMMED Lemma-12 error row (`HybridMoments.lemma12_meansq_all_chi`).

⟦WHAT THE RE-CUT COSTS: NOTHING⟧ the flat proof already ran per character and only assembled
at the pack; `fibrePack` is exactly the inverse of `exists_charFibre`, so the packed witness
set lands in `𝔄` **pairwise** rather than fibre-by-fibre-into-one-`A`.  The single `A ⊆ [−T,T]`
becomes `∀ r ∈ 𝔄, r.2 ∈ [−T,T]` and the single `MeasurableSet A` becomes the fibrewise family
`hAm` — which is precisely C2's design (ii), and (by `Set (χ × ℝ) ≅ (χ → Set ℝ)`) also its
design (iii), at zero extra generality and zero extra measure theory.

⟦THE BINDERS⟧ (i) the datum: `H`, `N`, `Xd`, `P`, `Q`, `a`, `b`, `cf`; (ii) the height and
error row: `T`, `E`, `hT`, `herr`; (iii) the `𝔄`-package: `𝔄`, `hAm`, `hAsub`; (iv) the split
level and the two branch bounds: `δ'`, `Sb`, `Lb`, `hTS`, `hTL`. -/
theorem usetGChi_integral_to_branches_family (q : ℕ) [NeZero q]
    (H : ℝ) (N Xd P Q : ℕ) (a b cf : ℕ → ℂ) (T E : ℝ) (hT : 0 ≤ T)
    (herr : (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
        ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E)
    (𝔄 : Set (DirichletCharacter ℂ q × ℝ))
    (hAm : ∀ χ : DirichletCharacter ℂ q, MeasurableSet {t : ℝ | (χ, t) ∈ 𝔄})
    (hAsub : ∀ r ∈ 𝔄, r.2 ∈ Set.Icc (-T) T)
    (δ' : ℝ) (Sb Lb : ℕ → ℝ)
    (hTS : ∀ j ∈ ramI H P Q, ∀ ℰ : Finset (DirichletCharacter ℂ q × ℝ),
      FibreWellSpaced ℰ → (∀ r ∈ ℰ, r ∈ 𝔄) →
      (∑ r ∈ TsetSmallChi q H P Q j cf δ' ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 cf) j r.2‖ ^ 2) ≤ Sb j)
    (hTL : ∀ j ∈ ramI H P Q, ∀ ℰ : Finset (DirichletCharacter ℂ q × ℝ),
      FibreWellSpaced ℰ → (∀ r ∈ ℰ, r ∈ 𝔄) →
      (∑ r ∈ tLsetChi q H P Q j cf δ' ℰ,
        ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 cf) j r.2‖ ^ 2) ≤ Lb j) :
    (∑ χ : DirichletCharacter ℂ q,
        ∫ t in {t : ℝ | (χ, t) ∈ 𝔄}, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
      ≤ 4 * ((ramI H P Q).card : ℝ) * (∑ j ∈ ramI H P Q, (Sb j + Lb j)) + 2 * E := by
  classical
  -- the fibre of `𝔄` at `χ` sits inside `[−T,T]`
  have hfib : ∀ χ : DirichletCharacter ℂ q, {t : ℝ | (χ, t) ∈ 𝔄} ⊆ Set.Icc (-T) T :=
    fun χ t ht => hAsub (χ, t) ht
  -- (i) eq (16) on each fibre, the error kept as its own full-range integral
  have hstep1 : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in {t : ℝ | (χ, t) ∈ 𝔄}, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ 2 * ((ramI H P Q).card : ℝ)
            * (∑ j ∈ ramI H P Q, ∫ t in {t : ℝ | (χ, t) ∈ 𝔄},
                ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2)
          + 2 * (∫ t in (-T)..T, ‖ramErr H N Xd P Q (chiBarCoeff q χ a)
              (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) := by
    intro χ
    exact meansq_on_subset_of_decomp (N := N) (a := chiBarCoeff q χ a) (I := ramI H P Q)
      (mainPoly := ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf))
      (errPoly := ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
        (chiBarCoeff q χ cf))
      (E := ∫ t in (-T)..T, ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
        (chiBarCoeff q χ cf) t‖ ^ 2)
      (T := T) (A := {t : ℝ | (χ, t) ∈ 𝔄}) hT (hAm χ) (hfib χ)
      (fun j _ => continuous_ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j)
      (continuous_ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
        (chiBarCoeff q χ cf))
      (fun t => spoly_ram_decomp H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
        (chiBarCoeff q χ cf) t)
      (le_refl _)
  -- (ii) per block: discretise every fibre, pack into ONE pair subset of `𝔄`, split at `δ'`
  have hper : ∀ j ∈ ramI H P Q,
      (∑ χ : DirichletCharacter ℂ q, ∫ t in {t : ℝ | (χ, t) ∈ 𝔄},
          ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2)
        ≤ 2 * (Sb j + Lb j) := by
    intro j hj
    have hdisc : ∀ χ : DirichletCharacter ℂ q, ∃ 𝒯 : Finset ℝ,
        (↑𝒯 : Set ℝ) ⊆ {t : ℝ | (χ, t) ∈ 𝔄} ∧ WellSpaced 𝒯 ∧
        (∫ t in {t : ℝ | (χ, t) ∈ 𝔄},
            ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2)
          ≤ 2 * ∑ t ∈ 𝒯,
            ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2 := by
      intro χ
      exact wellspaced_discretize T
        (fun t => ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2)
        ((continuous_ramMain H N Xd P Q (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) j).norm.pow 2)
        (fun t => by positivity) {t : ℝ | (χ, t) ∈ 𝔄} (hAm χ) (hfib χ)
    choose 𝒯 h𝒯A hws hle using hdisc
    have hpack_sub : ∀ r ∈ fibrePack 𝒯, r ∈ 𝔄 := by
      intro r hr
      have hmem : (r.1, r.2) ∈ 𝔄 := h𝒯A r.1 (Finset.mem_coe.mpr (mem_fibrePack.mp hr))
      simpa using hmem
    have hpack_ws : FibreWellSpaced (fibrePack 𝒯) := fibreWellSpaced_fibrePack 𝒯 hws
    have hregroup : (∑ χ : DirichletCharacter ℂ q, ∑ t ∈ 𝒯 χ,
          ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2)
        = ∑ r ∈ fibrePack 𝒯,
          ‖ramMain H N Xd P Q (chiBarCoeff q r.1 b) (chiBarCoeff q r.1 cf) j r.2‖ ^ 2 :=
      (sum_fibrePack 𝒯 (fun χ t =>
        ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2)).symm
    have hsplit := sum_TSChi_add_TLChi q H N Xd P Q j b cf δ' (fibrePack 𝒯)
    have h1 := hTS j hj (fibrePack 𝒯) hpack_ws hpack_sub
    have h2 := hTL j hj (fibrePack 𝒯) hpack_ws hpack_sub
    have hsum : (∑ χ : DirichletCharacter ℂ q, ∫ t in {t : ℝ | (χ, t) ∈ 𝔄},
          ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2)
        ≤ 2 * ∑ χ : DirichletCharacter ℂ q, ∑ t ∈ 𝒯 χ,
            ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun χ _ => hle χ)
    rw [hregroup, ← hsplit] at hsum
    linarith
  -- (iii) assemble
  have hchi := Finset.sum_le_sum
    (fun (χ : DirichletCharacter ℂ q) (_ : χ ∈ Finset.univ) => hstep1 χ)
  have hdistrib : (∑ χ : DirichletCharacter ℂ q,
        (2 * ((ramI H P Q).card : ℝ)
            * (∑ j ∈ ramI H P Q, ∫ t in {t : ℝ | (χ, t) ∈ 𝔄},
                ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2)
          + 2 * (∫ t in (-T)..T, ‖ramErr H N Xd P Q (chiBarCoeff q χ a)
              (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2)))
      = 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∑ χ : DirichletCharacter ℂ q,
              ∫ t in {t : ℝ | (χ, t) ∈ 𝔄},
              ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2)
        + 2 * (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
            ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
              (chiBarCoeff q χ cf) t‖ ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  rw [hdistrib] at hchi
  have hblocks : (∑ j ∈ ramI H P Q, ∑ χ : DirichletCharacter ℂ q,
        ∫ t in {t : ℝ | (χ, t) ∈ 𝔄},
        ‖ramMain H N Xd P Q (chiBarCoeff q χ b) (chiBarCoeff q χ cf) j t‖ ^ 2)
      ≤ 2 * ∑ j ∈ ramI H P Q, (Sb j + Lb j) := by
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [← Finset.mul_sum]
  have hcard0 : (0 : ℝ) ≤ 2 * ((ramI H P Q).card : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hblocks hcard0
  linarith

/-! ## §3 — ⟦ii-6⟧ THE GRADED 𝒰-EXIT COMPOSE at the fibrewise family binder

`usetGChi_integral_to_branches_family` with both branch bounds substituted:

* the **`𝒯_S` branch** at the re-pinned level `ε_Q = (log X)^{−106}` and the GRADED thinness
  (§1's `usetGChi_TS_branch_exit_repinned`) — unconditional;
* the **`𝒯_L` branch** (`USetChi.tLChi_main_sumsq`) at the SAME level, which is where the pair
  socket is spent.  That rung's binders are ALREADY pair-native — no `A`, no partition — so it
  is consumed here exactly as `PortClose` §3 consumes it, with `r.2 ∈ A` replaced by `r ∈ 𝔄`.

⟦THE SOCKET, POINTWISE⟧ as in `PortClose` §3, the socket enters as
`hslot : HalaszPrimesChi Cs cs q T` at THIS compose's own `(q, T)`; §4 discharges it. -/

set_option maxHeartbeats 800000 in
-- Same cause as `PortClose` §3: the compose threads two branch exits (each with a dozen
-- in-statement gates) through the χ-summed eq-(16) composition.
/-- **⟦ii-6⟧ ⟦A3, GRADED + FIBREWISE⟧ THE 𝒰-EXIT, COMPOSED.**  The `χ`-summed window mean
square of the twisted Dirichlet polynomial on the FIBRES of a pair set
`𝔄 ⊆ UsetGChi …` (the consumer's `(Ann ∖ ball) ∩ 𝒰` read at the graded threshold, fibrewise),
from the pair socket, the landed `φ(q)`-graded integers row, the GRADED `𝒰`-thinness and the
Lemma-12 error row.

The two branch prices are visible in the bound: `5128·(log X)^{−200}·M·(1+log 2T)·(mass)` on
`𝒯_S` — byte-for-byte MR's `q = 1` grade — and `81·Cs·Rbd²·(H/j)²` on `𝒯_L`.  Compare
`PortClose.usetChi_window_meansq_of_socket`: the exits are IDENTICAL; what moved is the
`𝒰`-genre (`UsetGChi` for `UsetChi`, `thinBundleGChi` for `thinBundleChi`) and the shape of
the set binder.

⟦THE BINDERS, ENUMERATED (no under-counted residue lists)⟧

1. **the graded `𝒰`-package (19)** — `f`, `hf1`, `Pseq`, `Qseq`, `Hseq`, `αseq`, `J`, `Jb`,
   `hJb1`, `hJbJ`, `hH2seq`, `hα0`, `VJ`, `hVJ`, `hP3`, `hPQ`, `hQT`, `hκ30Q`, `hUA`;
2. **the razor exponents and the budget (9)** — `η`, `X`, `ε`, `hα`, `hη2`, `hTX`, `hX0`,
   `hdebit`, `hbudget`;
3. **the per-`j` block gates (7)**, uniform on `ramI H P Q` — `hHj`, `hB3`, `hBT`, `hκ30`,
   `hBT10`, `hWL`, `hgate`;
4. **the ambient height/scale gates (9)** — `hT1`, `hqT`, `hLL5`, `hL0`, `hqlog`, `hlogT1`,
   `hTL`, `hLe`, `hlogV`;
5. **the `𝒯_L` level data (3)** — `V`, `hV1`, `hVδ`;
6. **`Rbd` (2)** — the pointwise co-factor bound on `𝒯_L`, `Rbd` and `hRbd` (NOT a
   `𝒰`-property: the landed rung says so, and the ladder cannot supply it);
7. **the Lemma-12 error row (2)** — `E`, `herr`;
8. **the socket (3)** — `Cs`, `cs` with `hCs`, `hcs`, and `hslot` (§4 removes `hslot`);
9. **the `𝔄`-package (3)** — `𝔄`, `hAm`, `hAsub`;
10. **the well-formedness binders (10)** — `q`, `[NeZero q]`, `T`, `L`, `H`, `hH2`, the datum
    `N Xd P Q M a b cf`, `hcf1`, `hM`: normalisation, range and boundedness conditions with no
    analytic content.

ABSENT relative to the flat twin (FINDING 3 of §0): `δ`, `hδ0`, `hVinv`, `hVα` — and `V` no
longer doubles as the thinness level. -/
theorem usetGChi_window_meansq_of_socket_family
    {Cs cs : ℝ} (hCs : 0 < Cs) (hcs : 0 < cs)
    (q : ℕ) [NeZero q] (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2seq : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ V L X : ℝ) (hslot : HalaszPrimesChi Cs cs q T)
    (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb)
    (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T)
    (hκ30Q : 30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (η ε : ℝ) (hα : αseq Jb ≤ 1 / 4 - η) (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) (hX0 : 0 < X)
    (hdebit : (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε)
    (hL0 : 0 < Real.log X) (hqlog : (q : ℝ) ≤ (Real.log X) ^ 12)
    (hV1 : 1 ≤ V) (hVδ : V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ))
    (hlogT1 : 1 ≤ Real.log ((q : ℝ) * T))
    (hTL : Real.log ((q : ℝ) * T) ≤ L) (hLe : Real.exp 1 ≤ L)
    (hlogV : Real.log V ≤ 100 * Real.log L)
    (H : ℝ) (hH2 : 2 ≤ H) (N Xd P Q M : ℕ) (a b cf : ℕ → ℂ) (hcf1 : ∀ n : ℕ, ‖cf n‖ ≤ 1)
    (hM : ∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 M)
    (hbudget : thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
        * X ^ (1 - 2 * η + ε) ≤ (M : ℝ))
    (hHj : ∀ j ∈ ramI H P Q, H ≤ (j : ℝ))
    (hB3 : ∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j)
    (hBT : ∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : ∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j))
    (hBT10 : ∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ T ^ 10)
    (hWL : ∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L)
    (hgate : ∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
      ≤ cs * (Real.log (ramQbase H P j)) ^ 2)
    (Rbd : ℝ) (hRbd : 0 ≤ Rbd)
    (𝔄 : Set (DirichletCharacter ℂ q × ℝ))
    (hAm : ∀ χ : DirichletCharacter ℂ q, MeasurableSet {t : ℝ | (χ, t) ∈ 𝔄})
    (hAsub : ∀ r ∈ 𝔄, r.2 ∈ Set.Icc (-T) T)
    (hUA : 𝔄 ⊆ UsetGChi q f Pseq Qseq Hseq αseq J)
    (hR : ∀ j ∈ ramI H P Q, ∀ r ∈ 𝔄,
      ‖ramR H N Xd P Q j (chiBarCoeff q r.1 b) r.2‖ ≤ Rbd)
    (E : ℝ)
    (herr : (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
        ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E) :
    (∑ χ : DirichletCharacter ℂ q,
        ∫ t in {t : ℝ | (χ, t) ∈ 𝔄}, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
      ≤ 4 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q,
              (5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * T))
                  * (∑ m ∈ Finset.Icc 1 M,
                      ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
                + 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2))
        + 2 * E := by
  refine usetGChi_integral_to_branches_family q H N Xd P Q a b cf T E (by linarith) herr
    𝔄 hAm hAsub ((Real.log X) ^ (-106 : ℝ))
    (fun j => 5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * T))
      * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2))
    (fun j => 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2) ?_ ?_
  · -- ⟦the `𝒯_S` branch⟧ §1's re-pinned GRADED exit, unconditional
    intro j hj ℰ hws hsub𝔄
    exact usetGChi_TS_branch_exit_repinned q f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ
      hH2seq hα0 T VJ hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ ℰ hws
      (fun r hr => hAsub r (hsub𝔄 r hr)) (fun r hr => hUA (hsub𝔄 r hr))
      η X ε hα hη2 hTX hX0 hdebit hL0 hqlog H N Xd P Q j M b cf (hM j hj) hbudget
  · -- ⟦the `𝒯_L` branch⟧ the pair socket, spent once per block (binders already pair-native)
    intro j hj ℰ hws hsub𝔄
    exact tLChi_main_sumsq hCs hcs q hH2 P Q j N Xd cf b hcf1 (hHj j hj) T V L
      ((Real.log X) ^ (-106 : ℝ)) Rbd hslot ℰ hws (fun r hr => hAsub r (hsub𝔄 r hr)) hT1 hqT
      (hB3 j hj) (hBT j hj) (hκ30 j hj) hLL5 hV1 hVδ (hBT10 j hj) hTL hlogT1 hLe (hWL j hj)
      hlogV (hgate j hj) hRbd
      (fun r hr => hR j hj r
        (hsub𝔄 r (tLsetChi_subset q H P Q j cf ((Real.log X) ^ (-106 : ℝ)) ℰ hr)))

/-! ## §4 — ⟦ii-6⟧ THE DELIVERABLE: the graded fibrewise `𝒰`-exit with the SOCKET GONE

§3's compose at `PortClose` §2's discharged socket.  `hslot` leaves the hypothesis list; what
replaces it is the per-`(q,T)` floor — `T₀ ≤ T` and the four gates G1–G4 — carried
in-statement, verbatim.  §0's ⟦K-5 CHECK⟧ is the verification that this list is jointly
satisfiable: **COMPATIBLE**, at the x-scale door regime exhibited there. -/

set_option maxHeartbeats 800000 in
-- Same cause as §3: the composed statement carries the ladder's full gate list.
/-- **⟦ii-6 — THE C2 DELIVERABLE⟧ ⟦A3, GRADED + FIBREWISE + GATED⟧.**  The `χ`-summed window
mean square of the twisted Dirichlet polynomial on the fibres of a pair set
`𝔄 ⊆ UsetGChi …`, with `HalaszPrimesChi` DISCHARGED by `PortClose` §2's pair row: the
constants `Cs, cs, T₀, Kq, Ks` are the port's own (`Ks` ineffective, Siegel; the rest
effective), and the socket's cost appears as the four `q`-vs-`T` gates.

This is `PortClose.usetChi_window_meansq_gated` re-cut at BOTH ratified moves at once — the
graded threshold (⟦THE THRESHOLD WALL⟧: the flat `𝒰` is structurally unusable by every landed
row) and C2's fibrewise pair binder — and it is additive: the flat statement is untouched.

⟦THE RESIDUE, ENUMERATED — every binder, in named groups⟧

1. **the graded `𝒰`-package (19)** — `f`, `hf1`, `Pseq`, `Qseq`, `Hseq`, `αseq`, `J`, `Jb`,
   `hJb1`, `hJbJ`, `2 ≤ Hseq Jb`, `0 ≤ αseq Jb`, `VJ`, `hVJ`, `3 ≤ Pseq Jb`,
   `Pseq Jb ≤ Qseq Jb`, `Qseq Jb ≤ qT`, the X₀ law `30 ≤ log(qT)/log(Qseq Jb)`, and the
   membership `𝔄 ⊆ UsetGChi …`;
2. **the razor exponents and the budget (9)** — `η`, `X`, `ε`, `αseq Jb ≤ 1/4 − η`, `2η ≤ 1`,
   `T ≤ X`, `0 < X`, the debit `q^{2α} ≤ X^ε`, and
   `thinBundleGChi(qT,VJ,H_Jb,P_Jb,Q_Jb)·X^{1−2η+ε} ≤ M`;
3. **the per-`j` block gates (7)**, uniform on `ramI H P Q` — `H ≤ j`, `3 ≤ ramQbase`,
   `ramQbase ≤ qT`, `30 ≤ log(qT)/log ramQbase`, `ramQbase ≤ T^{10}`, `log ramQbase ≤ L`, and
   the socket-price gate `420·L·L^{3/4}(log L)^5 ≤ cs·(log ramQbase)²`;
4. **the ambient height/scale gates (9)** — `1 ≤ T`, `1 < qT`, `5 ≤ loglog(qT)`, `0 < log X`,
   `q ≤ (log X)^{12}`, `1 ≤ log(qT)`, `log(qT) ≤ L`, `e ≤ L`, `log V ≤ 100 log L`;
5. **the `𝒯_L` level data (3)** — `V`, `1 ≤ V`, `V⁻¹ ≤ (log X)^{−106}`;
6. **`Rbd` (2)** — the pointwise co-factor bound on `𝒯_L` and its nonnegativity (NOT a
   `𝒰`-property; the ladder cannot supply it);
7. **the Lemma-12 error row (2)** — `E` and `herr` (`HybridMoments.lemma12_meansq_all_chi`
   supplies it);
8. **the per-`(q,T)` floor (5)** — `T₀ ≤ T` and G1–G4, the price of the socket's discharge;
9. **the `𝔄`-package (3)** — `𝔄`, the fibrewise measurability `hAm`, and
   `∀ r ∈ 𝔄, r.2 ∈ [−T,T]`;
10. **the well-formedness binders (10)** — `q`, `[NeZero q]`, `T`, `L`, `H`, `2 ≤ H`, the datum
    `N Xd P Q M a b cf`, `‖cf n‖ ≤ 1`, and the range condition `hM`.

⟦THE FOUR LOG SCALES, kept apart⟧ the gates read `log(5T+1)`, the socket's decay denominator
reads `log(qT)`, the count and the kill read `L ≥ log(qT)`, and the `𝒯_S` level reads `log X`.
None of the four is substituted for another anywhere in this statement, and §0's K-5 walk
checks the combined list at one named regime. -/
theorem usetGChi_window_meansq_gated_family :
    ∃ Cs cs T₀ Kq Ks : ℝ, 0 < Cs ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (f : ℕ → ℂ), (∀ n : ℕ, ‖f n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (T VJ V L X : ℝ), 1 ≤ T → 1 < (q : ℝ) * T →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T →
        30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * T)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → T ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        -- ⟦THE PER-`(q,T)` FLOOR — what the socket's discharge costs⟧
        T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * T) → Real.log ((q : ℝ) * T) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q M : ℕ) (a b cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 M) →
        thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ (M : ℝ) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * T) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ T ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ 𝔄 : Set (DirichletCharacter ℂ q × ℝ),
        (∀ χ : DirichletCharacter ℂ q, MeasurableSet {t : ℝ | (χ, t) ∈ 𝔄}) →
        (∀ r ∈ 𝔄, r.2 ∈ Set.Icc (-T) T) →
        𝔄 ⊆ UsetGChi q f Pseq Qseq Hseq αseq J →
        (∀ j ∈ ramI H P Q, ∀ r ∈ 𝔄,
          ‖ramR H N Xd P Q j (chiBarCoeff q r.1 b) r.2‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        (∑ χ : DirichletCharacter ℂ q,
            ∫ t in {t : ℝ | (χ, t) ∈ 𝔄}, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (∑ j ∈ ramI H P Q,
                  (5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * T))
                      * (∑ m ∈ Finset.Icc 1 M,
                          ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
                    + 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2))
            + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hT₀, hKq, hKs, hpt⟩ :=
    halaszPrimesChi_pointwise_of_gates
  refine ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hT₀, hKq, hKs, ?_⟩
  intro q _ f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 T VJ V L X hT1 hqT hP3 hPQ
    hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV H hH2 N Xd P Q M a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL
    hgate Rbd hRbd 𝔄 hAm hAsub hUA hR E herr
  exact usetGChi_window_meansq_of_socket_family hCs hcs q f hf1 Pseq Qseq Hseq αseq J Jb
    hJb1 hJbJ hH2seq hα0 T VJ V L X (hpt q T hT₀T hG1 hG2 hG3 hG4) hT1 hqT hP3 hPQ hQT
    hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hlogT1 hTL hLe hlogV
    H hH2 N Xd P Q M a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd
    𝔄 hAm hAsub hUA hR E herr

end Salt.MR
