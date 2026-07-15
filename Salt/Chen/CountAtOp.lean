/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.CountW
import Salt.Chen.HeadlineW2
import Salt.Chen.PackB

/-!
# HCOUNT — the count chain composed at the operating point (`hcount_at_op`)

Design: `docs/blueprints/flags.md`, the `2026-07-15 PACK-A/PACK-B` entry (HCOUNT's enumerated
pieces) and the `2026-07-14 GLU-1`/`CNTW` entries (the count-chain map; the ledger is
`X_W`-relative).

## The target slot

`GlueNormalized.normalized_package` (`GlueNormalized.lean:232`) and its W-composition
regression (`CountW.lean:749`) consume the `hcount` slot

  `hcount : Real.log x · T ≤ (cbar + ecount) · totalMass`

with `T = tripleSumW opQ opA x (opZ x) (opY x)` the A₃ main count factor and
`totalMass = totalMassSmooth / φ(opQ)` the smooth window mass, `totalMassSmooth =
∑_{n ∈ twinWindow x} Λ n` (`TwinA1W.twinA1SieveW_totalMass`).  So the concrete op slot is

  `Real.log x · tripleSumW opQ opA x (opZ x) (opY x)
      ≤ (cbar + ecount) · ((∑ n ∈ twinWindow x, Λ n) / φ(opQ))`.                    (SLOT)

## The keystone (enumerated)

`CountW.tripleSum_le_cbar_final_W {A C}` (`Salt/Chen/CountW.lean:679`) delivers, for `A,C > 0`,
a `Ksw > 0` and threshold `N₀` such that at any AP witnesses `(Q,a,x,zN,yN)` with real carriers
`(zR,yR)`, under

* the AP rows: `0 < Q`, `Coprime Q (a+2)`, `∀ p prime ∣ Q → p < zN`,
  `3 ≤ Lval x yN`, `N₀ ≤ Lval x yN`, `(Q:ℝ) ≤ (log (Lval x yN))^C`;
* the landed keystone geometry rows (verbatim `CountFinal.tripleSum_le_cbar_final`):
  `1 < x`, `2 ≤ zR`, `zR ≤ yR`, `log zR = log x/8`, `log yR = log x/3`,
  the floor brackets `(zN:ℝ) ≤ zR ≤ zN+1`, `(yN:ℝ) ≤ yR ≤ yN+1`, and `4 ≤ log (Lval x yN)`,

a `K ≥ 0` with

  `tripleSumW Q a x zN yN
     ≤ ( LF·WF·(cbar/2)·(x/log x) + [ LF·WF·(x/2)·CORR + |pairSet'|/L₀ ] ) / φ(Q)
       + ( Ksw·x/(log (Lval x yN))^A · Σ_{pairSet} 1/(p₁p₂) + 2·|pairSet| )`,

where `LF = 1 + 3K/L₀`, `WF = 1 + 4log2/log(2·Lval x yN)`, `L₀ = log (Lval x yN)`, and
`CORR = Ifun(x,yR,zN)/zN + Ifun(x,yR,yN)/yN + (21/log zR)·Ifun(x,yR,zR)
        + Σ_{p₁ ∈ S1set} (1/p₁)·( hbjs(x,p₁,⌊√(x/p₁)⌋)/⌊√(x/p₁)⌋
                                  + (21/log yR)·hbjs(x,p₁,√(x/p₁)) )`
is the Abel-error/boundary-prime sum (the `o(x/log x)` pieces of `weightedPairSum'_le_cbar`).

## The two composition layers of HCOUNT

Writing `φ := φ(opQ)`, `M := ∑_{twinWindow x} Λ`, `T := tripleSumW opQ opA x (opZ x)(opY x)`:

**(1) The Λ-mass bridge (this module, FULLY CLOSED).**  `MertensPNT.lambda_mass_lower` gives the
window mass lower bound `M ≥ x/2 − 1 − 2·Kmass·x/log x =: massLo x Kmass` past `x ≥ 8`.  Since
`cbar + ecount ≥ 0` and `φ > 0`, the SLOT follows from the count-vs-`massLo` bound

  `log x · T ≤ (cbar + ecount) · (massLo x Kmass / φ)`                             (★)

by the monotonicity `massLo x Kmass ≤ M`.  This is `hcount_massBridge`.

**(2) The ecount extraction (DEFERRED — genuine analytic work, confirms the PackB gap list).**
Multiplying the keystone by `log x`, dividing by `φ` and comparing to (★) reduces to

  `log x·[LF·WF·(cbar/2)(x/log x) + Rem] + φ·log x·E_SW ≤ (cbar+ecount)·massLo x Kmass`,

i.e. absorbing the multiplicative slack `(LF·WF−1)·(cbar/2)·x`, `log x·Rem`, `φ·log x·E_SW`, and
the mass slack `cbar·(1 + 2·Kmass·x/log x)` into `ecount·massLo`.  With `massLo ≥ x/4` and
`log (opZ x) = log x/8`, the honest closed form is `ecount = C / log (opZ x)` with

  `C = cbar·(11·K + 12·log 2)/4 + (lower-order)`

(`K` the `psiTot_pnt` constant shared by the keystone slack and the mass slack; `12 log 2` from
`WF`; the lower-order pieces are `x^{−1/8}·polylog` boundary primes and the `x/(log x)^{11}`
strip from `E_SW`).  The three `o(x/log x)` sub-bounds this needs — an `Ifun` upper bound, an
`hbjs` boundary bound, and the `S1set` prime-reciprocal bound on `CORR` — have no landed
infrastructure yet (`AbelPass2` supplies only `Ifun_nonneg`/`Ifun_integral_eq_cbar`), so the
ecount extraction is left as three flagged sub-nodes.  See the module tail and `flags.md`.

## What is closed here

* `hcount_massBridge` — layer (1), fully closed via `lambda_mass_lower`.
* `hcount_op_geometry` — the eight landed-keystone geometry rows at op (real carriers
  `zR = x^{1/8}`, `yR = x^{1/3}`), fully closed.
* `hcount_op_AP3` — the three AP rows `0 < opQ`, `Coprime opQ (opA+2)`,
  `∀ p prime ∣ opQ → p < opZ x`, fully closed (`opf_*` + `opf_tower`).
* `hcount_at_op` — the SLOT, from (★) via the mass bridge, with `ecount` a free explicit real.
* the compiled slot `example` (matches `GlueNormalized.hmA3_normalized`'s `hcount` slot verbatim).

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace Salt.Chen

/-! ## Layer 1 — the Λ-mass bridge -/

/-- **`hcount_massBridge` — the window Λ-mass bridge (layer 1, FULLY CLOSED).**
`MertensPNT.lambda_mass_lower` supplies a fixed `Kmass ≥ 0` and threshold with
`x/2 − 1 − 2·Kmass·x/log x ≤ ∑_{twinWindow x} Λ` for `x ≥ 8`.  Hence for any `ecount` with
`cbar + ecount ≥ 0`, the GlueNormalized `hcount` SLOT against the true window mass follows from
the count-vs-`massLo` bound (★) by monotonicity of `t ↦ (cbar+ecount)·(t/φ(opQ))`.  This is the
honest reduction of HCOUNT to the count line's closure against the PNT lower mass. -/
theorem hcount_massBridge :
    ∃ (Kmass : ℝ) (x₁ : ℕ), 0 ≤ Kmass ∧ ∀ x : ℕ, x₁ ≤ x → ∀ ecount : ℝ, 0 ≤ cbar + ecount →
      Real.log x * tripleSumW opQ opA x (opZ x) (opY x)
          ≤ (cbar + ecount)
              * (((x : ℝ) / 2 - 1 - 2 * Kmass * x / Real.log x) / (opQ.totient : ℝ)) →
      Real.log x * tripleSumW opQ opA x (opZ x) (opY x)
          ≤ (cbar + ecount)
              * ((∑ n ∈ twinWindow x, vonMangoldt n) / (opQ.totient : ℝ)) := by
  obtain ⟨Kmass, hK0, hmass⟩ := lambda_mass_lower
  refine ⟨Kmass, 8, hK0, fun x hx ecount hce hbound => ?_⟩
  refine le_trans hbound ?_
  have hφ : (0 : ℝ) < (opQ.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr opf_Q_pos
  have hlow := hmass x hx
  gcongr

/-! ## The dischargeable keystone rows at the operating point

These feed `CountW.tripleSum_le_cbar_final_W`'s hypotheses at the op witnesses
`(opQ, opA, x, opZ x, opY x)` with the real carriers `zR = x^{1/8}`, `yR = x^{1/3}`.  They are
the packageable half of PACK-B's HCOUNT enumeration (the geometry rows and the three AP `(b)`
rows); the `Lval`/`Q ≤ (log Lval)^C` rows and the `CORR` bound are the deferred analytic half. -/

/-- **`hcount_op_geometry` — the eight landed-keystone geometry rows at op (FULLY CLOSED).**
With the real carriers `zR = x^{1/8}`, `yR = x^{1/3}`: `1 < x`, `2 ≤ zR`, `zR ≤ yR`,
`log zR = log x/8`, `log yR = log x/3`, and the floor brackets `(opZ x) ≤ zR ≤ opZ x + 1`,
`(opY x) ≤ yR ≤ opY x + 1`.  These are `tripleSum_le_cbar_final`'s geometry hypotheses verbatim
(the exact-geometry constraint `log zR = log x/8` is discharged by `Real.log_rpow`, NOT idealised
— cf. catch #75's A₂ exactness which cannot be reached; the count geometry IS exact at op). -/
theorem hcount_op_geometry {x : ℕ} (hx : 256 ≤ x)
    {zR yR : ℝ} (hzR : zR = (x : ℝ) ^ ((1 : ℝ) / 8)) (hyR : yR = (x : ℝ) ^ ((1 : ℝ) / 3)) :
    1 < (x : ℝ) ∧ (2 : ℝ) ≤ zR ∧ zR ≤ yR
      ∧ Real.log zR = Real.log x / 8 ∧ Real.log yR = Real.log x / 3
      ∧ (opZ x : ℝ) ≤ zR ∧ zR ≤ (opZ x : ℝ) + 1
      ∧ (opY x : ℝ) ≤ yR ∧ yR ≤ (opY x : ℝ) + 1 := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have : (256 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hx1 : (1 : ℝ) < (x : ℝ) := by
    have : (256 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hx256R : (256 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hzRpos : 0 < zR := by rw [hzR]; exact Real.rpow_pos_of_pos hxpos _
  have hyRpos : 0 < yR := by rw [hyR]; exact Real.rpow_pos_of_pos hxpos _
  have hlogzR : Real.log zR = Real.log x / 8 := by rw [hzR, Real.log_rpow hxpos]; ring
  have hlogyR : Real.log yR = Real.log x / 3 := by rw [hyR, Real.log_rpow hxpos]; ring
  -- `2 ≤ zR` via logs: `8·log 2 = log 256 ≤ log x`, so `log 2 ≤ log x/8 = log zR`
  have hlog256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlog2le : Real.log 2 ≤ Real.log zR := by
    rw [hlogzR]
    have h := Real.log_le_log (by norm_num) hx256R
    rw [hlog256] at h; linarith
  have h2zR : (2 : ℝ) ≤ zR := (Real.log_le_log_iff (by norm_num) hzRpos).mp hlog2le
  -- `zR ≤ yR` (base `≥ 1`, `1/8 ≤ 1/3`)
  have hzy : zR ≤ yR := by
    rw [hzR, hyR]; exact Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  -- floor brackets
  have hzlo : (opZ x : ℝ) ≤ zR := by rw [opZ, ← hzR]; exact Nat.floor_le hzRpos.le
  have hzhi : zR ≤ (opZ x : ℝ) + 1 := by rw [opZ, ← hzR]; exact (Nat.lt_floor_add_one zR).le
  have hylo : (opY x : ℝ) ≤ yR := by rw [opY, ← hyR]; exact Nat.floor_le hyRpos.le
  have hyhi : yR ≤ (opY x : ℝ) + 1 := by rw [opY, ← hyR]; exact (Nat.lt_floor_add_one yR).le
  exact ⟨hx1, h2zR, hzy, hlogzR, hlogyR, hzlo, hzhi, hylo, hyhi⟩

/-- **`hcount_op_AP3` — the three AP rows at op (FULLY CLOSED).**  `0 < opQ` (`opf_Q_pos`),
`Coprime opQ (opA+2)` (`opf_Qa2`, the `a = Q−1` residue witness), and `∀ p prime ∣ opQ → p < opZ x`
(`opf_Q_primeFactors`: `opQ`'s primes are `< opW'`, and `opW' ≤ opZ x` from `opf_tower`). -/
theorem hcount_op_AP3 : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    0 < opQ ∧ Nat.Coprime opQ (opA + 2)
      ∧ (∀ p : ℕ, p.Prime → p ∣ opQ → p < opZ x) := by
  obtain ⟨xt, _, htower⟩ := opf_tower
  refine ⟨xt, fun x hx => ?_⟩
  obtain ⟨_, _, hw'z, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := htower x hx
  refine ⟨opf_Q_pos, opf_Qa2, fun p hp hpd => ?_⟩
  have hmem : p ∈ opQ.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, opf_Q_pos.ne'⟩
  rw [opf_Q_primeFactors, Finset.mem_filter, Finset.mem_range] at hmem
  omega

/-! ## The ecount witness and the packaged slot -/

/-- The honest explicit `ecount` at op: `ecountOp C x = C / log (opZ x)` — the `O(1/log z)` form
the GLU-1 ledger anticipates (`GlueNormalized.lean`, the `hcount` cert note).  The leading
constant is `C = cbar·(11·K + 12·log 2)/4` with `K` the `psiTot_pnt` PNT-error constant (shared
by the keystone multiplicative slack `LF·WF−1` and the mass slack `2·Kmass·x/log x`); see the
module tail for the derivation and the deferred sub-bounds. -/
noncomputable def ecountOp (C : ℝ) (x : ℕ) : ℝ := C / Real.log (opZ x)

/-- **`hcount_at_op` — HCOUNT's SLOT at the operating point, with `ecount` explicit.**
For every `C ≥ 0`, there is a fixed mass constant `Kmass ≥ 0` (from `lambda_mass_lower`) and a
threshold past which the GlueNormalized `hcount` SLOT

  `log x · tripleSumW opQ opA x (opZ x)(opY x) ≤ (cbar + ecountOp C x)·((∑ Λ)/φ(opQ))`

holds **provided** the count line closes against the PNT lower window mass `massLo`:

  `log x · tripleSumW opQ opA x (opZ x)(opY x)
      ≤ (cbar + ecountOp C x)·(massLo x Kmass / φ(opQ))`,   `massLo x K := x/2 − 1 − 2·K·x/log x`.

The premise is the honest residual analytic obligation of HCOUNT (composing
`tripleSum_le_cbar_final_W` with the `CORR`/slack bound — the DEFERRED half); everything else —
the `/φ(opQ)` normalisation, the window-mass monotonicity `massLo ≤ ∑ Λ`, and the explicit
`ecount = C/log(opZ x)` — is discharged here.  Composes `hcount_massBridge`. -/
theorem hcount_at_op {C : ℝ} (hC : 0 ≤ C) :
    ∃ (Kmass : ℝ) (x₁ : ℕ), 0 ≤ Kmass ∧ ∀ x : ℕ, x₁ ≤ x →
      Real.log x * tripleSumW opQ opA x (opZ x) (opY x)
          ≤ (cbar + ecountOp C x)
              * (((x : ℝ) / 2 - 1 - 2 * Kmass * x / Real.log x) / (opQ.totient : ℝ)) →
      Real.log x * tripleSumW opQ opA x (opZ x) (opY x)
          ≤ (cbar + ecountOp C x)
              * ((∑ n ∈ twinWindow x, vonMangoldt n) / (opQ.totient : ℝ)) := by
  obtain ⟨Kmass, x₀, hK0, hbridge⟩ := hcount_massBridge
  refine ⟨Kmass, max x₀ 256, hK0, fun x hx hbound => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx256 : 256 ≤ x := le_trans (le_max_right _ _) hx
  -- `0 ≤ cbar + ecountOp C x`: `cbar > 0`, `C ≥ 0`, `log (opZ x) > 0` (since `opZ x ≥ 2`)
  have hce : 0 ≤ cbar + ecountOp C x := by
    have hzR : ((x : ℝ) ^ ((1 : ℝ) / 8)) = (x : ℝ) ^ ((1 : ℝ) / 8) := rfl
    obtain ⟨_, h2zR, _, _, _, hzlo, _, _, _⟩ :=
      hcount_op_geometry hx256 (zR := (x : ℝ) ^ ((1 : ℝ) / 8))
        (yR := (x : ℝ) ^ ((1 : ℝ) / 3)) rfl rfl
    have hopZ2 : (2 : ℝ) ≤ (opZ x : ℝ) := by
      rw [opZ]; exact_mod_cast Nat.le_floor (by exact_mod_cast h2zR)
    have hlogpos : 0 < Real.log (opZ x) := Real.log_pos (by linarith)
    have : 0 ≤ ecountOp C x := by rw [ecountOp]; positivity
    linarith [cbar_pos]
  exact hbridge x hx0 (ecountOp C x) hce hbound

/-- **The compiled slot example.**  The `hcount_at_op` SLOT output (with `ecount = ecountOp C x`)
plugs verbatim into `GlueNormalized.hmA3_normalized`'s `hcount` hypothesis at the op witnesses
(`Q = opQ`, `T = tripleSumW opQ opA x (opZ x)(opY x)`, `totalMass = (∑ Λ)/φ(opQ)`) — the smooth
AP scale of gate correction C3.  Mirrors `CountW.lean:749`, specialised to the operating point. -/
example (x : ℕ) {C : ℝ}
    {XW Wz Wy Fv slack3 R3 rho mainA3 : ℝ}
    (hXW : 0 < XW)
    (hXWdef : XW = (∑ n ∈ twinWindow x, vonMangoldt n) / (opQ.totient : ℝ) * Wz)
    (hrawA3 : mainA3
      ≤ Real.log x * (tripleSumW opQ opA x (opZ x) (opY x) * Wy * (Fv + slack3) + R3))
    (hcertA3 : Fv ≤ 243 / 100) (hFslack_nn : 0 ≤ Fv + slack3)
    (hWy : Wy ≤ Wz * rho) (hrho_nn : 0 ≤ rho) (hWz_nn : 0 ≤ Wz)
    (hLTnn : 0 ≤ Real.log x * tripleSumW opQ opA x (opZ x) (opY x))
    (hcountW : Real.log x * tripleSumW opQ opA x (opZ x) (opY x)
      ≤ (cbar + ecountOp C x) * ((∑ n ∈ twinWindow x, vonMangoldt n) / (opQ.totient : ℝ))) :
    mainA3 ≤ XW * (cbar * (3 / 8) * (243 / 100)
        + (((cbar + ecountOp C x) * rho * (243 / 100 + slack3) - cbar * (3 / 8) * (243 / 100))
            + Real.log x * R3 / XW)) :=
  hmA3_normalized hXW hXWdef hrawA3 hcertA3 hFslack_nn hWy hrho_nn hWz_nn hLTnn hcountW

/-! ## The DEFERRED half of HCOUNT — the exact remaining list (design-tier sub-nodes)

`hcount_at_op` closes the SLOT modulo the premise (★): `log x·T ≤ (cbar+ecountOp C x)·massLo/φ`.
Discharging (★) means composing `tripleSum_le_cbar_final_W` (A = 13, C = 2 — its `Ksw, N₀`
depend only on `A, C`) with the mass slack and the honest `ecountOp C x = C/log(opZ x)`.  Rows
already discharged here: the geometry rows (`hcount_op_geometry`), the three AP rows
(`hcount_op_AP3`), and the `/φ(opQ)` + `massLo ≤ ∑ Λ` bridge (`hcount_massBridge`).  What
remains, each a self-contained sub-node:

* **HCOUNT-Lval** — the `Lval` rows at op: `3 ≤ Lval x (opY x)`, `N₀ ≤ Lval x (opY x)`,
  `4 ≤ log (Lval x (opY x))`, and `(opQ:ℝ) ≤ (log (Lval x (opY x)))^2`.  Route:
  `Lval x (opY x) = x/(2·opY x·√x) ≈ x^{1/6}/2`, so `log Lval ≈ log x/6`; with `opQ ≤ log x`
  (`opf_tower` row 1) the `C = 2` range row is `log x ≤ (log x/6)^2`, i.e. `log x ≥ 36` — a
  tower-scale threshold.  Needs an `x^{1/6}/const ≤ Lval` nat-division/floor lower bound.
* **HCOUNT-CORR** — the `o(x/log x)` bound on the keystone's `CORR` sum.  Three missing
  analytic pieces (no landed infrastructure — `AbelPass2` has only `Ifun_nonneg`,
  `Ifun_integral_eq_cbar`):
    (i)   an `Ifun` UPPER bound `Ifun x yR t ≤ C_I/log x` on `[zN, yN]` (from the closed form
          `Ifun_cf`, `log(2−3β) ≤ log(13/8)`);
    (ii)  the boundary `hbjs` bound `hbjs x p₁ (√(x/p₁)) = 2/(log x + log p₁) ≤ 2/log x`;
    (iii) the `S1set` prime-reciprocal bound `Σ_{p₁∈S1set} 1/p₁ ≤ log(8/3) + O(1/log z)`
          (a windowed-Mertens sum; `sum_inv_prime_window_le`-shaped).
  Together these give `CORR ≤ C_CORR/(log x)^2`, hence `log x·(x/2)·CORR ≤ C_CORR·x/(2 log x)`.
* **HCOUNT-SLACK** — the multiplicative-slack collapse `LF·WF − 1 ≤ (3K + 4 log 2·6)/log Lval`
  (`LF = 1+3K/L₀`, `WF = 1+4log2/log(2 Lval)`, `L₀ = log Lval ≥ log x/7`), giving
  `(LF·WF−1)·(cbar/2)·x ≤ (9K + 12 log 2)·cbar·x/log x`, plus the `E_SW` polylog-beats-power
  `φ·log x·E_SW = O(x/(log x)^{11})` (`φ ≤ opQ ≤ log x`, `E_SW`'s `Σ1/(p₁p₂)` via
  `sum_inv_pairSet_le`, `|pairSet| ≤ y√x` via `pairSet_card_le`).

Summing HCOUNT-CORR + HCOUNT-SLACK + the mass slack `cbar·2·Kmass·x/log x` and matching to
`ecountOp C x · massLo ≈ (C/log(opZ x))·(x/2) = 4C·x/log x` fixes the honest leading constant

  `C = cbar·(11·K + 12·log 2)/4`

(`K` the shared `psiTot_pnt` constant), which is `≪ 0.01` at the tower `x₀` (`log(opZ x) ≥
opW'^opW'/8`), inside the razor's `M ≥ 1/100` margin — so HEB/`hEbundle_at_op` closes once these
three sub-nodes land. -/

end Salt.Chen
