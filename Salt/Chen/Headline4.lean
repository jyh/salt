/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.TheHeadline
import Salt.Chen.PackA
import Salt.Chen.PackB
import Salt.Chen.CountAtOp3
import Salt.Chen.A2Window
import Salt.Chen.AssembleA3b
import Salt.Chen.AggSum
import Salt.Chen.AggCE
import Salt.Chen.AggDiag
import Salt.Chen.H4Cond
import Salt.Chen.GlueNormalized
import Salt.Chen.RazorClose
import Salt.Chen.GlueFinal

/-!
# fin8d — THE HEADLINE WIRING

This module composes the landed Chen suppliers into

  `chen_headline : {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite`.

The composition is organised as three floors over the frozen operating point
(`opZ`/`opY`/`opP`/`opPs`/`opQ`/`opA`/`opW'`, `Salt/Chen/HeadlineW2.lean`):

* **F3 backbone** (`chen_headline_of_ops`): reduces `chen_headline` to four
  operating-point analytic bundles `m1`/`m2`/`m3` (the A₁ lower / A₂ upper / A₃
  upper carriers) and the ledger positivity, discharging all eight *structural*
  conjuncts of `chen_of_hypotheses_W` from the `opf_*` facts.  This is pure
  wiring and is proved unconditionally here.

* **F2 ledger** (`normalized_package`, `Salt/Chen/GlueNormalized.lean`): the
  ledger positivity from the raw carrier bounds + the value/reconciliation certs
  + the error bundle `hEbundle ≤ 1/200`.

* **F1 A₃** (the a12_hA3 bundle): `hBVblocksW_discharge'` at the op witnesses →
  `mainA3_of_block_remainders_W` (via the `PDiag`:782 template).

The A₁/A₂ bundles are the *landed* `a12_hA1`/`a12_hA2` (`HeadlineW2.lean`); only
their at-op hypotheses need discharging.

## Obligation table (supplier → floor → status)

| Slot            | Supplier                                    | Floor | Status |
|-----------------|---------------------------------------------|-------|--------|
| structural ×8   | `opf_*`, `hyx_at_op`                         | F3    | DONE   |
| `hA1` (m1)      | `a12_hA1` (landed)                           | F2    | at-op hyps |
| `hA2` (m2)      | `a12_hA2` (landed)                           | F2    | at-op hyps |
| `hA3` (m3)      | `mainA3_of_block_remainders_W` ∘ discharge'  | F1    | compose |
| `hcertA1`       | `fchain_A1_final` ∘ `logRatio_A1_mem`       | F2    | cert   |
| `hcertA2`       | `A2grid_window_le` ∘ `logRatio_A2_window_mem`| F2    | cert   |
| `hcertA3`       | `Fchain_switch_le` ∘ `logRatio_A3_mem`      | F2    | cert   |
| `hWy`           | `hWy_at_op`                                 | F2    | DONE (PackB) |
| `hcount`        | `hcount_slot_closed` + equidist bridge      | F2    | GAP (equidist) |
| `hXW`           | `XW_pos_at_op`                              | F2    | DONE (PackB) |
| `hEbundle`      | 8 shares via `W_twinA1_ge`                  | F2    | numeric |

No `sorry`, no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Real

/-! ## F3 — the backbone: reduce `chen_headline` to the four op-level analytic bundles

`chen_of_hypotheses_W` (`Salt/Chen/Assembly.lean`) consumes, for every threshold `X`, an
operating point `x` with the residue data + 12 conjuncts.  We instantiate the witnesses at
the frozen operating point (`z = opZ x`, `P = opP x`, `y = opY x`, `Q = opQ`, `a = opA`,
`w' = opW'`) and the analytic carriers at three free functions `m1`/`m2`/`m3 : ℕ → ℝ`.  The
eight *structural* conjuncts are discharged from `opf_*` + `hyx_at_op`; the four analytic
conjuncts become the hypotheses `hA1`/`hA2`/`hA3`/`hL`. -/

/-- **F3 backbone.**  If, past a threshold, the three carriers are pinned by `m1`/`m2`/`m3`
(A₁ lower, A₂ upper, A₃ upper at the W-carriers) and the ledger `m1 − m2/2 − m3/2 −
log x·x/(z−1)/2` is positive, then there are infinitely many primes `p` with `p + 2` a P₂.

The A₁/A₂ bundles are the landed `a12_hA1`/`a12_hA2`; `hA3` is the F1 supplier; `hL` is the
F2 ledger.  This lemma performs the entire structural wiring of `chen_of_hypotheses_W`. -/
theorem chen_headline_of_ops (m1 m2 m3 : ℕ → ℝ)
    (hA1 : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x → m1 x ≤ A1primeSumW opQ opA x (opP x))
    (hA2 : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
        omegaPrimeSumW opQ opA x (opP x) (opY x) ≤ m2 x)
    (hA3 : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
        triplePrimeSumW opQ opA x (opP x) (opY x) ≤ m3 x)
    (hL : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
        0 < m1 x - m2 x / 2 - m3 x / 2
          - Real.log x * (x : ℝ) / ((opZ x : ℝ) - 1) / 2) :
    {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite := by
  obtain ⟨xa1, hxa1⟩ := hA1
  obtain ⟨xa2, hxa2⟩ := hA2
  obtain ⟨xa3, hxa3⟩ := hA3
  obtain ⟨xl, hxl⟩ := hL
  obtain ⟨xt, hxt8, htower⟩ := opf_tower
  apply chen_of_hypotheses_W
  intro X
  -- the operating threshold: past all bundle thresholds, the tower, and `≥ 2X`
  obtain ⟨x, hx1, hx2, hx3, hx4, hx5, hx6⟩ :
      ∃ x, xa1 ≤ x ∧ xa2 ≤ x ∧ xa3 ≤ x ∧ xl ≤ x ∧ xt ≤ x ∧ 2 * X ≤ x :=
    ⟨max (max (max xa1 xa2) (max xa3 xl)) (max xt (2 * X)), by
      have := Nat.le_max_left (max (max xa1 xa2) (max xa3 xl)) (max xt (2 * X))
      have := Nat.le_max_right (max (max xa1 xa2) (max xa3 xl)) (max xt (2 * X))
      have := Nat.le_max_left (max xa1 xa2) (max xa3 xl)
      have := Nat.le_max_right (max xa1 xa2) (max xa3 xl)
      have := Nat.le_max_left xa1 xa2
      have := Nat.le_max_right xa1 xa2
      have := Nat.le_max_left xa3 xl
      have := Nat.le_max_right xa3 xl
      have := Nat.le_max_left xt (2 * X)
      have := Nat.le_max_right xt (2 * X)
      omega⟩
  have hxge2 : 2 ≤ x := by omega
  have ht := htower x hx5
  have hz3 : 3 ≤ opZ x := ht.2.2.2.1
  refine ⟨x, opZ x, opP x, opY x, opQ, opA, opW', m1 x, m2 x, m3 x,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- X ≤ x / 2
    omega
  · -- 2 ≤ x
    exact hxge2
  · -- 2 ≤ opZ x
    omega
  · -- 3 ≤ opW'
    exact opf_w'3
  · -- x < (opY x + 1) ^ 3
    exact hyx_at_op x (by omega)
  · -- ∀ q, q.Prime → q < opW' → q ∣ opQ
    exact opf_Qfull
  · -- ∀ q, q.Prime → opW' ≤ q → q < opZ x → q ∣ opP x
    exact opf_Pfull' x
  · -- Nat.Coprime opQ (opA + 2)
    exact opf_Qa2
  · -- m1 x ≤ A1primeSumW opQ opA x (opP x)
    exact hxa1 x hx1
  · -- omegaPrimeSumW opQ opA x (opP x) (opY x) ≤ m2 x
    exact hxa2 x hx2
  · -- triplePrimeSumW opQ opA x (opP x) (opY x) ≤ m3 x
    exact hxa3 x hx3
  · -- the ledger
    exact hxl x hx4

/-! ## F2/A₁ — the A₁ carrier `M1` and its bundle (from the landed `a12_hA1`)

`M1 x` is the `a12_hA1` lower-bound expression at the canonical proofs `opf_P_sq x`/`opf_Podd x`;
it doubles as `normalized_package`'s A₁ raw form (`XW·(fchain − slack1) − R1`, ring-equal). -/

/-- The A₁ carrier: the landed `a12_hA1` lower bound, at the op proofs. -/
noncomputable def M1 (x : ℕ) : ℝ :=
  (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass *
      (Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)) *
        (fchain (maxDepth (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
            (logRatio (opZ x) (opD x))
          - opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opZ x) (opD x))))
    - (x : ℝ) / (Real.log x) ^ 10
    - Real.sqrt x * (Nat.log 2 x : ℝ) * Real.log x

/-- **The A₁ bundle** — `M1 x ≤ A1primeSumW` past a threshold.  The landed `a12_hA1` with its
~13 at-op hypotheses discharged from `opf_*` + `opf_tower`. -/
theorem hA1_bundle : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x → M1 x ≤ A1primeSumW opQ opA x (opP x) := by
  obtain ⟨x1, h⟩ := a12_hA1
  obtain ⟨xt, hxt8, htower⟩ := opf_tower
  refine ⟨max x1 xt, fun x hx => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxt : xt ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hQlog, hwz, _, hz3, hzD, hD1, _, _, _, hStop, _⟩ := htower x hxt
  exact h x hx1 (opf_P_sq x) (opf_Podd x) (opf_Pz x) (opf_Plow x) (opf_QP x) opf_Qma
    hz3 hzD hD1 hStop hwz opf_Q2 hQlog

/-! ## F2/A₂ — the A₂ carrier `M2` and its bundle (from the landed `a12_hA2`) -/

/-- The A₂ carrier: the landed `a12_hA2` upper bound, at the op proofs. -/
noncomputable def M2 (x : ℕ) : ℝ :=
  ((twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
        * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
      * (A2grid ((Finset.Icc (opZ x) (opY x)).filter Nat.Prime) (opZ x) (opD x)
            (fun p => maxDepth (twinA2SieveW opQ opA x (opP x) p (opf_P_sq x) (opf_Podd x)))
          + ∑ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime,
              (1 / ((p : ℝ) - 1))
                * (opEps * CsharpB opEps * Real.exp 2
                    * hBJS (logRatio (opZ x) (cdiv (opD x) p))))
    + (x : ℝ) / (Real.log x) ^ 10

/-- **The A₂ bundle** — `omegaPrimeSumW ≤ M2 x` past a threshold.  The landed `a12_hA2` with its
~17 at-op hypotheses discharged; `hyD : opY x ≤ opD x` from the exponent monotonicity. -/
theorem hA2_bundle : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    omegaPrimeSumW opQ opA x (opP x) (opY x) ≤ M2 x := by
  obtain ⟨x1, h⟩ := a12_hA2
  obtain ⟨xt, hxt8, htower⟩ := opf_tower
  refine ⟨max x1 xt, fun x hx => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxt : xt ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hQlog, hwz, hw'z, hz3, hzD, hD1, _, _, _, _, _⟩ := htower x hxt
  have hxge8 : 8 ≤ x := le_trans hxt8 hxt
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hyD : opY x ≤ opD x := by
    rw [opY, opD]
    exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num))
  exact h x hx1 (opf_P_sq x) (opf_Podd x) (opf_Pz x) (opf_Plow x) (opf_QP x) opf_Qma
    opf_Qfull (opf_Pfull' x) opf_Qa2 (opf_QmPr x hw'z) hz3 hD1 hwz opf_Q2 hQlog hyD

/-! ## F1 — the A₃ carrier `M3` (the `mainA3_of_block_remainders_W` output shape)

`M3 x` is the exact conclusion of `mainA3_of_block_remainders_W` (equivalently the `PDiag`:782
template) at the op witnesses `z = opZ x`, `y = opY x`, `Ps = opPs x`, `Dlev = opDlev x`,
`ε = opEps`.  Producing the bundle `triplePrimeSumW ≤ M3 x` is F1 (the `hBVblocksW_discharge'`
composition); it is left as an explicit hypothesis of `chen_headline_of_A3_ledger`. -/

/-- The A₃ carrier: the `mainA3_of_block_remainders_W` output at the op witnesses. -/
noncomputable def M3 (x : ℕ) : ℝ :=
  Real.log x *
      (tripleSum x (opZ x) (opY x) / (opQ.totient : ℝ)
          * Salt.BrunLower.W (switchSieve x (opZ x) (opY x) (opPs x) (opf_Ps_sq x) (opf_Psodd x))
          * (Fchain (maxDepth (switchSieve x (opZ x) (opY x) (opPs x) (opf_Ps_sq x)
                (opf_Psodd x))) (logRatio (opY x) (opDlev x))
            + opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opY x) (opDlev x)))
        + (x : ℝ) / (Real.log x) ^ 10)

/-! ## The final reduction

`chen_headline` reduces — via the F3 backbone and the landed A₁/A₂ bundles — to exactly two
operating-point obligations:

* **F1** (`hA3`): `triplePrimeSumW opQ opA x (opP x) (opY x) ≤ M3 x` past a threshold, and
* **F2 ledger** (`hL`): `0 < M1 x − M2 x/2 − M3 x/2 − log x·x/(opZ x − 1)/2` past a threshold.

Both are stated at the concrete carriers `M1`/`M2`/`M3`, so the next session supplies exactly
these two bundles (F1 via `hBVblocksW_discharge'`; F2 via `normalized_package` + the certs +
`hEbundle ≤ 1/200`) to obtain `chen_headline`. -/

/-- **The final wiring reduction.**  With the F1 A₃ bundle and the F2 ledger bundle at the
concrete carriers `M1`/`M2`/`M3`, the Chen headline follows.  The A₁/A₂ legs (`hA1_bundle`/
`hA2_bundle`) and the entire structural wiring (`chen_headline_of_ops`) are discharged. -/
theorem chen_headline_of_A3_ledger
    (hA3 : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
        triplePrimeSumW opQ opA x (opP x) (opY x) ≤ M3 x)
    (hL : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
        0 < M1 x - M2 x / 2 - M3 x / 2
          - Real.log x * (x : ℝ) / ((opZ x : ℝ) - 1) / 2) :
    {p : ℕ | p.Prime ∧ IsP2 2 (p + 2)}.Infinite :=
  chen_headline_of_ops M1 M2 M3 hA1_bundle hA2_bundle hA3 hL

/-! ## F2 raw-shape verification (de-risking `normalized_package`)

The F2 ledger (`hL`) is `normalized_package` (`Salt/Chen/GlueNormalized.lean`) at
`XW = totalMass·Wz`, `mainA1 = M1 x`, `mainA2 = M2 x`, `mainA3 = M3 x`.  Its three *raw*
hypotheses (`hrawA1`/`hrawA2`/`hrawA3`) hold by `ring` once the carriers are the ledger-normalised
forms.  These lemmas certify exactly that regrouping, so the next session's `hrawᵢ` discharge is
`le_of_eq (by rw [...]; ring)`.

`M3` is already in the raw form `log x·(T·Wy·(Fv + slack3) + R3)` (rfl), so only `M1`/`M2` — whose
`totalMass·(W··)` vs `(totalMass·W)·(·)` regrouping and combined strip `R1` are nontrivial — are
recorded. -/

/-- `M1` is `XW·(fA1 − slack1) − R1` with `XW = totalMass·W`, `R1 = x/(log x)^10 +
√x·(Nat.log 2 x)·log x` — the `hrawA1` shape `normalized_package` consumes. -/
theorem M1_raw_shape (x : ℕ) :
    (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
        * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x))
        * (fchain (maxDepth (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
              (logRatio (opZ x) (opD x))
            - opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opZ x) (opD x)))
      - ((x : ℝ) / (Real.log x) ^ 10 + Real.sqrt x * (Nat.log 2 x : ℝ) * Real.log x)
      = M1 x := by
  unfold M1; ring

/-- `M2` is `XW·(A2grid + aggSlack) + R2` with `XW = totalMass·W`, `R2 = x/(log x)^10` — the
`hrawA2` shape `normalized_package` consumes. -/
theorem M2_raw_shape (x : ℕ) :
    (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
        * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x))
        * (A2grid ((Finset.Icc (opZ x) (opY x)).filter Nat.Prime) (opZ x) (opD x)
              (fun p => maxDepth (twinA2SieveW opQ opA x (opP x) p (opf_P_sq x) (opf_Podd x)))
            + ∑ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime,
                (1 / ((p : ℝ) - 1))
                  * (opEps * CsharpB opEps * Real.exp 2
                      * hBJS (logRatio (opZ x) (cdiv (opD x) p))))
      + (x : ℝ) / (Real.log x) ^ 10
      = M2 x := by
  unfold M2; ring

end Salt.Chen
