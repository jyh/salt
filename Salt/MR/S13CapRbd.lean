/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RbdSupply
import Salt.MR.M4CapWire
import Salt.MR.CofactorSupplier
import Salt.MR.USetGradedPrice
import Salt.MR.S13FramesB

/-!
# ⟦CAPGATE / W-RBD⟧ — the co-factor block of `S13CapGatePerBlock` (`S13CapRbd`)

Design provenance: **CAPGATE-SCOPE** (flags, 2026-07-30), the supply campaign for
`S13FramesB.S13CapGatePerBlock` — the last unsupplied bundle on the living const road.
This file is wave **W-RBD**: the bundle's four co-factor fields, at the shared binder.

**PURELY ADDITIVE.**  No landed declaration is touched; `Salt/MR/All.lean` is NOT edited
(⟦MAESTRO RULING 10⟧ — the maestro adds the import at the seal).

## ⟦THE FOUR FIELDS⟧ (`S13FramesB.lean` line numbers)

| field | line | class | route |
|---|---|---|---|
| `Rbd_nonneg` | 1066 | WIRING | `0 ≤ R̄₀` (the register's own line) times `2^J` |
| `Rbd_grade` | 1068 | ⟦RULING 9⟧ carried | the register's `4·R̄₀ ≤ C_R·(log X)^{−ρ₂₉₃}` |
| `Cq_gate` | 1070 | ⟦RULING 9⟧ carried | the register's `1728·C_q·C_R² ≤ (log X)^{2θ₂₉₃}` |
| `Rbd_socket` | 1072 | SUPPLIED | `RbdSupply.m4_supplier_all_chi` at `J = 2`, `Ps = 1` |

⟦MAESTRO RULING 9⟧ `Rbd_grade` and `Cq_gate` are carried as SUPPLIER HYPOTHESES — they are
hypotheses at all six landed sites already (`M4DoorClose:265`/`:211`,
`M4DoorClosePool:198/528/857/1178`, `M4T0Discharge:700`), so the corpus posture is
unchanged.  They are stated here VERBATIM at the pin `C_R := gradeCR2 Cb`, which is the
spelling every one of those sites uses; the wide-arm grading page (which would DERIVE them)
is a separate later wave.

## ⟦THE PIN⟧ — how `m4_supplier_all_chi` is read at the S13 door

| supplier slot | S13 value |
|---|---|
| `X` | `((Nd : ℕ) : ℝ)` (the bundle's base) |
| `θ` | `theta293` (so `0 < θ`, `θ ≤ 1/32` are DISCHARGED here, not carried) |
| `H` | `H83 ((Nd : ℕ) : ℝ) theta293` |
| `N`, `Xd` | `2 * Nd`, `Nd` |
| `Pseq`, `Qseq` | `calP (Adoor M) (3072 * M)`, `calQK (Adoor M) (3072 * M) M` |
| `J`, `Ps` | `2`, `1` (so `1 ≤ Ps` is `le_rfl`, not carried) |
| `t₁` | FREE — the field quantifies it, the supplier's binder list never mentions it |
| `Rbar` | `2 ^ 2 * R̄₀`, i.e. the field's `Rbd` |

`M4CapWire.m4_capRbd_at_door` already consumes EXACTLY this spelling (it is what turns the
socket into `DoorCapBase`'s `Rbd_binder`), so the field and the wire agree byte for byte.

## ⟦THE REGISTER — nothing dropped⟧

`s13CapRbd_all` carries `m4_supplier_all_chi`'s hypothesis bundle in full: 31 wide-supply
gates (the 34 of the supplier minus the three the pin discharges: `1 ≤ Ps`, `0 < θ`,
`θ ≤ 1/32`), the two existential constants `X₀` (the wide-supply scale) and `K` (the `_vt`
floor's threshold constant — ⟦NOT `DoorArithFrameRho`'s `K`⟧, and never identified with it),
the mask debit `D`, and three register lines quoted verbatim from `M4DoorClose:264/265/211`.
The gate block is `M4DoorClose.lean:233–266`'s, at the S13 pin above.

⟦THE `0 ≤ R̄₀` LINE⟧ is carried rather than derived because `ramI H P Q` may be EMPTY, in
which case the endpoint gate says nothing.  §1 below is the wire that discharges it at any
site whose block set is inhabited (`CofactorSupplier.cofactorRbdGen_nonneg`); the register
line is `M4DoorClose:264` verbatim, so no landed site pays anything new.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — ⟦THE `R̄₀` NON-NEGATIVITY WIRE⟧

`CofactorSupplier.cofactorRbdGen_nonneg` says the fused general-datum `R̄` is `≥ 0` off
`0 ≤ S` alone.  The supply register's endpoint line dominates that quantity by `R̄₀` at every
block, so `0 ≤ R̄₀` is free as soon as ONE block exists. -/

/-- **⟦`0 ≤ R̄₀` FROM THE ENDPOINT GATE⟧** (`s13_rbar0_nonneg_of_ramI`).  At an inhabited
block set, the register's `0 ≤ R̄₀` line (`M4DoorClose:264`) is redundant: it follows from
`0 ≤ S` and the endpoint gate (`M4DoorClose:261–263`). -/
theorem s13_rbar0_nonneg_of_ramI {H : ℝ} {P Q : ℕ} {Mt kk : ℕ → ℕ} {Rrad S Rbar0 : ℝ}
    (hS0 : 0 ≤ S) (hne : (ramI H P Q).Nonempty)
    (hRbdU : ∀ j ∈ ramI H P Q,
      cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
        (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar0) :
    0 ≤ Rbar0 := by
  obtain ⟨j, hj⟩ := hne
  exact le_trans (cofactorRbdGen_nonneg hS0) (hRbdU j hj)

/-! ## §2 — ⟦THE FOUR FIELDS AT THE SHARED BINDER⟧ -/

/-- **⟦W-RBD — `S13CapGatePerBlock`'s CO-FACTOR BLOCK⟧** (`s13CapRbd_all`).  The bundle's
four co-factor fields — `Rbd_nonneg` (1066), `Rbd_grade` (1068), `Cq_gate` (1070) and
`Rbd_socket` (1072) — delivered together at the shared binder, at the pins

  `Rbd = 2 ^ 2 * Rbar0` (⟦`J = 2`⟧) and `CR = gradeCR2 Cb`.

The hypothesis register is `RbdSupply.m4_supplier_all_chi`'s, verbatim, at the S13 pin
(module header), together with the three lines `M4DoorClose:264`, `:265` and `:211` that
⟦RULING 9⟧ keeps as supplier hypotheses.  The existentials `X₀` and `K` are the supplier's
own — a wide-supply scale and the `_vt` floor's threshold constant. -/
theorem s13CapRbd_all (Qm : ℕ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (q : ℕ) [NeZero q] (M Nd P Q : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
        (cq L cg Cb Cq Rrad Tann Rbar0 c S D CR Rbd : ℝ),
        -- ⟦THE TWO PINS⟧
        CR = gradeCR2 Cb →
        Rbd = 2 ^ 2 * Rbar0 →
        -- ⟦THE WIDE-SUPPLY GATES⟧ (`m4_supplier_all_chi`, at the S13 pin)
        q ≤ Qm →
        Real.exp (Real.exp 1) ≤ ((Nd : ℕ) : ℝ) →
        0 ≤ D →
        (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (Adoor M) (3072 * M) i)
              (calQK (Adoor M) (3072 * M) M i) ((Nd : ℕ) : ℝ), (1 : ℝ) / (p : ℝ)) ≤ D) →
        40 * Real.log (Real.log (Real.log ((Nd : ℕ) : ℝ)))
            + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
                + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q
                + K + 25 + D)
          < Real.log (Real.log ((Nd : ℕ) : ℝ)) →
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        1 ≤ P → 0 < Rrad →
        P83 ((Nd : ℕ) : ℝ) theta293 ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ) → P ≤ Q →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
          TLBlockGates34 cq (H83 ((Nd : ℕ) : ℝ) theta293) P (2 * Nd) Nd Mt kk Tann L cg Cb
            ((Nd : ℕ) : ℝ) theta293 Rrad j) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * ((Nd : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, 1 ≤ Dd j) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, Dd j ≤ kk j) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, X₀ ≤ Real.sqrt (Xa j)) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
          Real.sqrt (Xa j) ≤ ((kk j / Dd j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
          pin2Gate ≤ ((kk j / Dd j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, Real.exp 1 ≤ Xa j) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ 2 * Xa j) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, 2 * Xa j ≤ ((Nd : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
          0 ≤ cofactorMfl ((Nd : ℕ) : ℝ) theta293 ((kk j / Dd j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, ∀ t : ℝ, |t| ≤ Tann → ∀ i : ℕ,
          ((kk j / Dd j : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa j →
            |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * ((Nd : ℕ) : ℝ)) →
        0 ≤ S →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
          cSq * caseASwide c Cb
              (cofactorMfl ((Nd : ℕ) : ℝ) theta293 ((kk j / Dd j : ℕ) : ℝ))
              ((kk j / Dd j : ℕ) : ℝ) (Xa j)
            + cSq * ((Dd j : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ S) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
          2 / ramRbot (H83 ((Nd : ℕ) : ℝ) theta293) Nd j
            ≤ cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
                (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad / 3) →
        (∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
          cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
              (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar0) →
        -- ⟦RULING 9 — the three carried register lines (`M4DoorClose:264`, `:265`, `:211`)⟧
        0 ≤ Rbar0 →
        4 * Rbar0 ≤ gradeCR2 Cb * (Real.log ((Nd : ℕ) : ℝ)) ^ (-rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (2 * theta293) →
        -- ⟦THE FOUR FIELDS⟧
        (0 ≤ Rbd)
          ∧ (Rbd ≤ CR * (Real.log ((Nd : ℕ) : ℝ)) ^ (-rho293))
          ∧ (1728 * Cq * CR ^ 2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (2 * theta293))
          ∧ (∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
              CofactorSocket (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd P Q Tann Rrad t₁ Rbd
                (doorCofactor0 χ (calP (Adoor M) (3072 * M))
                  (calQK (Adoor M) (3072 * M) M) 2 1)) := by
  obtain ⟨X₀, hX₀0, K, hK0, hsup⟩ := m4_supplier_all_chi Qm
  refine ⟨X₀, hX₀0, K, hK0, ?_⟩
  intro q _ M Nd P Q Mt kk Dd Xa cq L cg Cb Cq Rrad Tann Rbar0 c S D CR Rbd
    hCR hRbd hq hXee hD0 hdebit hthr hc0 hce hc1 hCb0 hCbound hP1 hR0 hPlow hQhigh hPQ
    hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0 hboxw hS0 hSbd hendGen hRbdU
    hRbar0 hgrade hCqgate
  subst hCR
  subst hRbd
  have hfour : (2 : ℝ) ^ 2 * Rbar0 = 4 * Rbar0 := by norm_num
  refine ⟨by rw [hfour]; linarith, by rw [hfour]; exact hgrade, hCqgate, ?_⟩
  intro t₁ χ
  exact hsup q (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M)
    (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd P Q 2 1 Mt kk Dd Xa cq L cg Cb
    ((Nd : ℕ) : ℝ) theta293 Rrad Tann t₁ Rbar0 c S D
    hq hXee hD0 hdebit hthr hc0 hce hc1 hCb0 hCbound hP1 le_rfl hR0 theta293_pos
    theta293_lt_one_div_32.le hPlow hQhigh hPQ hblk hbox hD1 hDk hX₀j hsqXa hpin hXae
    hMXa hXaX hMfl0 hboxw hS0 hSbd hendGen hRbdU χ

end Salt.MR

end

