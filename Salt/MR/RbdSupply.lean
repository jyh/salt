/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CaseAWide
import Salt.MR.VkMidSharp
import Salt.MR.HybridMoments
import Salt.MR.BigXiArc

/-!
# `RbdSupply` — WIRING THE LANDED CO-FACTOR SUPPLY INTO THE `Rbd` BINDER

⟦COUNCIL C3, 2026-07-30⟧ the Rbd supply wiring.  `PortClose.usetChi_window_meansq_gated`
carries, among its well-formedness binders, the co-factor ceiling

  `Rbd : ∀ j ∈ ramI H P Q, ∀ r : X̂(q) × ℝ, r.2 ∈ A → ‖R_{j,H}(χ̄·b; r.2)‖ ≤ R̄`,

one inequality per block and per pair `r = (χ, t)`.  The SUPPLY side is landed:
`CaseAWide.m4_supplier_complete` delivers `CofactorSocket … (2^J·R̄₀) (doorCofactor0 χ …)`
whose ONLY character-dependent hypothesis is the per-piece cap-free floor
`CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X`, and THAT floor has the landed supplier
`VkMidSharp.capFreeFloor3_pieceDatum_vt`.  Nothing between the two is missing; what is
missing is the WIRE.  This file is the wire, in five pieces.

## The five items

* **§1 the datum adapter** (`doorCofactor0_at_one_chiBar`).  At the shift `Ps = 1` the
  door's un-phased co-factor slot IS a `χ̄`-twist of a character-free datum:
  `doorCofactor0 χ Pseq Qseq J 1 = chiBarCoeff q χ (memSCoeff Pseq Qseq J liouvilleC)`.
  `CofactorSupplier.doorCofactor0_at_one` puts the datum in `memSCoeff` form and
  `M4Sieve.memSCoeff_mul` slides the twist out of the sieve indicator; the rest is
  commutativity.  This is what lets ONE socket serve the consumer's `chiBarCoeff q r.1 b`.
* **§2 the socket-to-binder bridge** (`rbd_binder_of_socket_chi` and its two
  specialisations).  `CofactorSocket` is stated on the ANNULUS
  `|t| ≤ T_ann ∧ R_rad ≤ |t − t₁|`; the consumer's binder is stated on an arbitrary
  measurable `A ⊆ [−T, T]`.  The height side is `T ≤ T_ann`; the RADIAL side is discharged
  by the socket's FREE `t₁` — `m4_supplier_complete` universally quantifies `t₁` and no
  hypothesis constrains it, so the consumer picks `t₁ := R_rad + T`, which puts the whole
  window outside the punctured disc.
* **§3 the `∀χ` socket** (`m4_supplier_all_chi`).  `m4_supplier_complete`'s hypothesis
  bundle carried VERBATIM (only `exp 1 ≤ log X` is traded for the floor's own
  `exp (exp 1) ≤ X`, which implies it), with the one character-dependent hypothesis
  discharged from `capFreeFloor3_pieceDatum_vt`: the wrapper's binder list is
  character-FREE, so its conclusion is `∀ χ, CofactorSocket …`.
* **§4 the Meissel–Mertens upper numeral** (`mertensM_le_two_thirds`, `mertensM_le_three`).
  The sibling of `SmallStones.mertensM_ge_neg_seventeen`, on the other side.  NOT by the
  same route: Mertens-2 at `t = 2` gives only `M ≤ 19`.  The corpus's own identification
  `Mertens.mertensM_eq_sub` (`M = γ − B`) with `mertensB_nonneg` and mathlib's
  `eulerMascheroniConstant_lt_two_thirds` gives `M ≤ 2/3` outright.
* **§5 the threshold arithmetic page** (`pieceFloor_vt_threshold_of_loglog` and the exit
  `capFreeFloor3_pieceDatum_arcDen`).  `capFreeFloor3_pieceDatum_vt`'s threshold is
  `40·ℓ₃ + 32·((1/8)log q + (1/4)mertensCap q + vkDebitConst(…) + vkMidDebitSharp q
  + K + 25 + D) < ℓ₂`.  At the arc's modulus range `q ≤ arcDen 12 H = (log H)^12` each
  summand gets its own named bound, all in `loglog H`:

  | summand | bound | lemma |
  |---|---|---|
  | `log q` | `12·loglog H` | `log_le_of_le_arcDen` |
  | `mertensCap q` | `log(12·loglog H) + 21` | `mertensCap_le_of_le_arcDen` |
  | `vkDebitConst (vkEulerCorr q · vkTwistConst q)` | `10 + 9·loglog H` | `vkDebitConst_le_of_le_arcDen` |
  | `vkMidDebitSharp q` | `29 + (1/4)log(7 + 12·loglog H)` | `vkMidDebitSharp_le_of_le_arcDen` |
  | the mask debit `D` | carried | (the consumer's own) |

  The assembly is therefore a `loglog X` LOWER bound whose right-hand side reads
  `loglog H` — ⟦THE LOG SCALES, KEPT APART⟧ `log X` (the floor's scale) and `log H` (the
  arc's) never substitute for one another here, and the assembled condition
  `40·ℓ₃(X) + 350·loglog H + 20·log(7 + 12·loglog H) + 2300 + 32K + 32D < loglog X` is the
  honest price: the arc's `(log H)^12` costs `Θ(loglog H)` against `loglog X`, so a
  consumer at `H = X^θ` does NOT clear it and one at `H = exp((log X)^ε)` does.  The
  constant `K` (the `_vt` floor's own anonymous constant, of which `cffKVt` is the named
  sibling at the un-margined floor) is carried SYMBOLICALLY throughout — no effective
  bound is attempted.

Everything here is ADDITIVE: no landed declaration is touched.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — THE DATUM ADAPTER: the door's shift-`1` slot IS a `χ̄`-twist -/

/-- **THE DATUM ADAPTER** (`doorCofactor0_at_one_chiBar`).  At the shift `Ps = 1`,

  `doorCofactor0 χ Pseq Qseq J 1 = chiBarCoeff q χ (memSCoeff Pseq Qseq J liouvilleC)`,

i.e. the door's un-phased co-factor slot is the consumer's `χ̄·b` at the CHARACTER-FREE
datum `b = 1_𝒮·λ` (the `memSCoeff`-masked Liouville function).

Route: `CofactorSupplier.doorCofactor0_at_one` (the shift at `1` is the plain sieve) puts
the slot in the form `memSCoeff Pseq Qseq J (liouChi χ)`; `M4Sieve.memSCoeff_mul` slides
the `χ̄` factor out through the sieve indicator (`1_𝒮·(a·w) = (1_𝒮·a)·w`); one
commutativity puts the twist on the left, where `chiBarCoeff` keeps it.

This is the identification the whole wire turns on: the socket is supplied at
`doorCofactor0`, the consumer's `Rbd` binder is stated at `chiBarCoeff q r.1 b`, and the
two are the SAME function of `m`. -/
theorem doorCofactor0_at_one_chiBar {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J : ℕ) :
    doorCofactor0 χ Pseq Qseq J 1
      = chiBarCoeff q χ (memSCoeff Pseq Qseq J liouvilleC) := by
  rw [doorCofactor0_at_one]
  funext m
  have hsplit : memSCoeff Pseq Qseq J (liouChi χ) m
      = memSCoeff Pseq Qseq J liouvilleC m * (starRingEnd ℂ) (χ (m : ZMod q)) :=
    memSCoeff_mul Pseq Qseq J liouvilleC
      (fun n => (starRingEnd ℂ) (χ (n : ZMod q))) m
  rw [hsplit, chiBarCoeff_apply, mul_comm]

/-! ## §2 — THE SOCKET-TO-BINDER BRIDGE -/

/-- **THE BRIDGE** (`rbd_binder_of_socket_chi`).  A per-character `CofactorSocket` at the
twisted datum `χ̄·b` gives the consumer's `Rbd` binder over ANY set `A ⊆ [−T, T]`:

* the HEIGHT side condition `|t| ≤ T_ann` is `T ≤ T_ann`;
* the RADIAL side condition `R_rad ≤ |t − t₁|` is `R_rad + T ≤ |t₁|` — the punctured
  disc of radius `R_rad` around `t₁` misses `[−T, T]` entirely.

No measurability is used: the binder is pointwise. -/
theorem rbd_binder_of_socket_chi {q : ℕ} {H : ℝ} {N Xd P Q : ℕ} {Tann Rrad t₁ T Rbd : ℝ}
    {b : ℕ → ℂ} {A : Set ℝ} (hA : A ⊆ Set.Icc (-T) T) (hT : T ≤ Tann)
    (hfar : Rrad + T ≤ |t₁|)
    (hs : ∀ χ : DirichletCharacter ℂ q,
      CofactorSocket H N Xd P Q Tann Rrad t₁ Rbd (chiBarCoeff q χ b)) :
    ∀ j ∈ ramI H P Q, ∀ r : DirichletCharacter ℂ q × ℝ, r.2 ∈ A →
      ‖ramR H N Xd P Q j (chiBarCoeff q r.1 b) r.2‖ ≤ Rbd := by
  intro j hj r hr
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp (hA hr)
  have habs : |r.2| ≤ T := abs_le.mpr ⟨hlo, hhi⟩
  refine hs r.1 j hj r.2 (le_trans habs hT) ?_
  have h1 := abs_sub_abs_le_abs_sub t₁ r.2
  rw [abs_sub_comm] at h1
  linarith

/-- **THE BRIDGE AT THE FREE `t₁`** (`rbd_binder_of_socket_chi_free`).  `t₁` is
unconstrained in `m4_supplier_complete` (it is one of the universally quantified reals, and
no hypothesis mentions it), so the radial side condition costs nothing: take
`t₁ := R_rad + T`, for which `R_rad + T ≤ |t₁|` is `le_abs_self` — no sign condition on
either `R_rad` or `T` is needed. -/
theorem rbd_binder_of_socket_chi_free {q : ℕ} {H : ℝ} {N Xd P Q : ℕ} {Tann Rrad T Rbd : ℝ}
    {b : ℕ → ℂ} {A : Set ℝ} (hA : A ⊆ Set.Icc (-T) T)
    (hT : T ≤ Tann)
    (hs : ∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
      CofactorSocket H N Xd P Q Tann Rrad t₁ Rbd (chiBarCoeff q χ b)) :
    ∀ j ∈ ramI H P Q, ∀ r : DirichletCharacter ℂ q × ℝ, r.2 ∈ A →
      ‖ramR H N Xd P Q j (chiBarCoeff q r.1 b) r.2‖ ≤ Rbd :=
  rbd_binder_of_socket_chi hA hT (le_abs_self (Rrad + T)) (hs (Rrad + T))

/-- **THE WIRE** (`rbd_binder_of_doorSocket_free`).  §1 and §2 composed: the `∀χ` door
socket at the shift `Ps = 1`, with `t₁` free, IS the consumer's `Rbd` binder at the
character-free datum `1_𝒮·λ`.  This is the shape `PortClose.usetChi_window_meansq_gated`
reads (its `b` slot instantiated at `memSCoeff Pseq Qseq J liouvilleC`). -/
theorem rbd_binder_of_doorSocket_free {q : ℕ} {H : ℝ} {N Xd P Q J : ℕ}
    {Tann Rrad T Rbd : ℝ} {Pseq Qseq : ℕ → ℕ} {A : Set ℝ}
    (hA : A ⊆ Set.Icc (-T) T) (hT : T ≤ Tann)
    (hs : ∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
      CofactorSocket H N Xd P Q Tann Rrad t₁ Rbd (doorCofactor0 χ Pseq Qseq J 1)) :
    ∀ j ∈ ramI H P Q, ∀ r : DirichletCharacter ℂ q × ℝ, r.2 ∈ A →
      ‖ramR H N Xd P Q j (chiBarCoeff q r.1 (memSCoeff Pseq Qseq J liouvilleC)) r.2‖
        ≤ Rbd := by
  refine rbd_binder_of_socket_chi_free (Rrad := Rrad) hA hT (fun t₁ χ => ?_)
  rw [← doorCofactor0_at_one_chiBar]
  exact hs t₁ χ

/-! ## §3 — THE `∀χ` SOCKET: `m4_supplier_complete` with the floor DISCHARGED

The bundle below is `m4_supplier_complete`'s own, conjunct for conjunct, in its own order,
with exactly two edits:

* the scale gate `exp 1 ≤ log X` is traded for the floor's `exp (exp 1) ≤ X`, which implies
  it (and which every consumer already carries — `M4DoorClose`'s `hXee`);
* the per-piece `CapFreeFloor3` hypothesis — the ONE character-dependent conjunct — is
  replaced by the `_vt` floor's own three: the modulus cap `q ≤ Qm`, the mask debit bound
  at every piece, and the loglog threshold at the `_vt` constant `K`.

Nothing else moves, and the conclusion becomes `∀ χ`. -/

/-- **THE `∀χ` DOOR SOCKET** (`m4_supplier_all_chi`).  For every modulus cap `Qm` there are
a wide-supply scale `X₀ > 0` and a floor constant `K ≥ 0` such that, under
`m4_supplier_complete`'s bundle (verbatim) together with the `_vt` floor's modulus cap, mask
debit and loglog threshold, EVERY character mod `q ≤ Qm` carries the door's co-factor socket
at the ceiling `2^J·R̄₀`.

The character quantifier is on the OUTSIDE of the socket and on the INSIDE of nothing: the
binder list never mentions `χ`.  That is the whole content — the supply side is uniform in
the character, so the `χ`-summed consumer pays no `φ(q)`. -/
theorem m4_supplier_all_chi (Qm : ℕ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (q : ℕ) [NeZero q] (Pseq Qseq : ℕ → ℕ)
        (H : ℝ) (N Xd P Q J Ps : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
        (cq L cg Cb X θ Rrad Tann t₁ Rbar0 c S D : ℝ),
        q ≤ Qm →
        Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
        (∀ 𝒥 ∈ (Finset.Icc 1 J).powerset,
          (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D) →
        40 * Real.log (Real.log (Real.log X))
            + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
                + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q
                + K + 25 + D)
          < Real.log (Real.log X) →
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        1 ≤ P → 1 ≤ Ps → 0 < Rrad → 0 < θ → θ ≤ 1 / 32 →
        P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        (∀ j ∈ ramI H P Q, TLBlockGates34 cq H P N Xd Mt kk Tann L cg Cb X θ Rrad j) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        (∀ j ∈ ramI H P Q, 1 ≤ Dd j) →
        (∀ j ∈ ramI H P Q, Dd j ≤ kk j) →
        (∀ j ∈ ramI H P Q, X₀ ≤ Real.sqrt (Xa j)) →
        (∀ j ∈ ramI H P Q, Real.sqrt (Xa j) ≤ ((kk j / Dd j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, pin2Gate ≤ ((kk j / Dd j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, Real.exp 1 ≤ Xa j) →
        (∀ j ∈ ramI H P Q, ((Mt j : ℕ) : ℝ) ≤ 2 * Xa j) →
        (∀ j ∈ ramI H P Q, 2 * Xa j ≤ X) →
        (∀ j ∈ ramI H P Q, 0 ≤ cofactorMfl X θ ((kk j / Dd j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, ∀ t : ℝ, |t| ≤ Tann → ∀ i : ℕ,
          ((kk j / Dd j : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa j →
            |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) →
        0 ≤ S →
        (∀ j ∈ ramI H P Q,
          cSq * caseASwide c Cb (cofactorMfl X θ ((kk j / Dd j : ℕ) : ℝ))
              ((kk j / Dd j : ℕ) : ℝ) (Xa j)
            + cSq * ((Dd j : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ S) →
        (∀ j ∈ ramI H P Q, 2 / ramRbot H Xd j
          ≤ cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
              (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad / 3) →
        (∀ j ∈ ramI H P Q,
          cofactorRbdGen S ((kk j : ℕ) : ℝ) ((Mt j : ℕ) : ℝ)
              (Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ))) Rrad ≤ Rbar0) →
        ∀ χ : DirichletCharacter ℂ q,
          CofactorSocket H N Xd P Q Tann Rrad t₁ (2 ^ J * Rbar0)
            (doorCofactor0 χ Pseq Qseq J Ps) := by
  obtain ⟨X₀, hX₀0, hsup⟩ := m4_supplier_complete
  obtain ⟨K, hK0, hK⟩ := capFreeFloor3_pieceDatum_vt Qm
  refine ⟨X₀, hX₀0, K, hK0, ?_⟩
  intro q _ Pseq Qseq H N Xd P Q' J Ps Mt kk Dd Xa cq L cg Cb X θ Rrad Tann t₁ Rbar0 c S D
    hq hXee hD0 hdebit hthr hc0 hce hc1 hCb0 hCbound hP1 hPs1 hR0 hθ0 hθ32 hPlow hQhigh hPQ
    hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0 hboxw hS0 hSbd hendGen hRbdU χ
  -- the floor's scale gate implies the supplier's
  have hLX : Real.exp 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 1)) hXee
    rwa [Real.log_exp] at h
  have hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 J).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X :=
    fun 𝒥 h𝒥 => hK q χ Pseq Qseq 𝒥 X D hq hXee hD0 (hdebit 𝒥 h𝒥) hthr
  exact hsup q χ Pseq Qseq H N Xd P Q' J Ps Mt kk Dd Xa cq L cg Cb X θ Rrad Tann t₁ Rbar0 c S
    hc0 hce hc1 hCb0 hCbound hP1 hPs1 hR0 hθ0 hθ32 hLX hPlow hQhigh hPQ hfloor hblk hbox
    hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0 hboxw hS0 hSbd hendGen hRbdU

/-! ## §4 — THE MEISSEL–MERTENS CONSTANT, FROM ABOVE

`SmallStones.mertensM_ge_neg_seventeen` is the lower numeral, from Mertens-2 at `t = 2`.
The same route from above gives only `M ≤ 1/2 − loglog 2 + 12/log 2 ≤ 19` — the `12/log t`
error is simply too large at `t = 2`, and sharpening it means computing `S(t)` at `t ≈ 90`.
The corpus's own identification is much cheaper. -/

/-- **THE MEISSEL–MERTENS UPPER NUMERAL** (`mertensM_le_two_thirds`).  `M ≤ 2/3`.

`Mertens.mertensM_eq_sub` is the landed identification `M = γ − B` (MERT-3c);
`Mertens.mertensB_nonneg` gives `B ≥ 0` (every `ppInner p = −log(1−1/p) − 1/p` is
nonnegative), and mathlib's `Real.eulerMascheroniConstant_lt_two_thirds` caps `γ`.  The
true value is `M ≈ 0.2615`. -/
theorem mertensM_le_two_thirds : Salt.Mertens.mertensM ≤ 2 / 3 := by
  have heq := Salt.Mertens.mertensM_eq_sub
  have hB := Salt.Mertens.mertensB_nonneg
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  linarith

/-- `M ≤ 3` — the round numeral the threshold page consumes (`mertensM_le_two_thirds` with
room to spare). -/
theorem mertensM_le_three : Salt.Mertens.mertensM ≤ 3 := by
  linarith [mertensM_le_two_thirds]

/-! ## §5 — THE THRESHOLD ARITHMETIC PAGE AT `q ≤ arcDen 12 H`

⟦THE LOG SCALES, KEPT APART⟧ every bound in this section reads the ARC's scale
`log H` — the modulus cap is `arcDen 12 H = (log H)^12` — while the threshold's
right-hand side is the FLOOR's scale `loglog X`.  The two are never substituted for one
another; the assembled condition carries both, and the consumer supplies the relation. -/

/-- `log((log H)^12) = 12·loglog H`. -/
lemma log_arcDen_twelve {H : ℕ} (hH : 0 < Real.log (H : ℝ)) :
    Real.log (arcDen 12 H) = 12 * Real.log (Real.log (H : ℝ)) := by
  rw [arcDen, Real.log_rpow hH]

/-- The arc's own scale floor: `e ≤ log H` gives `1 ≤ loglog H`. -/
lemma one_le_loglog_of_exp_le {H : ℕ} (hH : Real.exp 1 ≤ Real.log (H : ℝ)) :
    (1 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by
  have h := Real.log_le_log (Real.exp_pos 1) hH
  rwa [Real.log_exp] at h

/-- Past `e ≤ log H` the denominator cap clears `2` (it clears `e^12`). -/
lemma two_le_arcDen {H : ℕ} (hH : Real.exp 1 ≤ Real.log (H : ℝ)) :
    (2 : ℝ) ≤ arcDen 12 H := by
  have h1 : Real.exp 1 ^ (12 : ℝ) ≤ Real.log (H : ℝ) ^ (12 : ℝ) :=
    Real.rpow_le_rpow (Real.exp_pos 1).le hH (by norm_num)
  have h2 : Real.exp 1 ^ (12 : ℝ) = Real.exp 12 := Real.exp_one_rpow 12
  have h3 : (2 : ℝ) ≤ Real.exp 12 := by
    have := Real.add_one_le_exp (12 : ℝ); linarith
  rw [arcDen]
  rw [h2] at h1
  linarith

/-- **THE `log q` SUMMAND** (`log_le_of_le_arcDen`).  `q ≤ (log H)^12 ⟹ log q ≤ 12·loglog H`. -/
lemma log_le_of_le_arcDen {q H : ℕ} [NeZero q] (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ arcDen 12 H) :
    Real.log q ≤ 12 * Real.log (Real.log (H : ℝ)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogH : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hH
  have h := Real.log_le_log (by linarith : (0 : ℝ) < (q : ℝ)) hq
  rwa [log_arcDen_twelve hlogH] at h

/-- `mertensCap`'s argument is `max 2 q`, which obeys the same cap. -/
lemma log_max_two_le_of_le_arcDen {q H : ℕ} (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ arcDen 12 H) :
    Real.log ((max 2 q : ℕ) : ℝ) ≤ 12 * Real.log (Real.log (H : ℝ)) := by
  have hlogH : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hH
  have hcast : ((max 2 q : ℕ) : ℝ) = max 2 (q : ℝ) := by push_cast; rfl
  have hle : ((max 2 q : ℕ) : ℝ) ≤ arcDen 12 H := by
    rw [hcast]; exact max_le (two_le_arcDen hH) hq
  have hpos : (0 : ℝ) < ((max 2 q : ℕ) : ℝ) := by
    rw [hcast]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have h := Real.log_le_log hpos hle
  rwa [log_arcDen_twelve hlogH] at h

/-- **THE `mertensCap` SUMMAND** (`mertensCap_le_of_le_arcDen`).
`mertensCap q ≤ log(12·loglog H) + 21`: the `loglog` term by monotonicity, `M ≤ 3` by §4,
and `12/log(max 2 q) ≤ 12/log 2 ≤ 17.4`. -/
lemma mertensCap_le_of_le_arcDen {q H : ℕ} (hH : Real.exp 1 ≤ Real.log (H : ℝ))
    (hq : (q : ℝ) ≤ arcDen 12 H) :
    mertensCap q ≤ Real.log (12 * Real.log (Real.log (H : ℝ))) + 21 := by
  have hmax := log_max_two_le_of_le_arcDen hH hq
  have h2le : (2 : ℝ) ≤ ((max 2 q : ℕ) : ℝ) := by
    have h : (2 : ℕ) ≤ max 2 q := le_max_left _ _
    exact_mod_cast h
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogmax : Real.log 2 ≤ Real.log ((max 2 q : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) h2le
  have hlogmaxpos : (0 : ℝ) < Real.log ((max 2 q : ℕ) : ℝ) := lt_of_lt_of_le hlog2pos hlogmax
  have hll : Real.log (Real.log ((max 2 q : ℕ) : ℝ))
      ≤ Real.log (12 * Real.log (Real.log (H : ℝ))) := Real.log_le_log hlogmaxpos hmax
  have hdiv : 12 / Real.log ((max 2 q : ℕ) : ℝ) ≤ 12 / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) hlog2pos hlogmax
  have h12 : 12 / Real.log 2 ≤ 17.4 := by
    rw [div_le_iff₀ hlog2pos]
    linarith [Real.log_two_gt_d9]
  have hM := mertensM_le_three
  unfold mertensCap
  linarith

/-- `log 4 = 2·log 2` — used three times below. -/
private lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  push_cast; ring

/-- `log 10⁷ ≤ 20` (via `10⁷ ≤ 2²⁸`; the true value is `16.118…`). -/
private lemma log_ten_million_le : Real.log 10000000 ≤ 20 := by
  have h1 : Real.log 10000000 ≤ Real.log ((2 : ℝ) ^ (28 : ℕ)) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h1
  push_cast at h1
  linarith [Real.log_two_lt_d9]

/-- **THE VK CONSTANT'S LOGARITHM** (`log_vkEuler_mul_vkTwist_le`).
`log(vkEulerCorr q · vkTwistConst q) ≤ 20 + 3·log q`.  `vkEulerCorr q ≤ q` (each factor
`1 + 1/p ≤ p`, and the radical divides `q`), `vkTwistConst q = 10⁷·q·(1 + log q) ≤ 10⁷·q²`
(`1 + log q ≤ q`), so the product is `≤ 10⁷·q³`.  `FarL2.plog_vk_qdebit`'s page, which is
`private` there. -/
lemma log_vkEuler_mul_vkTwist_le {q : ℕ} [NeZero q] :
    Real.log (vkEulerCorr q * vkTwistConst q) ≤ 20 + 3 * Real.log q := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hlq : (1 : ℝ) + Real.log q ≤ (q : ℝ) := by
    have := Real.log_le_sub_one_of_pos hq0; linarith
  have hEC : vkEulerCorr q ≤ (q : ℝ) := by
    unfold vkEulerCorr
    calc ∏ p ∈ q.primeFactors, (1 + 1 / (p : ℝ))
        ≤ ∏ p ∈ q.primeFactors, (p : ℝ) := by
          refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
          have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
          have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
          have h1 : (1 : ℝ) / (p : ℝ) ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          linarith
      _ = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (q : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
            (Nat.prod_primeFactors_dvd q)
  have hECpos : (0 : ℝ) < vkEulerCorr q := vkEulerCorr_pos q
  have hTC : vkTwistConst q ≤ 10000000 * (q : ℝ) * (q : ℝ) := by
    unfold vkTwistConst
    nlinarith [hlq, hq1]
  have hTCpos : (0 : ℝ) < vkTwistConst q := by
    have := one_le_vkTwistConst (q := q); linarith
  have hprod : vkEulerCorr q * vkTwistConst q ≤ 10000000 * (q : ℝ) ^ 3 := by
    nlinarith [hEC, hTC, hECpos.le, hTCpos.le, hq1]
  have hprodpos : (0 : ℝ) < vkEulerCorr q * vkTwistConst q := by positivity
  have h := Real.log_le_log hprodpos hprod
  have hrw : Real.log (10000000 * (q : ℝ) ^ 3) = Real.log 10000000 + 3 * Real.log q := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  rw [hrw] at h
  linarith [log_ten_million_le]

/-- **THE `vkDebitConst` SUMMAND** (`vkDebitConst_le_of_le_arcDen`).
`vkDebitConst (vkEulerCorr q · vkTwistConst q) ≤ 10 + 9·loglog H`: the `X`-free head
`2log4 + (31/16)log2 ≤ 4.12` plus `(1/4)·(20 + 36·loglog H)`. -/
lemma vkDebitConst_le_of_le_arcDen {q H : ℕ} [NeZero q]
    (hH : Real.exp 1 ≤ Real.log (H : ℝ)) (hq : (q : ℝ) ≤ arcDen 12 H) :
    vkDebitConst (vkEulerCorr q * vkTwistConst q)
      ≤ 10 + 9 * Real.log (Real.log (H : ℝ)) := by
  have hlogq := log_le_of_le_arcDen hH hq
  have hC := log_vkEuler_mul_vkTwist_le (q := q)
  have h2 := Real.log_two_lt_d9
  have h4 := log_four_eq
  unfold vkDebitConst
  linarith

/-- **THE `vkMidDebitSharp` SUMMAND** (`vkMidDebitSharp_le_of_le_arcDen`).
`vkMidDebitSharp q ≤ 29 + (1/4)·log(7 + 12·loglog H)`.

The inner argument is `7/2 + log2 + log q + log(2e^{e^100} + 2)`.  Two roundings:
`2e^A + 2 ≤ 4e^A` puts the height term at `log 4 + e^100`, and `e^100 + B ≤ e^100·(1 + B)`
(valid for `B ≥ 0` since `e^100 ≥ 1`) pulls the `e^100` out of the logarithm as the
additive `100`.  What is left is `(1/4)·log(1 + B)` with `B = 6 + 12·loglog H`, and
`2log4 + (3/4)log2 + 25 ≤ 29`. -/
lemma vkMidDebitSharp_le_of_le_arcDen {q H : ℕ} [NeZero q]
    (hH : Real.exp 1 ≤ Real.log (H : ℝ)) (hq : (q : ℝ) ≤ arcDen 12 H) :
    vkMidDebitSharp q
      ≤ 29 + (1 / 4) * Real.log (7 + 12 * Real.log (Real.log (H : ℝ))) := by
  have hLH1 := one_le_loglog_of_exp_le hH
  have hlogq := log_le_of_le_arcDen hH hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq0 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have h2 := Real.log_two_lt_d9
  have h2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h4 := log_four_eq
  set LH : ℝ := Real.log (Real.log (H : ℝ)) with hLHdef
  have hE1 : (1 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h0 : (0 : ℝ) ≤ Real.exp 100 := (Real.exp_pos 100).le
    calc (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr h0
  have he100 : (1 : ℝ) ≤ Real.exp 100 := by
    have := Real.add_one_le_exp (100 : ℝ); linarith
  -- the height term: `log(2e^A + 2) ≤ log 4 + e^100`
  have hht : Real.log (2 * Real.exp (Real.exp 100) + 2) ≤ Real.log 4 + Real.exp 100 := by
    have hb : 2 * Real.exp (Real.exp 100) + 2 ≤ 4 * Real.exp (Real.exp 100) := by linarith
    have h1 : Real.log (2 * Real.exp (Real.exp 100) + 2)
        ≤ Real.log (4 * Real.exp (Real.exp 100)) := Real.log_le_log (by positivity) hb
    have h2' : Real.log (4 * Real.exp (Real.exp 100)) = Real.log 4 + Real.exp 100 := by
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    linarith
  -- the inner argument, rounded to `e^100 + (6 + 12·loglog H)`
  have hinner : 7 / 2 + Real.log 2 + Real.log q
      + Real.log (2 * Real.exp (Real.exp 100) + 2)
      ≤ Real.exp 100 + (6 + 12 * LH) := by linarith
  have hinner0 : (0 : ℝ) < 7 / 2 + Real.log 2 + Real.log q
      + Real.log (2 * Real.exp (Real.exp 100) + 2) := by
    have hnn : (0 : ℝ) ≤ Real.log (2 * Real.exp (Real.exp 100) + 2) :=
      Real.log_nonneg (by linarith)
    linarith
  -- pull `e^100` out of the logarithm
  have hB0 : (0 : ℝ) ≤ 6 + 12 * LH := by linarith
  have h7pos : (0 : ℝ) < 7 + 12 * LH := by linarith
  have hstep : Real.exp 100 + (6 + 12 * LH) ≤ Real.exp 100 * (7 + 12 * LH) := by
    nlinarith [he100, hB0]
  have hlogstep : Real.log (Real.exp 100 + (6 + 12 * LH))
      ≤ 100 + Real.log (7 + 12 * LH) := by
    have h1 : Real.log (Real.exp 100 + (6 + 12 * LH))
        ≤ Real.log (Real.exp 100 * (7 + 12 * LH)) :=
      Real.log_le_log (by linarith) hstep
    have h2' : Real.log (Real.exp 100 * (7 + 12 * LH)) = 100 + Real.log (7 + 12 * LH) := by
      rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt h7pos), Real.log_exp]
    linarith
  have hlogmono : Real.log (7 / 2 + Real.log 2 + Real.log q
        + Real.log (2 * Real.exp (Real.exp 100) + 2))
      ≤ Real.log (Real.exp 100 + (6 + 12 * LH)) := Real.log_le_log hinner0 hinner
  unfold vkMidDebitSharp
  linarith

/-- **THE ASSEMBLY** (`pieceFloor_vt_threshold_of_loglog`).  At the arc's modulus range
`q ≤ arcDen 12 H`, one explicit `loglog X` lower bound implies
`capFreeFloor3_pieceDatum_vt`'s threshold verbatim.

Summand budget (`ℓ₃ := logloglog X`, `Λ := loglog H`):
`4·log q ≤ 48Λ`, `8·mertensCap q ≤ 8·log(12Λ) + 168`,
`32·vkDebitConst ≤ 288Λ + 320`, `32·vkMidDebitSharp ≤ 8·log(7+12Λ) + 928`, and `32·25 = 800`
— total `336Λ + 16·log(7+12Λ) + 2216`, against the hypothesis's `350Λ + 20·log(7+12Λ) + 2300`.

The `_vt` constant `K` and the mask debit `D` are carried SYMBOLICALLY (each appears with
its own `32·` weight on both sides). -/
theorem pieceFloor_vt_threshold_of_loglog {q H : ℕ} [NeZero q] {X K D : ℝ}
    (hH : Real.exp 1 ≤ Real.log (H : ℝ)) (hq : (q : ℝ) ≤ arcDen 12 H)
    (hthr : 40 * Real.log (Real.log (Real.log X))
        + 350 * Real.log (Real.log (H : ℝ))
        + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
        + 2300 + 32 * K + 32 * D
      < Real.log (Real.log X)) :
    40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * mertensCap q
          + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebitSharp q
          + K + 25 + D)
      < Real.log (Real.log X) := by
  have hLH1 := one_le_loglog_of_exp_le hH
  set LH : ℝ := Real.log (Real.log (H : ℝ)) with hLHdef
  have hlogq := log_le_of_le_arcDen hH hq
  have hcap := mertensCap_le_of_le_arcDen (q := q) hH hq
  have hvkd := vkDebitConst_le_of_le_arcDen (q := q) hH hq
  have hvkm := vkMidDebitSharp_le_of_le_arcDen (q := q) hH hq
  -- the two logarithms, merged into `log(7 + 12Λ)`
  have h7pos : (0 : ℝ) < 7 + 12 * LH := by linarith
  have hmerge : Real.log (12 * LH) ≤ Real.log (7 + 12 * LH) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlognn : (0 : ℝ) ≤ Real.log (7 + 12 * LH) := Real.log_nonneg (by linarith)
  linarith

/-- **THE EXIT** (`capFreeFloor3_pieceDatum_arcDen`).  `capFreeFloor3_pieceDatum_vt` with
its threshold replaced by the arc-range `loglog` condition of
`pieceFloor_vt_threshold_of_loglog`.  This is the form a consumer whose modulus range is
the major-arc denominator cap `(log H)^12` reads.

The constant `K` is the `_vt` floor's own (the `capFreeFloor3_margin_all_chi_vt` witness);
it is carried symbolically, exactly as `cffKVt` is at the un-margined floor. -/
theorem capFreeFloor3_pieceDatum_arcDen (Qm : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (H : ℕ) (χ : DirichletCharacter ℂ q)
      (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X D : ℝ), q ≤ Qm →
      Real.exp 1 ≤ Real.log (H : ℝ) → (q : ℝ) ≤ arcDen 12 H →
      Real.exp (Real.exp 1) ≤ X → 0 ≤ D →
      (∑ j ∈ 𝒥, ∑ p ∈ blockWindowPrimes (Pseq j) (Qseq j) X, (1 : ℝ) / (p : ℝ)) ≤ D →
      40 * Real.log (Real.log (Real.log X))
          + 350 * Real.log (Real.log (H : ℝ))
          + 20 * Real.log (7 + 12 * Real.log (Real.log (H : ℝ)))
          + 2300 + 32 * K + 32 * D
        < Real.log (Real.log X) →
        CapFreeFloor3 (pieceDatum χ 𝒥 Pseq Qseq) X := by
  obtain ⟨K, hK0, hK⟩ := capFreeFloor3_pieceDatum_vt Qm
  refine ⟨K, hK0, ?_⟩
  intro q _ H χ Pseq Qseq 𝒥 X D hq hH harc hX hD0 hdebit hthr
  exact hK q χ Pseq Qseq 𝒥 X D hq hX hD0 hdebit
    (pieceFloor_vt_threshold_of_loglog hH harc hthr)

end Salt.MR
