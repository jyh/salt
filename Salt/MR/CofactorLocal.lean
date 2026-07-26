/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CofactorSupply

/-!
# CofactorLocal — R1 of `⟦V6b⟧`: THE LOCALIZED PER-`t` DICHOTOMY

`CofactorSupply`'s `pocket_transport` splits over the WHOLE contour box `|v| ≤ 3X`.  The
CASE-B arm it feeds therefore knows nothing about where the pocket centre `t₁'` sits, and the
transfer radius has to be supplied from outside — `USetPrice`'s ambient `hDmax : Tann + |t₁| ≤
Dmax`, which drags `Rmax ≥ Tann` into `farErr`'s `log(3 + Rmax(1+log Y))` and (⟦V6a⟧,
kernel-certified) refutes the whole grade.

**The localized twin** splits over the window that is the ONLY one the CASE-A floor is ever
consumed on (`CofactorGrade.caseA_rhs_socket`'s `hMwin`, at the truncation height
`T*(k, log k)`):

  `by_cases hpocket : ∃ v, |v − t| ≤ T*(M, log M) ∧ 𝔻²(ℓ(g_x), p^{iv}; X) ≤ (1/32−θ)·loglog X`

* the ¬-branch is the localized `hMwin` VERBATIM — the window `|v − t| ≤ T*(k, log k)` at any
  `k ∈ [k₀, M]` sits inside the split window by `Tstar_mono`, so the floor is available
  exactly where CASE A asks for it;
* the pocket branch now hands `|t − t₁'| ≤ T*(M, log M)` FOR FREE.  That IS the transfer
  radius, so CASE B runs at `Rmax := T*(M, log M)` and the ambient `Dmax` supply disappears
  from the hypothesis list altogether.

Everything remains `x`-free, so the `[0,1]` average of `spolyA_ramRcoeff_le_of_damp` is
untouched, and the exit is the SAME `cofactorRbd` — only its `Rmax` slot moved.

## What survives from the ambient arm, and what does not

* `CofactorDist.pocket_collision_window` is still needed, but **for the LOWER gate only**:
  `CofactorBall`'s `hRle : R ≤ 1 + |t − t₁'|` comes from `pocket_far_from_ball`, i.e. from the
  row's own far leg `R ≤ |t − t₁|` plus the collision `|t₁' − t₁| < 1`.  It is unchanged.
* The collision's own box gate `|t₁'| ≤ 3X` is now DERIVED, not assumed: `|t₁'| ≤ |t| +
  |t₁' − t| ≤ |t| + T*(M, log M)`, so the single contour gate
  `hTM : |t| + T*(M, log M) ≤ 3X` replaces `pocket_transport`'s `∀ k ∈ [k₀,M]` family
  (which is exactly that family's `k = M` member — the strongest one, by `Tstar_mono`).
* The far-leg UPPER gate `|t − t₁| ≤ Dmax` is GONE.  `Dmax` does not occur in this file.

## The stones

* **§1 `Tstar_window_mono`** — the split window dominates every consumed window.
* **§2 (L-1) `pocket_transport_local`** — the localized dichotomy.
* **§3 (L-2) `cofactor_Rbd_local`** — the fused `Rbd` at `Rmax = T*(M, log M)`.
* **§4 (L-3) `tL_supply_discharged_local`** — the `𝒯_L` consumer at the localized `Rbd`.
* **§5 (L-4) `farErr_local_le` / `farErr_local_of_gate` / `farErr_local_window_ge`** —
  THE CERTIFICATE.  The localized numerator is `log T*(Y, log Y) = 4·loglog Y +
  log Y/(4·loglog Y)`, an `L/(4 log L)` scale in place of ⟦V6a⟧'s `log Tann ≥ 30√(log X)`.
  That is a genuine gain and it is **still not enough**: against `√(log kmin)` below, the
  ratio is `√(log W)/log log W → ∞` (`farErr_local_window_ge`, a LOWER bound — the honest
  witness that R1 alone does not close).  ⟦V6b⟧'s R2 (the `y` re-pin `log y = L^{2/5}`) is
  what closes it; R1 is the structural half.

## Law #253 — every gate in the open

`ballMertensThreshold ≤ k₀`, `e^{64} ≤ k₀`, `M ≤ X`, the loglog descent gate, the single
contour gate `hTM`, the far-leg LOWER gate `R ≤ |t − t₁|`, the endpoint charge: all
in-statement.  Nothing is absorbed.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the split window dominates every consumed window -/

/-- `k ↦ T*(k, log k)` climbs across the co-factor window, so the ONE window
`|v − t| ≤ T*(M, log M)` contains every window `|v − t| ≤ T*(k, log k)`, `k ∈ [k₀, M]`, that
`CofactorGrade`'s `hMwin` is consumed on.  The gate is `Tstar_mono`'s `e^e ≤ k`, and
`ballMertensThreshold = e^{e^{40}}` clears it by a tower. -/
lemma Tstar_window_mono {k₀ M k : ℕ} (hk₀th : ballMertensThreshold ≤ (k₀ : ℝ))
    (hk1 : k₀ ≤ k) (hk2 : k ≤ M) :
    Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ Tstar (M : ℝ) (Real.log (M : ℝ)) := by
  have hthr : Real.exp (Real.exp 1) ≤ ballMertensThreshold := by
    unfold ballMertensThreshold
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))
  have hk₀k : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hee : Real.exp (Real.exp 1) ≤ (k : ℝ) := by linarith
  have hkM : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk2
  exact Tstar_mono hee hkM

/-- **NOTHING IS SMUGGLED.**  The single contour gate `hTM` this file runs on is EQUIVALENT
to `CofactorSupply.cofactor_Rbd`'s contour family `∀ k ∈ [k₀,M], |t| + T*(k, log k) ≤ 3X`:
`→` is `Tstar_window_mono`, `←` is the family's own `k = M` member.  So R1 does not weaken a
hypothesis to make the pocket branch cheaper — it only stops asking for `Dmax`. -/
lemma contour_gate_local_iff {k₀ M : ℕ} {t X : ℝ} (hk₀M : k₀ ≤ M)
    (hk₀th : ballMertensThreshold ≤ (k₀ : ℝ)) :
    (|t| + Tstar (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * X)
      ↔ (∀ k : ℕ, k₀ ≤ k → k ≤ M → |t| + Tstar (k : ℝ) (Real.log (k : ℝ)) ≤ 3 * X) := by
  constructor
  · intro hTM k hk1 hk2
    have := Tstar_window_mono hk₀th hk1 hk2
    linarith
  · intro hfam
    exact hfam M hk₀M le_rfl

/-! ## §2 (L-1) — THE LOCALIZED DICHOTOMY

The split is taken at the GLOBAL scale `X` (so the pocket still descends for free and the
floor still pays exactly one Mertens tail), but over the LOCAL window `|v − t| ≤ T*(M, log M)`
instead of the whole box `|v| ≤ 3X`.  That single change is what makes the pocket branch
hand back a radius. -/

/-- **L-1 — THE LOCALIZED POCKET TRANSPORT** (`pocket_transport_local`).  At a FIXED damping
parameter `x ∈ [0,1]`: either the CASE-A window floor holds at the value `cofactorMfl X θ k₀`
on every consumed window, or the CASE-B pocket family exists at `x` — **with its centre
already inside the truncation window**, `|t − t₁'| ≤ T*(M, log M)`.

The twin of `CofactorSupply.pocket_transport`; the three transports are unchanged (the twist
slot is `caseA_partial_supply_slice`'s, the pocket's descent is free by
`pretDistSq_mono_scale`, the floor's is priced by `pretDistSq_tail_le`).  The differences,
and only these:

1. the `by_cases` window is `|v − t| ≤ T*(M, log M)` instead of `|v| ≤ 3X`;
2. the ¬-branch needs `Tstar_window_mono` to move from the consumed window at `k` to the
   split window at `M` (transport 3 becomes a monotonicity, not a contour gate);
3. the pocket branch now REPORTS `|t − t₁'| ≤ T*(M, log M)`, and derives `|t₁'| ≤ 3X` from
   the single contour gate `hTM` rather than assuming it.

`hll` is the loglog descent gate, verbatim: the pocket at grade `(1/32 − θ)loglog X` must sit
under the A.4 window cap `(1/16)loglog k₀`. -/
theorem pocket_transport_local {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (P Q : ℕ)
    {k₀ M : ℕ} {X θ t x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hk₀th : ballMertensThreshold ≤ (k₀ : ℝ)) (hMX : (M : ℝ) ≤ X)
    (hll : (1 / 32 - θ) * Real.log (Real.log X) ≤ (1 / 16) * Real.log (Real.log (k₀ : ℝ)))
    (hTM : |t| + Tstar (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * X) :
    (∀ k : ℕ, k₀ ≤ k → k ≤ M → ∀ v : ℝ, |v - t| ≤ Tstar (k : ℝ) (Real.log (k : ℝ)) →
        cofactorMfl X θ (k₀ : ℝ)
          ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) (k : ℝ))
      ∨ (∃ t₁' : ℝ, |t - t₁'| ≤ Tstar (M : ℝ) (Real.log (M : ℝ)) ∧ |t₁'| ≤ 3 * X ∧
          pretDistSq (ellLin (gxDatum g P Q x)) (costwist t₁') X
            ≤ (1 / 32 - θ) * Real.log (Real.log X) ∧
          ∀ y : ℝ, (k₀ : ℝ) ≤ y → y ≤ (M : ℝ) →
            pretDistSq (fun n => ellLin (gxDatum g P Q x) n * eIu (-t₁') n) (fun _ => 1) y
              ≤ Salt.Mertens.SPartial y / 8) := by
  classical
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum g P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx0 hx1 hg p hp
  have hEll : ∀ n : ℕ, ‖ellLin (gxDatum g P Q x) n‖ ≤ 1 := ellLin_norm_le_one _ hgx
  by_cases hpocket : ∃ v : ℝ, |v - t| ≤ Tstar (M : ℝ) (Real.log (M : ℝ)) ∧
      pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) X
        ≤ (1 / 32 - θ) * Real.log (Real.log X)
  · -- the pocket arm: the descent to the window is FREE, and the RADIUS comes with it
    right
    obtain ⟨v, hvwin, hv⟩ := hpocket
    have hvabs : |v| ≤ 3 * X := by
      have h1 : |v| ≤ |v - t| + |t| := by
        have := abs_add_le (v - t) t
        simpa using this
      linarith
    have hrad : |t - v| ≤ Tstar (M : ℝ) (Real.log (M : ℝ)) := by
      rw [abs_sub_comm]; exact hvwin
    refine ⟨v, hrad, hvabs, hv, ?_⟩
    intro y hy1 hy2
    rw [← pretDistSq_twist_slot]
    have hcw : ∀ n : ℕ, ‖costwist v n‖ ≤ 1 := fun n => le_of_eq (costwist_norm v n)
    have hmono : pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) y
        ≤ pretDistSq (ellLin (gxDatum g P Q x)) (costwist v) X :=
      pretDistSq_mono_scale hEll hcw (le_trans hy2 hMX)
    have h16 := sixteenth_loglog_le_SPartial_div_eight hk₀th hy1
    linarith
  · -- the floor arm: the descent to the window is PRICED, and the window is the LOCAL one
    left
    simp only [not_exists, not_and, not_le] at hpocket
    intro k hk1 hk2 v hv
    have hcw : ∀ n : ℕ, ‖costwist v n‖ ≤ 1 := fun n => le_of_eq (costwist_norm v n)
    -- transport 3, localized: the consumed window sits inside the split window
    have hvwin : |v - t| ≤ Tstar (M : ℝ) (Real.log (M : ℝ)) :=
      le_trans hv (Tstar_window_mono hk₀th hk1 hk2)
    have hXbig := hpocket v hvwin
    -- transport 2: the priced ascent, charged at the window bottom
    have hkM : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk2
    have hkX : ⌊(k : ℝ)⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono (le_trans hkM hMX)
    have htail := pretDistSq_tail_le (f := ellLin (gxDatum g P Q x)) (g := costwist v)
      hEll hcw hkX
    have hSk : Salt.Mertens.SPartial (k₀ : ℝ) ≤ Salt.Mertens.SPartial (k : ℝ) := by
      refine SPartial_mono_floor ?_
      rw [Nat.floor_natCast, Nat.floor_natCast]
      exact hk1
    unfold cofactorMfl
    linarith

/-! ## §3 (L-2) — THE FUSED `Rbd` AT THE LOCALIZED RADIUS

The dichotomy is discharged INSIDE the proof, one damping parameter at a time, at
`spolyA_ramRcoeff_le_of_damp`'s binder — exactly as in `CofactorSupply.cofactor_Rbd`.  The
only structural change is that CASE B's radius is no longer imported: L-1 produces it. -/

/-- **L-2 — THE LOCALIZED CO-FACTOR `Rbd`** (`cofactor_Rbd_local`).  The twin of
`CofactorSupply.cofactor_Rbd` at

  `Rmax := T*(M, log M)`   (in place of the ambient `Dmax + 1`),

i.e.

  `‖R_{j,H}(1+it)‖ ≤ cofactorRbd c Cb X θ k₀ M (T*(M, log M)) R
                   = 3·max (2·caseAS c Cb (cofactorMfl X θ k₀) k₀)
                           (farSupS k₀ M (T*(M, log M)) R)`.

**THE HYPOTHESIS DIFF versus `cofactor_Rbd` — this is the whole point of R1.**

*Removed.*  `Dmax` itself, and with it the far-leg UPPER gate `|t − t₁| ≤ Dmax` — the
binder whose only supply is `USetPrice`'s ambient `hDmax : Tann + |t₁| ≤ Dmax`, which is what
forces `Rmax ≥ Tann` and (⟦V6a⟧) refutes the grade.

*Replaced.*  `cofactor_Rbd`'s contour family `∀ k ∈ [k₀,M], |t| + T*(k, log k) ≤ 3X` by its
single strongest member `hTM : |t| + T*(M, log M) ≤ 3X` (`Tstar_window_mono`).  **Stated
honestly: this gate is still needed**, because `pocket_collision_window` is still consumed —
see below — and its box binder `|t₁'| ≤ 3X` is exactly what `hTM` supplies.  It is however
weaker than the family, and it is the ONLY place `3X` occurs.

*Kept verbatim.*  Everything else: the `c`-contract, the amplitude datum, the two scale gates
at the shifted scale, the seven window-geometry binders, `M ≤ X`, the loglog descent gate,
the collision inputs at the global scale (`collisionGate X 25 C` included), the far-leg
LOWER gate `0 < R`, `R ≤ |t − t₁|`, the floor value `0 ≤ cofactorMfl X θ k₀`, and the
half-open endpoint charge `hend` — now read at the localized `Rbd`.

**Why the collision survives.**  `CofactorBall`'s CASE-B input is a pair of radius facts:
the UPPER one `|t − t₁'| ≤ Rmax` (which L-1 now hands over for free) and the LOWER one
`R ≤ 1 + |t − t₁'|`, which is `pocket_far_from_ball` applied to the row's own far leg
`R ≤ |t − t₁|` and the collision `|t₁' − t₁| < 1`.  Only the UPPER one was ever `Dmax`-fed. -/
theorem cofactor_Rbd_local :
    ∃ X₀ C : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ) (N Xn P Q j M k₀ : ℕ) (c Cb X θ t t₁ R : ℝ),
        -- (2),(3) the `c`-contract and the amplitude datum
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        -- (4),(6) the scale gates, at the SHIFTED scale
        X₀ ≤ (k₀ : ℝ) → Real.exp 64 ≤ (k₀ : ℝ) → ballMertensThreshold ≤ (k₀ : ℝ) →
        -- (9) the co-factor window geometry
        M ≤ N → (k₀ : ℝ) < ramRbot H Xn j → ramRbot H Xn j ≤ (k₀ : ℝ) + 1 →
        1 < ramRbot H Xn j → ramRbot H Xn j - 1 ≤ (M : ℝ) →
        (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) → 2 * ramRbot H Xn j < (M : ℝ) + 3 →
        -- (11),(12),(13') THE TRANSPORT GATES — (13') is the LOCALIZED contour gate
        (M : ℝ) ≤ X →
        (1 / 32 - θ) * Real.log (Real.log X) ≤ (1 / 16) * Real.log (Real.log (k₀ : ℝ)) →
        |t| + Tstar (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * X →
        -- (7) the collision inputs, at the GLOBAL scale
        Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 0 < θ → θ ≤ 1 / 32 →
        P83 X θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 C →
        -- (8) the far leg — the LOWER gate only
        0 < R → R ≤ |t - t₁| →
        -- (5) the floor value, and (10) the half-open endpoint charge
        0 ≤ cofactorMfl X θ (k₀ : ℝ) →
        2 / ramRbot H Xn j
          ≤ cofactorRbd c Cb X θ (k₀ : ℝ) (M : ℝ) (Tstar (M : ℝ) (Real.log (M : ℝ))) R / 3 →
        ‖ramR H N Xn P Q j (ellLin g) t‖
          ≤ cofactorRbd c Cb X θ (k₀ : ℝ) (M : ℝ) (Tstar (M : ℝ) (Real.log (M : ℝ))) R := by
  obtain ⟨X₀, hX₀0, hslice⟩ := caseA_partial_supply_slice
  obtain ⟨C, hC⟩ := pocket_collision_window
  refine ⟨X₀, C, hX₀0, ?_⟩
  intro g hg H N Xn P Q j M k₀ c Cb X θ t t₁ R hc0 hce hc1 hCb0 hCbound hX₀k hk₀64
    hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX hll hTM hX hLX hθ0 hθ32 hPlow hQhigh
    hPQ ht₁ hrow hgate hR0 hfar hMfl0 hend
  -- the window arithmetic (`caseA_ramR_bound`'s own)
  have hk₀0 : (0 : ℝ) < (k₀ : ℝ) := lt_of_lt_of_le (Real.exp_pos 64) hk₀64
  have hk₀3R : (3 : ℝ) ≤ (k₀ : ℝ) := by
    have h65 : (65 : ℝ) ≤ (k₀ : ℝ) := by linarith [Real.add_one_le_exp (64 : ℝ)]
    linarith
  have hk₀3 : 3 ≤ k₀ := by exact_mod_cast hk₀3R
  have hk₀e : Real.exp 1 ≤ (k₀ : ℝ) := le_trans (Real.exp_le_exp.mpr (by norm_num)) hk₀64
  have hk₀MR : (k₀ : ℝ) ≤ (M : ℝ) := by linarith
  have hk₀M : k₀ ≤ M := by exact_mod_cast hk₀MR
  have hM2k₀ : (M : ℝ) ≤ 2 * (k₀ : ℝ) := by linarith
  have hfl : ⌊((k₀ : ℕ) : ℝ)⌋₊ = k₀ := Nat.floor_natCast k₀
  have hk64 : ∀ k : ℕ, ⌊((k₀ : ℕ) : ℝ)⌋₊ ≤ k → k ≤ M → Real.exp 64 ≤ (k : ℝ) := by
    intro k hk1 _
    rw [hfl] at hk1
    have : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  set S : ℝ := max (2 * caseAS c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ))
    (farSupS (k₀ : ℝ) (M : ℝ) (Tstar (M : ℝ) (Real.log (M : ℝ))) R) with hS
  have hSA : 2 * caseAS c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) ≤ S := le_max_left _ _
  have hSB : farSupS (k₀ : ℝ) (M : ℝ) (Tstar (M : ℝ) (Real.log (M : ℝ))) R ≤ S :=
    le_max_right _ _
  have hRbdS :
      cofactorRbd c Cb X θ (k₀ : ℝ) (M : ℝ) (Tstar (M : ℝ) (Real.log (M : ℝ))) R = 3 * S := rfl
  have hendS : 2 / ramRbot H Xn j ≤ S := by
    rw [hRbdS] at hend; linarith
  rw [hRbdS]
  refine ramR_abel_sup (fun n => ellLin_norm_le_one g hg n) hbot hlow hhigh hMtop hendS ?_
  intro m hm
  refine spolyA_ramRcoeff_le_of_damp ?_
  intro x hx
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases pocket_transport_local hg P Q hx.1 hx.2 hk₀th hMX hll hTM with hA | hB
  · -- CASE A at this `x` — unchanged from the ambient arm
    have hsup : ∀ k : ℕ, k₀ ≤ k → k ≤ M →
        ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t) n‖
          ≤ caseAS c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) * (k : ℝ) := by
      intro k hk1 hk2
      refine hslice g hg P Q c Cb t (k₀ : ℝ) (cofactorMfl X θ (k₀ : ℝ)) x M hx.1 hx.2 hc0 hce
        hc1 hCb0 hCbound hX₀k hk₀e hk₀MR hM2k₀ hk64 hMfl0 ?_ k (by rw [hfl]; exact hk1) hk2
      intro k' hk1' hk2' v hv
      rw [hfl] at hk1'
      exact hA k' hk1' hk2' v hv
    have hS0 : (0 : ℝ) ≤ caseAS c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) :=
      caseAS_nonneg hc1 hCb0 (by linarith)
    have hbd := caseA_damped_partial (g := g) (H := H) (N := N) (Xn := Xn) (P := P) (Q := Q)
      (j := j) (M := M) (k₀ := k₀) (x := x) (t := t) hS0 hMN hk₀M hk₀lo hk₀hi hhigh hsup m hm
    have hmul : 2 * caseAS c Cb (cofactorMfl X θ (k₀ : ℝ)) (k₀ : ℝ) * (m : ℝ) ≤ S * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hSA hm0
    linarith
  · -- CASE B at this `x` — the radius arrives WITH the pocket
    obtain ⟨t₁', hRmax, ht₁'abs, hpock, hcap⟩ := hB
    have hcoll := hC g hg P Q X x θ t₁ t₁' hX hLX hθ0 hθ32 hx.1 hx.2 hPlow hQhigh hPQ ht₁
      ht₁'abs hrow hpock hgate
    have hRle : R ≤ 1 + |t - t₁'| := by
      have := pocket_far_from_ball hcoll hfar
      linarith
    have hbd := damped_partial_transfer hg hx.1 hx.2 hk₀3 hMN hk₀lo hk₀hi hhigh hcap hR0 hRle
      hRmax m hm
    have hmul : farSupS (k₀ : ℝ) (M : ℝ) (Tstar (M : ℝ) (Real.log (M : ℝ))) R * (m : ℝ)
        ≤ S * (m : ℝ) := mul_le_mul_of_nonneg_right hSB hm0
    linarith

/-! ## §4 (L-3) — THE `𝒯_L` CONSUMER AT THE LOCALIZED `Rbd`

`USetThinTL.tL_main_sumsq`'s `Rbd` socket, filled by §3 instead of by
`CofactorSupply.cofactor_Rbd`.  The composition is `tL_supply_discharged`'s, verbatim; what
changes is only what the per-`t` bundle has to promise. -/

/-- **L-3 — THE LOCALIZED `𝒯_L` EXIT** (`tL_supply_discharged_local`).

  `Σ_{t∈𝒯_L} ‖Q_{j,H}·R_{j,H}‖² ≤ 54·C_q·Rbd_loc²·(H/j)²`,
  `Rbd_loc = cofactorRbd cg Cb Xg θ k₀ M (T*(M, log M)) R`,

the twin of `CofactorSupply.tL_supply_discharged` with the co-factor supply taken from
`cofactor_Rbd_local`.

**The per-`t` bundle `hTL_loc` is where R1 pays off.**  `tL_supply_discharged` demands, at
every `𝒯_L` ordinate,

  `R ≤ |t − t₁|` **and** `|t − t₁| ≤ Dmax` **and** `∀ k ∈ [k₀,M], |t| + T*(k, log k) ≤ 3Xg`.

Here it demands

  `R ≤ |t − t₁|` **and** `|t| + T*(M, log M) ≤ 3Xg`

— the middle conjunct is gone.  That conjunct is the one `USetPrice.hU_fully_priced` supplies
from `hDmax : Tann + |t₁| ≤ Dmax`, forcing `Rmax ≥ Tann` into `farErr`; the localized bundle
never mentions `Dmax`, so a consumer of this stone is free of the ⟦V6a⟧ floor.  Both
remaining conjuncts are `𝒰`-side geometry of the ordinate set, stated (law #253). -/
theorem tL_supply_discharged_local :
    ∃ Cq cq T₀ X₀ C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ), 2 ≤ H → ∀ (P Q j N Xn M k₀ : ℕ) (cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      H ≤ (j : ℝ) →
      -- U-8's own window
      ∀ (T V L δ' : ℝ) (𝒯 : Finset ℝ), WellSpaced 𝒯 →
      (∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) → T₀ ≤ T → 1 < T →
      3 ≤ ramQbase H P j → (ramQbase H P j : ℝ) ≤ T →
      30 ≤ Real.log T / Real.log (ramQbase H P j) →
      5 ≤ Real.log (Real.log T) → 1 ≤ V → V⁻¹ ≤ δ' →
      Real.log T ≤ L → 1 ≤ Real.log T → Real.exp 1 ≤ L →
      Real.log (ramQbase H P j) ≤ L → Real.log V ≤ 100 * Real.log L →
      420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cq * (Real.log (ramQbase H P j)) ^ 2 →
      -- U-7's own gates (all `t`-free), with `Dmax` GONE
      ∀ (cg Cb Xg θ t₁ R : ℝ),
        0 < cg → cg ≤ 1 / Real.exp 1 → 2 * cg < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ (k₀ : ℝ) → Real.exp 64 ≤ (k₀ : ℝ) → ballMertensThreshold ≤ (k₀ : ℝ) →
        M ≤ N → (k₀ : ℝ) < ramRbot H Xn j → ramRbot H Xn j ≤ (k₀ : ℝ) + 1 →
        1 < ramRbot H Xn j → ramRbot H Xn j - 1 ≤ (M : ℝ) →
        (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) → 2 * ramRbot H Xn j < (M : ℝ) + 3 →
        (M : ℝ) ≤ Xg →
        (1 / 32 - θ) * Real.log (Real.log Xg)
          ≤ (1 / 16) * Real.log (Real.log (k₀ : ℝ)) →
        Real.exp 1 ≤ Xg → Real.exp 1 ≤ Real.log Xg → 0 < θ → θ ≤ 1 / 32 →
        P83 Xg θ ≤ (P : ℝ) → (Q : ℝ) ≤ Q83 Xg → P ≤ Q → |t₁| ≤ Xg →
        pretDistSq (ellLin g) (costwist t₁) Xg ≤ (1 / 16) * Real.log (Real.log Xg) →
        collisionGate Xg 25 C → 0 < R →
        0 ≤ cofactorMfl Xg θ (k₀ : ℝ) →
        2 / ramRbot H Xn j
          ≤ cofactorRbd cg Cb Xg θ (k₀ : ℝ) (M : ℝ)
              (Tstar (M : ℝ) (Real.log (M : ℝ))) R / 3 →
        -- the per-`t` gates on the `𝒯_L` branch: the far LOWER leg and the local contour box
        (∀ t ∈ tLset H P Q j cf δ' 𝒯, R ≤ |t - t₁| ∧
          |t| + Tstar (M : ℝ) (Real.log (M : ℝ)) ≤ 3 * Xg) →
        ∑ t ∈ tLset H P Q j cf δ' 𝒯, ‖ramMain H N Xn P Q (ellLin g) cf j t‖ ^ 2
          ≤ 54 * Cq * cofactorRbd cg Cb Xg θ (k₀ : ℝ) (M : ℝ)
                (Tstar (M : ℝ) (Real.log (M : ℝ))) R ^ 2
              * (H / (j : ℝ)) ^ 2 := by
  obtain ⟨Cq, cq, T₀, hCq, hcq, hT₀, htL⟩ := tL_main_sumsq
  obtain ⟨X₀, C, hX₀0, hRbd⟩ := cofactor_Rbd_local
  refine ⟨Cq, cq, T₀, X₀, C, hCq, hcq, hT₀, hX₀0, ?_⟩
  intro g hg H hH P Q j N Xn M k₀ cf hcf1 hHj T V L δ' 𝒯 hws hsub hT₀T hT hB3 hBT hκ30 hLL5
    hV1 hVδ hTL hlogT1 hLe hWL hlogV hkill cg Cb Xg θ t₁ R hc0 hce hc1 hCb0 hCbound
    hX₀k hk₀64 hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX hll hX hLX hθ0 hθ32 hPlow
    hQhigh hPQ ht₁ hrow hgate hR0 hMfl0 hend hper
  have hk₀1 : (1 : ℝ) ≤ (k₀ : ℝ) := by
    have h65 : (65 : ℝ) ≤ (k₀ : ℝ) := by
      linarith [Real.add_one_le_exp (64 : ℝ), hk₀64]
    linarith
  refine htL H hH P Q j N Xn cf (ellLin g) hcf1 hHj T V L δ'
    (cofactorRbd cg Cb Xg θ (k₀ : ℝ) (M : ℝ) (Tstar (M : ℝ) (Real.log (M : ℝ))) R) 𝒯 hws hsub
    hT₀T hT hB3 hBT hκ30 hLL5 hV1 hVδ hTL hlogT1 hLe hWL hlogV hkill
    (cofactorRbd_nonneg hc1 hCb0 hk₀1) ?_
  intro t ht
  obtain ⟨hfar, hTM⟩ := hper t ht
  exact hRbd g hg H N Xn P Q j M k₀ cg Cb Xg θ t t₁ R hc0 hce hc1 hCb0 hCbound hX₀k
    hk₀64 hk₀th hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hMX hll hTM hX hLX hθ0 hθ32 hPlow
    hQhigh hPQ ht₁ hrow hgate hR0 hfar hMfl0 hend

/-! ## §5 (L-4) — THE CERTIFICATE: what the localized radius buys, and what it does not

`farErr W Y Rmax = 4·ballSupC·(1 + log(3 + Rmax·(1 + log Y)))/√(log W)`.  R1 moves the `Rmax`
slot from the ambient `Dmax + 1 ≥ Tann` to `T*(M, log M)`.  ⟦V6a⟧'s refutation ran on
`TannGate X Tann → Tann ≥ exp(30·(log X)^{1/2})`, i.e. `log Rmax ≥ 30·√(log X)` — hopeless
against `√(log kmin) ≤ √(log X)` below.  Localized,

  `log T*(Y, log Y) = 4·loglog Y + log Y/(4·loglog Y)`,

an `L/(4 log L)` scale.  That is the gain, and it is real.  It is **not** the closure: with
`W ≤ Y ≤ W²` (the co-factor window's own geometry, `k₀ ≤ M ≤ 2k₀`) the quotient is still
`≳ √(log W)/(1 + loglog W) → ∞`, which no `(log X)^{−2θ₂₉₃}` gate can absorb.  ⟦V6b⟧ says
exactly this: R1 + R3 are the certificate pair, R2 (the `y` re-pin `log y = L^{2/5}`, which
replaces the `1/(4 log L)` exponent by `L^{−2/5}`) is what closes it. -/

/-- `a ≤ b → 0 ≤ c → a/c ≤ b/c`, in the one form §5 divides by. -/
private lemma div_le_div_same {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  have h : a * c⁻¹ ≤ b * c⁻¹ := mul_le_mul_of_nonneg_right hab (inv_nonneg.mpr hc)
  rwa [← div_eq_mul_inv, ← div_eq_mul_inv] at h

/-- **The localized truncation height, logarithmically.**
`log T*(Y, log Y) = 4·loglog Y + log Y/(4·loglog Y)` — the exact exit factor GS 7.1's
`d`-split hands `ballErr`, with nothing absorbed. -/
lemma log_Tstar_self {Y : ℝ} (hY : Real.exp (Real.exp 1) ≤ Y) :
    Real.log (Tstar Y (Real.log Y))
      = 4 * Real.log (Real.log Y) + Real.log Y / (4 * Real.log (Real.log Y)) := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hLe : Real.exp 1 ≤ Real.log Y := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hY
  have hL1 : (1 : ℝ) < Real.log Y := lt_of_lt_of_le (by linarith [Real.exp_one_gt_d9]) hLe
  have hL0 : (0 : ℝ) < Real.log Y := by linarith
  have hll1 : (1 : ℝ) ≤ Real.log (Real.log Y) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hLe
  have hll0 : (0 : ℝ) < Real.log (Real.log Y) := by linarith
  have hp0 : (Real.log Y : ℝ) ^ 4 ≠ 0 := by positivity
  have hr0 : (Y : ℝ) ^ (1 / (4 * Real.log (Real.log Y))) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hY0 _)
  unfold Tstar
  rw [Real.log_mul hp0 hr0, Real.log_pow, Real.log_rpow hY0, Nat.cast_ofNat]
  field_simp

/-- **L-4 — THE CERTIFICATE (upper).**  At the localized radius,

  `farErr W Y (T*(Y, log Y))
     ≤ 4·ballSupC·(3 + 5·loglog Y + log Y/(4·loglog Y))/√(log W)`.

Every constant is explicit (law #253): the `3` absorbs `1 + 2·log 2`, the `5·loglog Y`
absorbs `log T*`'s own `4·loglog Y` plus the `log(1 + log Y)` of the `(1 + log Y)` weight, and
`log Y/(4·loglog Y)` is the leading term — `T*`'s `k^{1/(4 log log k)}` exponent, the whole
content of the localization.  Compare ⟦V6a⟧'s ambient numerator, which carries
`log Tann ≥ 30·√(log X)` instead. -/
theorem farErr_local_le {W Y : ℝ} (hY : Real.exp (Real.exp 1) ≤ Y) :
    farErr W Y (Tstar Y (Real.log Y))
      ≤ 4 * ballSupC
          * (3 + 5 * Real.log (Real.log Y)
              + Real.log Y / (4 * Real.log (Real.log Y)))
        / Real.sqrt (Real.log W) := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hY1 : (1 : ℝ) ≤ Y := by
    have h : (1 : ℝ) ≤ Real.exp (Real.exp 1) := Real.one_le_exp (Real.exp_pos 1).le
    linarith
  have hLe : Real.exp 1 ≤ Real.log Y := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hY
  have hL2 : (2 : ℝ) < Real.log Y := lt_of_lt_of_le (by linarith [Real.exp_one_gt_d9]) hLe
  have hL0 : (0 : ℝ) < Real.log Y := by linarith
  have hll1 : (1 : ℝ) ≤ Real.log (Real.log Y) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hLe
  have hll0 : (0 : ℝ) < Real.log (Real.log Y) := by linarith
  -- the truncation height itself
  have hT4 : Real.log Y ^ 4 ≤ Tstar Y (Real.log Y) := Tstar_ge hY1 (by linarith)
  have hT16 : (16 : ℝ) ≤ Real.log Y ^ 4 := by
    have h : (2 : ℝ) ^ 4 ≤ Real.log Y ^ 4 := pow_le_pow_left₀ (by norm_num) hL2.le 4
    norm_num at h; linarith
  have hT3 : (3 : ℝ) ≤ Tstar Y (Real.log Y) := by linarith
  have hT0 : (0 : ℝ) < Tstar Y (Real.log Y) := by linarith
  have hlogT := log_Tstar_self hY
  -- `3 + T·(1+log Y) ≤ 2·T·(1+log Y)`
  have hprod : (3 : ℝ) ≤ Tstar Y (Real.log Y) * (1 + Real.log Y) := by nlinarith
  have hstep1 : Real.log (3 + Tstar Y (Real.log Y) * (1 + Real.log Y))
      ≤ Real.log (2 * (Tstar Y (Real.log Y) * (1 + Real.log Y))) :=
    Real.log_le_log (by linarith) (by linarith)
  have hstep2 : Real.log (2 * (Tstar Y (Real.log Y) * (1 + Real.log Y)))
      = Real.log 2 + Real.log (Tstar Y (Real.log Y)) + Real.log (1 + Real.log Y) := by
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (ne_of_gt hT0) (by linarith)]
    ring
  -- `log (1 + log Y) ≤ log 2 + loglog Y`
  have hstep3 : Real.log (1 + Real.log Y) ≤ Real.log 2 + Real.log (Real.log Y) := by
    have h1 : Real.log (1 + Real.log Y) ≤ Real.log (2 * Real.log Y) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hL0)] at h1
    exact h1
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hnum : 1 + Real.log (3 + Tstar Y (Real.log Y) * (1 + Real.log Y))
      ≤ 3 + 5 * Real.log (Real.log Y) + Real.log Y / (4 * Real.log (Real.log Y)) := by
    linarith
  have hC0 : (0 : ℝ) < ballSupC := ballSupC_pos
  have hmul : 4 * ballSupC * (1 + Real.log (3 + Tstar Y (Real.log Y) * (1 + Real.log Y)))
      ≤ 4 * ballSupC * (3 + 5 * Real.log (Real.log Y)
          + Real.log Y / (4 * Real.log (Real.log Y))) :=
    mul_le_mul_of_nonneg_left hnum (by positivity)
  unfold farErr
  exact div_le_div_same hmul (Real.sqrt_nonneg _)

/-- **L-4 — the gate form.**  What a consumer must check to price the localized far arm at a
target `B`: the whole numerator against `B·√(log W)`.  Stating it this way keeps the demand
in the open — no `X` large enough, no absorbed constant. -/
theorem farErr_local_of_gate {W Y B : ℝ} (hY : Real.exp (Real.exp 1) ≤ Y) (hW : 1 < W)
    (hgate : 4 * ballSupC * (3 + 5 * Real.log (Real.log Y)
        + Real.log Y / (4 * Real.log (Real.log Y))) ≤ B * Real.sqrt (Real.log W)) :
    farErr W Y (Tstar Y (Real.log Y)) ≤ B := by
  have hs : (0 : ℝ) < Real.sqrt (Real.log W) := Real.sqrt_pos.mpr (Real.log_pos hW)
  have h1 := farErr_local_le (W := W) hY
  have h2 : 4 * ballSupC * (3 + 5 * Real.log (Real.log Y)
      + Real.log Y / (4 * Real.log (Real.log Y))) / Real.sqrt (Real.log W) ≤ B := by
    rw [div_le_iff₀ hs]; exact hgate
  linarith

/-- **L-4 — THE CERTIFICATE (lower): R1 alone does NOT close.**  On the co-factor window's own
geometry — `log W ≤ log Y ≤ 2·log W`, which is `k₀ ≤ M ≤ 2k₀` after logs —

  `ballSupC·√(log W)/(1 + loglog W) ≤ farErr W Y (T*(Y, log Y))`.

The right side is what a consumer of `cofactor_Rbd_local` actually pays; the left side
DIVERGES.  So the localized far arm cannot meet `farErr ≤ (log X)^{−2θ₂₉₃}` either — the
`log Rmax` factor is smaller than ⟦V6a⟧'s by a full `√(log X)/loglog X`, and still infinite.
This is the honest half of R1: the wall moved, it did not fall.  ⟦V6b⟧'s R2 is the closure. -/
theorem farErr_local_window_ge {W Y : ℝ} (hY : Real.exp (Real.exp 1) ≤ Y)
    (hWY : Real.log W ≤ Real.log Y) (hYW : Real.log Y ≤ 2 * Real.log W) :
    ballSupC * Real.sqrt (Real.log W) / (1 + Real.log (Real.log W))
      ≤ farErr W Y (Tstar Y (Real.log Y)) := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hY1 : (1 : ℝ) ≤ Y := by
    have h : (1 : ℝ) ≤ Real.exp (Real.exp 1) := Real.one_le_exp (Real.exp_pos 1).le
    linarith
  have hLe : Real.exp 1 ≤ Real.log Y := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hY
  have hL2 : (2 : ℝ) < Real.log Y := lt_of_lt_of_le (by linarith [Real.exp_one_gt_d9]) hLe
  have hL0 : (0 : ℝ) < Real.log Y := by linarith
  have hll1 : (1 : ℝ) ≤ Real.log (Real.log Y) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hLe
  have hll0 : (0 : ℝ) < Real.log (Real.log Y) := by linarith
  -- the window forces `log W > 1`, so `loglog W > 0`
  have hΛ1 : (1 : ℝ) < Real.log W := by linarith
  have hΛ0 : (0 : ℝ) < Real.log W := by linarith
  have hlΛ0 : (0 : ℝ) < Real.log (Real.log W) := Real.log_pos hΛ1
  have hsq : (0 : ℝ) < Real.sqrt (Real.log W) := Real.sqrt_pos.mpr hΛ0
  have hsqsq : Real.sqrt (Real.log W) * Real.sqrt (Real.log W) = Real.log W :=
    Real.mul_self_sqrt hΛ0.le
  -- `loglog Y ≤ 1 + loglog W`
  have hllle : Real.log (Real.log Y) ≤ 1 + Real.log (Real.log W) := by
    have h1 : Real.log (Real.log Y) ≤ Real.log (2 * Real.log W) :=
      Real.log_le_log hL0 hYW
    rw [Real.log_mul (by norm_num) (ne_of_gt hΛ0)] at h1
    linarith [Real.log_two_lt_d9]
  -- the numerator, from below
  have hT4 : Real.log Y ^ 4 ≤ Tstar Y (Real.log Y) := Tstar_ge hY1 (by linarith)
  have hT16 : (16 : ℝ) ≤ Real.log Y ^ 4 := by
    have h : (2 : ℝ) ^ 4 ≤ Real.log Y ^ 4 := pow_le_pow_left₀ (by norm_num) hL2.le 4
    norm_num at h; linarith
  have hT0 : (0 : ℝ) < Tstar Y (Real.log Y) := by linarith
  have hlogT := log_Tstar_self hY
  have hTin : Tstar Y (Real.log Y) ≤ 3 + Tstar Y (Real.log Y) * (1 + Real.log Y) := by
    nlinarith
  have hlogmono : Real.log (Tstar Y (Real.log Y))
      ≤ Real.log (3 + Tstar Y (Real.log Y) * (1 + Real.log Y)) :=
    Real.log_le_log hT0 hTin
  have hNge : Real.log Y / (4 * Real.log (Real.log Y))
      ≤ 1 + Real.log (3 + Tstar Y (Real.log Y) * (1 + Real.log Y)) := by
    have h4 : (0 : ℝ) ≤ 4 * Real.log (Real.log Y) := by linarith
    linarith
  have hN0 : (0 : ℝ) ≤ 1 + Real.log (3 + Tstar Y (Real.log Y) * (1 + Real.log Y)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 + Tstar Y (Real.log Y) * (1 + Real.log Y) by
      nlinarith)
    linarith
  -- clear the division in `hNge`
  have hLmul : Real.log Y
      ≤ (1 + Real.log (3 + Tstar Y (Real.log Y) * (1 + Real.log Y)))
        * (4 * Real.log (Real.log Y)) :=
    (div_le_iff₀ (by linarith)).mp hNge
  have hΛmul : Real.log W
      ≤ 4 * (1 + Real.log (Real.log W))
        * (1 + Real.log (3 + Tstar Y (Real.log Y) * (1 + Real.log Y))) := by
    nlinarith
  have hC0 : (0 : ℝ) < ballSupC := ballSupC_pos
  unfold farErr
  rw [div_le_div_iff₀ (by linarith) hsq]
  nlinarith [mul_nonneg hC0.le hN0]

end Salt.MR
