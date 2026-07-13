/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.GeneralBV
import Salt.LS.Conductor
import Salt.LS.PhiSum

/-!
# C3c′ — the bilinear dyadic conductor descent (discharge of `hLargeDisc`)

Design: `docs/blueprints/chen.md`, the C3c row / the `hLargeDisc` slot exposed by
`Salt.Chen.general_BV_weak` and `Salt.Chen.general_BV_closed`.  This is the last
hard analytic node of the `chen` rung: the large-conductor bilinear character
energy
```
∑_{d ∈ Dset, d > D0} (1/φd) ∑_{χ ≠ 1 mod d} ‖A_d(χ)‖·‖B_d(χ)‖
  ≤ Klarge · XY / (log XY)^A     (A_d(χ) = bilinTwist α X d χ, etc.)
```
the exact shape general-BV consumes.  It mirrors the corpus' LINEAR V3.1 conductor
descent (`Salt.BV.regroupL1_perq` + `Salt.BV.swapPhi_le` + the large-sieve energy)
bilinearly.

## The resolution of the C3c flag (the imprimitive twist is a primitive twist)

The C3c flag recorded the obstruction: the linear per-character primitive descent
(`norm_psiChi_sub_primitiveCharacter_le`, cheap for the prime-power–supported `Λ`)
does **not** mirror to a general `α`-side — the imprimitive-vs-primitive difference
`A_d(χ) − A⋆_f(ψ)` is not small for a general `‖α‖ ≤ 1` sequence.

The honest resolution landed here (`bilinTwist_coprimeRestrict_primitive`): the
imprimitive twist mod `d` induced by the primitive `ψ = χ⋆` mod `f = conductor χ`
is **exactly** the primitive twist of the *coprime-restricted* coefficient
`α_d(m) = α(m)·[gcd(m,d)=1]`, which still has `‖α_d‖ ≤ 1`.  There is **no error at
the fold** — the difficulty is only that `α_d` depends on `d` (not just `f`), so the
shell cannot be applied after the conductor regroup with a fixed coefficient.

## What this file lands (sorry-free)

1. **The fold** (`coprimeRestrict`, `norm_coprimeRestrict_le`,
   `bilinTwist_coprimeRestrict_primitive`) — the resolution above.  FULL.

2. **The conductor regroup + φ-swap** (`bilinPrimEnergy`, `regroup_bilin`,
   `swapPhi_generic`) — bilinear ports of `regroupL1_perq`/`swapPhi_le`: the
   non-principal character energy mod `d` is bounded by the primitive-conductor
   block energy over `f ∣ d`, and the `∑_q (1/φq)∑_{f∣q}` sum swaps to
   `4(1+log Q)·∑_f (1/φf)`.  FULL.

3. **The per-`d` large-sieve consumption** (`perd_energy_le`) — a genuine
   consumption of the corpus' bilinear shell `Salt.Chen.bilinTwist_energy_le`
   (`⇐ Salt.BV.bilinear_LS_shell`): fold each imprimitive character to a primitive
   twist of `α_d`, regroup, lift the `(1/φf)`↦`(f/φf)` weight, and consume the
   shell at `Q = d`.  FULL.  (Aggregate-lossy — the per-`d` `(q/φq)`↔`(1/φd)`
   weight gap the flag flagged; the tight route is the dyadic-in-conductor
   `hMainEnergy` below.)

4. **The discharge** (`bilinear_hLargeDisc`) — the `hLargeDisc` slot.  Per `χ`
   (`prod_split_le`) `‖A_d‖‖B_d‖ ≤ ‖A⋆‖‖B⋆‖ + err` (full-`α` primitive main +
   `α`-side error); the main term is regrouped (`regroup_bilin`) and swapped
   (`swapPhi_generic`) onto the `(1/φf)`-weighted primitive block energy.  The
   result is the `hLargeDisc` bound reduced to two named analytic cores:
   `hMainEnergy` (the dyadic-in-conductor shell arithmetic on the FULL-`α`
   primitive block energy — where the shell now applies with a *fixed* coefficient)
   and `hErrSum` (the summed `α`-side coprimality `L¹` error).

## FLAG (Iron Rule 1 / STOP-AND-FLAG) — PB-floor (A)

`bilinear_hLargeDisc` still takes `hMainEnergy` and `hErrSum` as **named
hypotheses** (the two dyadic-glue inputs of the PB-floor).  Both are satisfiable
under the operating scale `D ≤ √(XY)/(log XY)^{10}`, `D0 = (log XY)^{C0}` (the
classical bilinear-BV endgame: `hMainEnergy` via the per-block shell
`perd_energy_le`-style consumption summed dyadically in `f`, geometric in the block
scale `F`; `hErrSum` via the Barban–Davenport–Halberstam Möbius treatment of the
coprimality restriction, whose `L¹`-over-`d` total is acceptable even though it
fails per character).  Their standalone proofs (the dyadic geometric sum and the
BDH error arithmetic) are the remaining analytic core, recorded in
`docs/blueprints/flags.md` (node C3c′).

Only `[propext, Classical.choice, Quot.sound]` are used.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## 1. The fold — the imprimitive twist is a primitive twist of `α_d` -/

open Classical in
/-- The coprime-restricted coefficient `α_d(m) = α(m)·[gcd(m,d)=1]` (detected by
`IsUnit (m : ZMod d)`).  Its twist by a primitive `ψ mod f` (`f ∣ d`) recovers the
imprimitive twist of `α` mod `d`. -/
noncomputable def coprimeRestrict (α : ℕ → ℂ) (d : ℕ) (m : ℕ) : ℂ :=
  if IsUnit ((m : ℕ) : ZMod d) then α m else 0

/-- The coprime restriction preserves any coefficient bound (`‖α_d‖ ≤ C`). -/
lemma norm_coprimeRestrict_le (α : ℕ → ℂ) (d : ℕ) {C : ℝ} (hα : ∀ m, ‖α m‖ ≤ C) (hC : 0 ≤ C)
    (m : ℕ) : ‖coprimeRestrict α d m‖ ≤ C := by
  unfold coprimeRestrict
  by_cases h : IsUnit ((m : ℕ) : ZMod d)
  · rw [if_pos h]; exact hα m
  · rw [if_neg h, norm_zero]; exact hC

/-- **The fold (resolution of the C3c flag).**  The imprimitive twist of `α` mod `d`
by `χ` equals the *primitive* twist of the coprime-restricted coefficient
`α_d = coprimeRestrict α d` by `χ⋆ = χ.primitiveCharacter` at the conductor
`f = χ.conductor`.  Off the units mod `d` both `χ` and `α_d` vanish; on the units
`χ⋆(m) = χ(m)` (`primitiveCharacter_apply_of_isUnit`).  **No error is created.** -/
lemma bilinTwist_coprimeRestrict_primitive {d : ℕ} [NeZero d] (α : ℕ → ℂ) (X : ℕ)
    (χ : DirichletCharacter ℂ d) :
    bilinTwist α X d χ
      = bilinTwist (coprimeRestrict α d) X χ.conductor χ.primitiveCharacter := by
  unfold bilinTwist coprimeRestrict
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases hu : IsUnit ((m : ℕ) : ZMod d)
  · rw [if_pos hu, Salt.LS.primitiveCharacter_apply_of_isUnit χ hu]
  · rw [if_neg hu, MulChar.map_nonunit χ hu, mul_zero, zero_mul]

/-! ## 2. The conductor regroup and the φ-swap (bilinear ports) -/

open Classical in
/-- `∑_{ψ primitive mod f} ‖A(ψ)‖·‖B(ψ)‖` — the bilinear analogue of
`Salt.BV.primEnergyL1`.  The primitive-character pair energy the dyadic descent
consumes. -/
noncomputable def bilinPrimEnergy (α β : ℕ → ℂ) (X Y f : ℕ) : ℝ :=
  ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive),
    ‖bilinTwist α X f ψ‖ * ‖bilinTwist β Y f ψ‖

lemma bilinPrimEnergy_nonneg (α β : ℕ → ℂ) (X Y f : ℕ) : 0 ≤ bilinPrimEnergy α β X Y f :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

open Classical in
/-- **The conductor regroup (bilinear port of `regroupL1_perq`).**  Summing the
primitive-pair energy `‖A(χ⋆)‖·‖B(χ⋆)‖` over the non-principal characters mod `q` is
bounded by summing `bilinPrimEnergy` over the divisors `f ∣ q`, `f ∈ [2,Q]`: the map
`χ ↦ ⟨conductor χ, χ⋆⟩` is injective (left inverse `changeLevel`), every term is
`≥ 0`, and each `f`-fiber is the full primitive-character set. -/
lemma regroup_bilin {q Q : ℕ} [NeZero q] (hqQ : q ≤ Q) (α β : ℕ → ℂ) (X Y : ℕ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
          * ‖bilinTwist β Y χ.conductor χ.primitiveCharacter‖
      ≤ ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), bilinPrimEnergy α β X Y f := by
  classical
  set D := (Finset.Icc 2 Q).filter (· ∣ q) with hD
  set tt : (f : ℕ) → Finset (DirichletCharacter ℂ f) :=
    fun f => Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive) with htt
  set i : DirichletCharacter ℂ q → Σ f : ℕ, DirichletCharacter ℂ f :=
    fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩ with hi
  set G : (Σ f : ℕ, DirichletCharacter ℂ f) → ℝ :=
    fun p => ‖bilinTwist α X p.1 p.2‖ * ‖bilinTwist β Y p.1 p.2‖ with hG
  set r : (Σ f : ℕ, DirichletCharacter ℂ f) → DirichletCharacter ℂ q :=
    fun p => if h : p.1 ∣ q then DirichletCharacter.changeLevel h p.2 else 1 with hr
  set T := D.sigma tt with hT
  have hri : ∀ χ : DirichletCharacter ℂ q, r (i χ) = χ := by
    intro χ
    simp only [hr, hi]
    rw [dif_pos χ.conductor_dvd_level]
    exact DirichletCharacter.changeLevel_primitiveCharacter (χ := χ)
  have hinj : ∀ a ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
      ∀ b ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, i a = i b → a = b := by
    intro a _ b _ hab
    have h := congrArg r hab
    rwa [hri a, hri b] at h
  have hRHS : ∑ p ∈ T, G p = ∑ f ∈ D, bilinPrimEnergy α β X Y f := by
    rw [hT, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    simp only [hG, htt, bilinPrimEnergy]
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
            * ‖bilinTwist β Y χ.conductor χ.primitiveCharacter‖
      = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, G (i χ) := by
        refine Finset.sum_congr rfl (fun χ _ => ?_); simp only [hG, hi]
    _ = ∑ p ∈ (Finset.univ.erase 1).image i, G p := (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ T, G p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · rw [Finset.image_subset_iff]
          intro χ hχ
          rw [Finset.mem_erase] at hχ
          obtain ⟨hχ1, _⟩ := hχ
          rw [hT, Finset.mem_sigma]
          have hcd : χ.conductor ∣ q := χ.conductor_dvd_level
          have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
          have hc_pos : 0 < χ.conductor := by
            rcases Nat.eq_zero_or_pos χ.conductor with h0 | hp
            · exact absurd (Nat.eq_zero_of_zero_dvd (h0 ▸ hcd)) (NeZero.ne q)
            · exact hp
          have hc_ne1 : χ.conductor ≠ 1 := by
            intro h
            exact hχ1 (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
          have hc_le : χ.conductor ≤ q := Nat.le_of_dvd hqpos hcd
          simp only [hi]
          refine ⟨?_, ?_⟩
          · rw [hD, Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨by omega, le_trans hc_le hqQ⟩, hcd⟩
          · rw [htt, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, DirichletCharacter.primitiveCharacter_isPrimitive (χ := χ)⟩
        · intro p _ _; simp only [hG]; positivity
    _ = ∑ f ∈ D, bilinPrimEnergy α β X Y f := hRHS

/-- **The φ double-counting swap (bilinear port of `swapPhi_le`).**  Swap
`∑_q (1/φq) ∑_{f∈[2,Q], f∣q}` into `∑_f (∑_{q≤Q, f∣q} 1/φq)` and fold the level sum
`≤ (4/φf)(1+log Q)` (`sum_inv_totient_dvd_le'`) into the `4(1+log Q)` prefactor. -/
lemma swapPhi_generic {Q : ℕ} (hQ : 1 ≤ Q) (E : ℕ → ℝ) (hE : ∀ f, 0 ≤ E f) :
    ∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
        ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), E f
      ≤ 4 * (1 + Real.log Q) *
        ∑ f ∈ Finset.Icc 2 Q, (1 / (f.totient : ℝ)) * E f := by
  have hdist : ∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
        ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), E f
      = ∑ q ∈ Finset.Icc 1 Q, ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q),
          (1 / (q.totient : ℝ)) * E f := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.mul_sum]
  rw [hdist]
  rw [Finset.sum_comm' (t' := Finset.Icc 2 Q) (s' := fun f => (Finset.Icc 1 Q).filter (f ∣ ·))
      (by intro q f; simp only [Finset.mem_filter, Finset.mem_Icc]; tauto)]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun f hf => ?_)
  rw [Finset.mem_Icc] at hf
  have hf1 : 1 ≤ f := by omega
  have hPnn : 0 ≤ E f := hE f
  rw [← Finset.sum_mul]
  have hφsum := Salt.LS.sum_inv_totient_dvd_le' hf1 hQ
  calc (∑ q ∈ (Finset.Icc 1 Q).filter (f ∣ ·), (1 / (q.totient : ℝ))) * E f
      ≤ ((4 / (f.totient : ℝ)) * (1 + Real.log Q)) * E f :=
        mul_le_mul_of_nonneg_right hφsum hPnn
    _ = 4 * (1 + Real.log Q) * ((1 / (f.totient : ℝ)) * E f) := by ring

/-! ## 3. The per-`d` bilinear large-sieve consumption (fold + shell) -/

open Classical in
/-- **Per-`d` bilinear large-sieve consumption (fold + `bilinTwist_energy_le`).**
The non-principal character energy mod `d` is, via the fold (each imprimitive twist
is a primitive twist of the coprime-restricted—norm ≤ 1—coefficient) and the shell
`bilinTwist_energy_le` at `Q = d`, bounded by the balanced
`√(d²+13(X+1))·√(d²+13(Y+1))·√X·√Y` energy.  A genuine consumption of the corpus'
bilinear large sieve; aggregate-lossy (the `(q/φq)`↔`(1/φd)` weight the flag noted)
but the honest per-`d` engine underlying the dyadic `hMainEnergy`. -/
theorem perd_energy_le {X Y d : ℕ} (hd : 2 ≤ d) (hY : 0 < Y) (α β : ℕ → ℂ)
    (hα : ∀ m, ‖α m‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
      ≤ 2 * (1 + Real.log Y)
          * Real.sqrt ((d : ℝ) ^ 2 + 13 * ((X : ℝ) + 1))
          * Real.sqrt ((d : ℝ) ^ 2 + 13 * ((Y : ℝ) + 1))
          * Real.sqrt (X : ℝ) * Real.sqrt (Y : ℝ) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  set aα := coprimeRestrict α d with haα
  set aβ := coprimeRestrict β d with haβ
  have haαle : ∀ m, ‖aα m‖ ≤ 1 := fun m => norm_coprimeRestrict_le α d hα (by norm_num) m
  have haβle : ∀ n, ‖aβ n‖ ≤ 1 := fun n => norm_coprimeRestrict_le β d hβ (by norm_num) n
  -- fold each summand to primitive twists of the coprime-restricted coefficients
  have hfold : ∀ χ : DirichletCharacter ℂ d,
      ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
        = ‖bilinTwist aα X χ.conductor χ.primitiveCharacter‖
          * ‖bilinTwist aβ Y χ.conductor χ.primitiveCharacter‖ := by
    intro χ
    rw [bilinTwist_coprimeRestrict_primitive α X χ, bilinTwist_coprimeRestrict_primitive β Y χ]
  rw [Finset.sum_congr rfl (fun χ _ => hfold χ)]
  -- regroup by conductor (instance-bridge the `erase`), then extend to `Icc 1 d`
  refine le_trans (Eq.trans_le
      (Finset.sum_congr
        (congrArg (fun i => @Finset.erase (DirichletCharacter ℂ d) i Finset.univ 1)
          (Subsingleton.elim _ _)) (fun _ _ => rfl))
      (regroup_bilin (le_refl d) aα aβ X Y)) ?_
  have hsub : (Finset.Icc 2 d).filter (· ∣ d) ⊆ Finset.Icc 1 d := by
    intro f hf; rw [Finset.mem_filter, Finset.mem_Icc] at hf; rw [Finset.mem_Icc]; omega
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun f _ _ => bilinPrimEnergy_nonneg _ _ _ _ _)) ?_
  -- weight-lift `bilinPrimEnergy ≤ (f/φf)·∑‖A·B‖` and match the shell LHS
  refine le_trans (Finset.sum_le_sum (fun f hf => ?_))
    (bilinTwist_energy_le hd hY aα aβ haαle haβle)
  rw [Finset.mem_Icc] at hf
  haveI : NeZero f := ⟨by omega⟩
  have hφpos : (0 : ℝ) < (f.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < f)
  have hffφ : (1 : ℝ) ≤ (f : ℝ) / (f.totient : ℝ) := by
    rw [le_div_iff₀ hφpos, one_mul]; exact_mod_cast Nat.totient_le f
  have heq : bilinPrimEnergy aα aβ X Y f
      = ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive),
          ‖bilinTwist aα X f ψ * bilinTwist aβ Y f ψ‖ := by
    unfold bilinPrimEnergy
    exact Finset.sum_congr rfl (fun ψ _ => (norm_mul _ _).symm)
  rw [heq]
  exact le_mul_of_one_le_left
    (Finset.sum_nonneg (fun ψ _ => norm_nonneg _)) hffφ

/-! ## 4. The `hLargeDisc` discharge -/

/-- **Per-`χ` product error split.**  `‖A_d‖‖B_d‖ ≤ ‖A⋆‖‖B⋆‖ + err`, where `A⋆, B⋆`
are the FULL-`α`/`β` primitive twists at the conductor and
`err = ‖A_d − A⋆‖‖B_d‖ + ‖A⋆‖‖B_d − B⋆‖` (two triangle steps).  This isolates a
main term to which the shell applies with a *fixed* coefficient from the residual
`α`-side coprimality error. -/
lemma prod_split_le {d : ℕ} (α β : ℕ → ℂ) (X Y : ℕ) (χ : DirichletCharacter ℂ d) :
    ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
      ≤ ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
            * ‖bilinTwist β Y χ.conductor χ.primitiveCharacter‖
        + (‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist β Y d χ‖
            + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist β Y d χ - bilinTwist β Y χ.conductor χ.primitiveCharacter‖) := by
  set Ad := bilinTwist α X d χ
  set Bd := bilinTwist β Y d χ
  set As := bilinTwist α X χ.conductor χ.primitiveCharacter
  set Bs := bilinTwist β Y χ.conductor χ.primitiveCharacter
  have hA : ‖Ad‖ ≤ ‖As‖ + ‖Ad - As‖ := by
    have := norm_sub_norm_le Ad As; linarith
  have hB : ‖Bd‖ ≤ ‖Bs‖ + ‖Bd - Bs‖ := by
    have := norm_sub_norm_le Bd Bs; linarith
  nlinarith [norm_nonneg Ad, norm_nonneg Bd, norm_nonneg As, norm_nonneg Bs,
    norm_nonneg (Ad - As), norm_nonneg (Bd - Bs), hA, hB]

open Classical in
/-- **C3c′ — the bilinear dyadic conductor descent: the `hLargeDisc` discharge.**
The large-conductor character energy over `Dset ∩ (D0, ∞)` splits (per `χ`, via
`prod_split_le`) into the FULL-`α` primitive main term and the `α`-side coprimality
error.  The main term is regrouped by conductor (`regroup_bilin` — the fold's
resolution) and φ-swapped (`swapPhi_generic`) onto the `(1/φf)`-weighted primitive
block energy `∑_{f≤D} (1/φf)·bilinPrimEnergy`; the dyadic-in-conductor shell
arithmetic on that (with a fixed coefficient) is the named `hMainEnergy`, and the
summed `α`-side error is the named `hErrSum` (the two dyadic-glue analytic cores,
both satisfiable under `D ≤ √(XY)/(log XY)^{10}`, `D0 = (log XY)^{C0}`).

The conclusion is the exact `hLargeDisc` slot of `general_BV_weak`/`general_BV_closed`
(with `Klarge = Kmain + Kerr`). -/
theorem bilinear_hLargeDisc (α β : ℕ → ℂ) (X Y D D0 : ℕ) (Dset : Finset ℕ)
    {A Kmain Kerr : ℝ}
    (hD1 : 1 ≤ D) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hMainEnergy : 4 * (1 + Real.log D) *
        ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f
      ≤ Kmain * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A)
    (hErrSum : ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
          (1 / (d.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
              (‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
                    * ‖bilinTwist β Y d χ‖
                  + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
                    * ‖bilinTwist β Y d χ - bilinTwist β Y χ.conductor χ.primitiveCharacter‖)
        ≤ Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A) :
    ∑ d ∈ Dset.filter (fun d => ¬ d ≤ D0),
        (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
      ≤ (Kmain + Kerr) * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
  classical
  set Dset' := Dset.filter (fun d => ¬ d ≤ D0) with hDset'
  -- main and error partial sums
  set MainSum := ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
          * ‖bilinTwist β Y χ.conductor χ.primitiveCharacter‖ with hMainSum
  set ErrSum := ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
        (‖bilinTwist α X d χ - bilinTwist α X χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist β Y d χ‖
            + ‖bilinTwist α X χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist β Y d χ - bilinTwist β Y χ.conductor χ.primitiveCharacter‖)
    with hErrSumDef
  -- Step 1: S ≤ MainSum + ErrSum (per-χ split).
  have hSplit : ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
          ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
      ≤ MainSum + ErrSum := by
    rw [hMainSum, hErrSumDef, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun d _ => ?_)
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun χ _ => prod_split_le α β X Y χ)
  -- Step 2: MainSum ≤ Kmain·  (regroup + extend + φ-swap + hMainEnergy).
  have hMainLe : MainSum ≤ Kmain * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by
    have hsubset : Dset' ⊆ Finset.Icc 1 D := by
      intro d hd
      rw [hDset', Finset.mem_filter] at hd
      rw [Finset.mem_Icc]
      exact ⟨by omega, hDsetD d hd.1⟩
    calc MainSum
        ≤ ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
            ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d), bilinPrimEnergy α β X Y f := by
          rw [hMainSum]
          refine Finset.sum_le_sum (fun d hd => ?_)
          rw [hDset', Finset.mem_filter] at hd
          have hdD : d ≤ D := hDsetD d hd.1
          have hd1 : 1 ≤ d := by omega
          haveI : NeZero d := ⟨by omega⟩
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Eq.trans_le ?_ (regroup_bilin hdD α β X Y)
          exact Finset.sum_congr
            (congrArg (fun i => @Finset.erase (DirichletCharacter ℂ d) i Finset.univ 1)
              (Subsingleton.elim _ _)) (fun _ _ => rfl)
      _ ≤ ∑ d ∈ Finset.Icc 1 D, (1 / (d.totient : ℝ)) *
            ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d), bilinPrimEnergy α β X Y f := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => ?_)
          exact mul_nonneg (by positivity)
            (Finset.sum_nonneg (fun f _ => bilinPrimEnergy_nonneg _ _ _ _ _))
      _ ≤ 4 * (1 + Real.log D) *
            ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * bilinPrimEnergy α β X Y f :=
          swapPhi_generic hD1 (bilinPrimEnergy α β X Y) (bilinPrimEnergy_nonneg α β X Y)
      _ ≤ Kmain * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := hMainEnergy
  -- Step 3: combine.
  calc ∑ d ∈ Dset', (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            ‖bilinTwist α X d χ‖ * ‖bilinTwist β Y d χ‖
      ≤ MainSum + ErrSum := hSplit
    _ ≤ Kmain * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A
        + Kerr * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A :=
        add_le_add hMainLe hErrSum
    _ = (Kmain + Kerr) * ((X : ℝ) * (Y : ℝ)) / (Real.log ((X : ℝ) * (Y : ℝ))) ^ A := by ring

end Salt.Chen
