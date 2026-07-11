/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.LS.CharLS
import Salt.LS.BDHPrep
import Salt.LS.Conductor
import Salt.LS.PhiSum

/-!
# L8.4 — Barban–Davenport–Halberstam (pure large-sieve Barban form)

Design: `docs/blueprints/largesieve.md`, node L8.4 (RE-FROZEN, Fable 2026-07-11).
The honest, Siegel–Walfisz-free Barban bound:

```
∑_{q ≤ Q} ∑_{a reduced} ‖ψ(x;q,a) − ψ(x,χ₀)/φ(q)‖² ≤ C·(Q·x + x²)·(log x)².
```

Assembly (see the node card):
1. `variance_eq` per modulus turns the residue variance into the non-principal
   character energy `(1/φ(q))·∑_{χ≠1} ‖ψ(x,χ)‖²`.
2. Conductor descent: `‖ψ(x,χ)‖² ≤ 2‖ψ(x,χ⋆)‖² + 2‖ψ(x,χ) − ψ(x,χ⋆)‖²`
   (`χ⋆ = χ.primitiveCharacter`), the second term the `Conductor` crude bound.
3. The error piece sums the small correction; the main piece regroups over
   primitive pairs `(f, χ⋆)` (the injection `χ ↦ ⟨conductor, primitiveCharacter⟩`),
   swaps the `(q,f)` sums (`PhiSum.sum_inv_totient_dvd_le'`), and closes each
   dyadic block `f ∈ (F, 2F]` with `char_LS` (`CharLS`) at level `2F`.

Everything is a finite `Finset` sum; no integrability side goals. Constants are
loose and explicit (track doctrine); the frozen numeral `6000` has ample headroom
(the verified chain lands near `5792`).
-/

open ArithmeticFunction Finset

namespace Salt.LS

/-- A uniform (Classical) `DecidableEq` for Dirichlet characters at *every* level `q`,
independent of `NeZero q`. This makes the `∑_{χ ≠ 1 mod q}` sums elaborate consistently
inside the outer `∑_{q ≤ Q}` (where `q` carries no `NeZero` instance), rather than falling
back to differently-shaped instances at the per-`q` and outer levels. -/
noncomputable local instance (priority := 5000) instDecEqDirichlet (q : ℕ) :
    DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _

/-! ## Numeric helpers -/

/-- `(log x)² ≤ 4x` for `x ≥ 1` (via `log x = 2 log √x ≤ 2√x`). -/
private lemma log_sq_le (x : ℝ) (hx : 1 ≤ x) : (Real.log x) ^ 2 ≤ 4 * x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hlogs : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs0
  have hlogx : Real.log x = 2 * Real.log (Real.sqrt x) := by
    have h := Real.log_pow (Real.sqrt x) 2
    rw [hsx] at h
    exact_mod_cast h
  have hlx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have h1 : Real.log x ≤ 2 * Real.sqrt x := by rw [hlogx]; linarith
  have hprod : (0 : ℝ) ≤ (2 * Real.sqrt x - Real.log x) * (2 * Real.sqrt x + Real.log x) :=
    mul_nonneg (by linarith) (by linarith [Real.sqrt_nonneg x])
  nlinarith [hprod, hsx]

/-- `logb 2 q ≤ 2 log x` for `1 ≤ q ≤ x`. -/
private lemma logb2_le {q x : ℕ} (hq1 : 1 ≤ q) (hqx : q ≤ x) :
    Real.logb 2 q ≤ 2 * Real.log x := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hlogq : Real.log (q : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by exact_mod_cast hq1) (by exact_mod_cast hqx)
  have hlogqnn : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have hlogxnn : 0 ≤ Real.log (x : ℝ) := le_trans hlogqnn hlogq
  rw [Real.logb, div_le_iff₀ hlog2pos]
  nlinarith [hlogq, hlogxnn, hlog2, hlogqnn,
    mul_nonneg hlogxnn (show (0 : ℝ) ≤ 2 * Real.log 2 - 1 by linarith)]

/-- `1 + log Q ≤ 3 log x` for `2 ≤ Q ≤ x`. -/
private lemma one_add_logQ_le {Q x : ℕ} (hQ : 2 ≤ Q) (hQx : Q ≤ x) :
    1 + Real.log Q ≤ 3 * Real.log x := by
  have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans hQ hQx)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlQx : Real.log (Q : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le two_pos hQ)) (by exact_mod_cast hQx)
  have hl2x : Real.log 2 ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) hx2
  linarith

/-! ## The primitive-character energy -/

open Classical in
/-- `∑_{ψ primitive mod f} ‖ψ(x, ψ)‖²` — the block quantity `char_LS` controls. -/
noncomputable def primEnergy (x f : ℕ) : ℝ :=
  ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive),
    ‖psiChi x ψ‖ ^ 2

private lemma primEnergy_nonneg (x f : ℕ) : 0 ≤ primEnergy x f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## Bridge to `char_LS`: `ψ(x,χ)` as a `range (x+1)` sum -/

/-- `ψ(x,χ) = ∑_{n < x+1} Λ(n)·χ(n)` (the `n = 0` term vanishes since `Λ 0 = 0`),
so it is the `expSum`/`char_LS` shape with `c = Λ`, `N = x+1`. -/
lemma psiChi_eq_range_sum {q : ℕ} (x : ℕ) (χ : DirichletCharacter ℂ q) :
    psiChi x χ = ∑ n ∈ Finset.range (x + 1), (vonMangoldt n : ℂ) * χ (n : ZMod q) := by
  unfold psiChi
  refine Finset.sum_subset ?_ ?_
  · intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
  · intro n hn hn'
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc] at hn'
    have hn0 : n = 0 := by omega
    subst hn0
    simp [ArithmeticFunction.map_zero]

/-- The `ℝ`-valued companion: `∑_{n < x+1} ‖Λ(n)‖² = ∑_{n ≤ x} Λ(n)²`. -/
lemma sum_sq_range_eq (x : ℕ) :
    ∑ n ∈ Finset.range (x + 1), ‖(vonMangoldt n : ℂ)‖ ^ 2
      = ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2 := by
  have hpt : ∀ n : ℕ, ‖(vonMangoldt n : ℂ)‖ ^ 2 = (vonMangoldt n) ^ 2 := by
    intro n
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  simp_rw [hpt]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
  · intro n hn hn'
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc] at hn'
    have hn0 : n = 0 := by omega
    subst hn0
    simp [ArithmeticFunction.map_zero]

open Classical in
/-- `char_LS` specialised to `c = Λ`, `N = x+1`, giving the primitive-energy budget:
`∑_{f ≤ M} (f/φf)·primEnergy x f ≤ (M² + 13(x+1))·∑ Λ²`. -/
lemma charLS_psi {x M : ℕ} (hM : 2 ≤ M) :
    ∑ f ∈ Finset.Icc 1 M, ((f : ℝ) / (f.totient : ℝ)) * primEnergy x f
      ≤ ((M : ℝ) ^ 2 + 13 * ((x : ℝ) + 1)) * ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2 := by
  have h := char_LS (N := x + 1) (Q := M) hM (fun n => (vonMangoldt n : ℂ))
  calc ∑ f ∈ Finset.Icc 1 M, ((f : ℝ) / (f.totient : ℝ)) * primEnergy x f
      = ∑ q ∈ Finset.Icc 1 M, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            ‖∑ n ∈ Finset.range (x + 1), (vonMangoldt n : ℂ) * χ (n : ZMod q)‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        unfold primEnergy
        congr 1
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [psiChi_eq_range_sum]
    _ ≤ ((M : ℝ) ^ 2 + 13 * ((x + 1 : ℕ) : ℝ)) *
          ∑ n ∈ Finset.range (x + 1), ‖(vonMangoldt n : ℂ)‖ ^ 2 := h
    _ = ((M : ℝ) ^ 2 + 13 * ((x : ℝ) + 1)) * ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2 := by
        rw [sum_sq_range_eq]; push_cast; ring

/-! ## The conductor regrouping (per modulus) -/

open Classical in
/-- The over-counting regrouping at level `q`: summing `2‖ψ(x,χ⋆)‖²` over the
non-principal `χ mod q` is bounded by summing over ALL primitive characters of the
proper divisors `f ∣ q`, `f ≠ 1`. The map `χ ↦ ⟨conductor χ, χ.primitiveCharacter⟩`
is injective (its left inverse is `changeLevel`), and every term is `≥ 0`. -/
lemma regroup {x q Q : ℕ} [NeZero q] (hqQ : q ≤ Q) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        2 * ‖psiChi x χ.primitiveCharacter‖ ^ 2
      ≤ ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), 2 * primEnergy x f := by
  classical
  set D := (Finset.Icc 2 Q).filter (· ∣ q) with hD
  set tt : (f : ℕ) → Finset (DirichletCharacter ℂ f) :=
    fun f => Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive) with htt
  set i : DirichletCharacter ℂ q → Σ f : ℕ, DirichletCharacter ℂ f :=
    fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩ with hi
  set G : (Σ f : ℕ, DirichletCharacter ℂ f) → ℝ := fun p => 2 * ‖psiChi x p.2‖ ^ 2 with hG
  set r : (Σ f : ℕ, DirichletCharacter ℂ f) → DirichletCharacter ℂ q :=
    fun p => if h : p.1 ∣ q then DirichletCharacter.changeLevel h p.2 else 1 with hr
  set T := D.sigma tt with hT
  -- left inverse of `i`
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
  -- RHS as a sigma sum
  have hRHS : ∑ p ∈ T, G p = ∑ f ∈ D, 2 * primEnergy x f := by
    rw [hT, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    simp only [hG, htt, primEnergy, Finset.mul_sum]
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          2 * ‖psiChi x χ.primitiveCharacter‖ ^ 2
      = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, G (i χ) := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        simp only [hG, hi]
    _ = ∑ p ∈ (Finset.univ.erase 1).image i, G p :=
        (Finset.sum_image hinj).symm
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
    _ = ∑ f ∈ D, 2 * primEnergy x f := hRHS

/-! ## The dyadic block sum -/

open Classical in
/-- Dyadic decomposition of `∑_{f ∈ [2,Q]} (1/φf)·primEnergy x f`. Fibring `f` by
`Nat.log 2 (f-1)` puts it into blocks `f ∈ (2ʲ, 2ʲ⁺¹]`; on each block
`1/φf ≤ (1/2ʲ)(f/φf)` and `char_LS` at level `2ʲ⁺¹` gives `(4·2ʲ + 13(x+1)/2ʲ)·∑Λ²`.
The geometric sums close it at `(8Q + 39x)·∑Λ²`. -/
lemma dyadic {x Q : ℕ} (hx : 2 ≤ x) (hQ : 2 ≤ Q) :
    ∑ f ∈ Finset.Icc 2 Q, (1 / (f.totient : ℝ)) * primEnergy x f
      ≤ (8 * (Q : ℝ) + 39 * x) * ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2 := by
  set SL2 := ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2 with hSL2def
  have hSL2nn : 0 ≤ SL2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  set J := Nat.log 2 (Q - 1) with hJdef
  have hmaps : ∀ f ∈ Finset.Icc 2 Q, Nat.log 2 (f - 1) ∈ Finset.range (J + 1) := by
    intro f hf
    rw [Finset.mem_Icc] at hf
    rw [Finset.mem_range]
    have h : Nat.log 2 (f - 1) ≤ Nat.log 2 (Q - 1) := Nat.log_mono_right (by omega)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun f => (1 / (f.totient : ℝ)) * primEnergy x f)]
  -- per-block bound
  have hfiber : ∀ j ∈ Finset.range (J + 1),
      ∑ f ∈ (Finset.Icc 2 Q).filter (fun f => Nat.log 2 (f - 1) = j),
          (1 / (f.totient : ℝ)) * primEnergy x f
        ≤ (1 / (2 : ℝ) ^ j) * (((2 : ℝ) ^ (j + 1)) ^ 2 + 13 * ((x : ℝ) + 1)) * SL2 := by
    intro j _
    have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have h2M : 2 ≤ 2 ^ (j + 1) := by
      have h1 : 0 < 2 ^ j := pow_pos (by norm_num) j
      rw [pow_succ]; omega
    have hle1 : ∑ f ∈ (Finset.Icc 2 Q).filter (fun f => Nat.log 2 (f - 1) = j),
          (1 / (f.totient : ℝ)) * primEnergy x f
        ≤ (1 / (2 : ℝ) ^ j) * ∑ f ∈ (Finset.Icc 2 Q).filter (fun f => Nat.log 2 (f - 1) = j),
            ((f : ℝ) / (f.totient : ℝ) * primEnergy x f) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro f hf
      rw [Finset.mem_filter, Finset.mem_Icc] at hf
      obtain ⟨⟨hf2, hfQ⟩, hflog⟩ := hf
      have hf1 : f - 1 ≠ 0 := by omega
      have hlow : 2 ^ j ≤ f - 1 := hflog ▸ Nat.pow_log_le_self 2 hf1
      have h2jf : (2 : ℝ) ^ j ≤ (f : ℝ) := by
        have : 2 ^ j ≤ f := by omega
        exact_mod_cast this
      have hφpos : (0 : ℝ) < (f.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      have hcoef : (1 : ℝ) / (f.totient : ℝ) ≤ (1 / (2 : ℝ) ^ j) * ((f : ℝ) / (f.totient : ℝ)) := by
        have hrw : (1 / (2 : ℝ) ^ j) * ((f : ℝ) / (f.totient : ℝ))
            = ((f : ℝ) / (2 : ℝ) ^ j) * (1 / (f.totient : ℝ)) := by ring
        rw [hrw]
        have hge1 : (1 : ℝ) ≤ (f : ℝ) / (2 : ℝ) ^ j := (one_le_div h2jpos).mpr h2jf
        calc (1 : ℝ) / (f.totient : ℝ) = 1 * (1 / (f.totient : ℝ)) := by ring
          _ ≤ ((f : ℝ) / (2 : ℝ) ^ j) * (1 / (f.totient : ℝ)) :=
              mul_le_mul_of_nonneg_right hge1 (by positivity)
      calc (1 / (f.totient : ℝ)) * primEnergy x f
          ≤ ((1 / (2 : ℝ) ^ j) * ((f : ℝ) / (f.totient : ℝ))) * primEnergy x f :=
            mul_le_mul_of_nonneg_right hcoef (primEnergy_nonneg x f)
        _ = (1 / (2 : ℝ) ^ j) * ((f : ℝ) / (f.totient : ℝ) * primEnergy x f) := by ring
    have hle2 : (1 / (2 : ℝ) ^ j) *
          ∑ f ∈ (Finset.Icc 2 Q).filter (fun f => Nat.log 2 (f - 1) = j),
            ((f : ℝ) / (f.totient : ℝ) * primEnergy x f)
        ≤ (1 / (2 : ℝ) ^ j) *
          ∑ f ∈ Finset.Icc 1 (2 ^ (j + 1) : ℕ), ((f : ℝ) / (f.totient : ℝ) * primEnergy x f) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro f hf
        rw [Finset.mem_filter, Finset.mem_Icc] at hf
        obtain ⟨⟨hf2, hfQ⟩, hflog⟩ := hf
        rw [Finset.mem_Icc]
        refine ⟨by omega, ?_⟩
        have hup : f - 1 < 2 ^ (j + 1) := by
          have hh := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (f - 1)
          rw [hflog] at hh
          exact hh
        omega
      · intro f _ _; exact mul_nonneg (by positivity) (primEnergy_nonneg x f)
    have hle3 : (1 / (2 : ℝ) ^ j) *
          ∑ f ∈ Finset.Icc 1 (2 ^ (j + 1) : ℕ), ((f : ℝ) / (f.totient : ℝ) * primEnergy x f)
        ≤ (1 / (2 : ℝ) ^ j) * (((2 : ℝ) ^ (j + 1)) ^ 2 + 13 * ((x : ℝ) + 1)) * SL2 := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hcl := charLS_psi (x := x) (M := 2 ^ (j + 1)) h2M
      refine hcl.trans (le_of_eq ?_)
      rw [hSL2def]
      push_cast
      ring
    exact (hle1.trans hle2).trans hle3
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hSL2nn
  -- geometric sum bound
  have hA : ∀ j : ℕ, (1 / (2 : ℝ) ^ j) * ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * (2 : ℝ) ^ j := by
    intro j
    have h2j : (2 : ℝ) ^ j ≠ 0 := by positivity
    have hexp : ((2 : ℝ) ^ (j + 1)) ^ 2 = (2 : ℝ) ^ j * (2 : ℝ) ^ j * 4 := by
      rw [pow_succ]; ring
    rw [hexp]
    field_simp
  have key : ∑ j ∈ Finset.range (J + 1),
        (1 / (2 : ℝ) ^ j) * (((2 : ℝ) ^ (j + 1)) ^ 2 + 13 * ((x : ℝ) + 1))
      = 4 * (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j)
        + 13 * ((x : ℝ) + 1) * (∑ j ∈ Finset.range (J + 1), (1 / (2 : ℝ) ^ j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_add, hA j]
    ring
  rw [key]
  have hgeom1 : ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j = (2 : ℝ) ^ (J + 1) - 1 := by
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]; norm_num
  have hgeom2 : ∑ j ∈ Finset.range (J + 1), (1 / (2 : ℝ) ^ j) ≤ 2 := by
    have heq : ∑ j ∈ Finset.range (J + 1), (1 / (2 : ℝ) ^ j)
        = ∑ j ∈ Finset.range (J + 1), (1 / (2 : ℝ)) ^ j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [div_pow, one_pow]
    rw [heq]
    exact sum_geometric_two_le (J + 1)
  have h2J1 : (2 : ℝ) ^ (J + 1) ≤ 2 * (Q : ℝ) := by
    have hJle : 2 ^ J ≤ Q - 1 := Nat.pow_log_le_self 2 (by omega)
    have hn : 2 ^ (J + 1) ≤ 2 * Q := by rw [pow_succ]; omega
    exact_mod_cast hn
  have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h13nn : 0 ≤ 13 * ((x : ℝ) + 1) := by positivity
  rw [hgeom1]
  calc 4 * ((2 : ℝ) ^ (J + 1) - 1) + 13 * ((x : ℝ) + 1)
          * (∑ j ∈ Finset.range (J + 1), (1 / (2 : ℝ) ^ j))
      ≤ 4 * ((2 : ℝ) ^ (J + 1) - 1) + 13 * ((x : ℝ) + 1) * 2 := by
        have hgc : 13 * ((x : ℝ) + 1) * (∑ j ∈ Finset.range (J + 1), (1 / (2 : ℝ) ^ j))
            ≤ 13 * ((x : ℝ) + 1) * 2 := mul_le_mul_of_nonneg_left hgeom2 h13nn
        linarith
    _ ≤ 8 * (Q : ℝ) + 39 * x := by nlinarith [h2J1, hx2]

/-! ## The BDH theorem -/

/-- **L8.4 — Barban–Davenport–Halberstam (pure large-sieve Barban form).**
For `2 ≤ Q ≤ x`, the sum over `q ≤ Q` of the residue-class variance of `ψ(x;q,·)`
about the mean `ψ(x,χ₀)/φ(q)` is `O((Qx + x²)(log x)²)`, with explicit constant. -/
theorem bdh {x Q : ℕ} (hx : 2 ≤ x) (hQ : 2 ≤ Q) (hQx : Q ≤ x) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
        ‖(psiAP x q a : ℂ) - psiChi x (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖ ^ 2
      ≤ 6000 * ((Q : ℝ) * x + (x : ℝ) ^ 2) * (Real.log x) ^ 2 := by
  have hx1r : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans one_le_two hx)
  have hLnn : (0 : ℝ) ≤ Real.log (x : ℝ) := Real.log_nonneg hx1r
  have hPnn : (0 : ℝ) ≤ (Q : ℝ) * x + (x : ℝ) ^ 2 := by positivity
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hQnn : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  -- Step 1: variance identity per modulus
  have hvar : ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
          ‖(psiAP x q a : ℂ) - psiChi x (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖ ^ 2
        = ∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖psiChi x χ‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [Finset.mem_Icc] at hq
    haveI : NeZero q := ⟨by omega⟩
    refine (variance_eq (q := q) x).trans ?_
    exact congrArg (fun s => (1 / (q.totient : ℝ)) * s)
      (Finset.sum_congr (by congr 1; exact Subsingleton.elim _ _) (fun _ _ => rfl))
  -- the second-moment bound and its `6xL` corollary
  have hSL2le : ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2
      ≤ (Real.log 4 + 4) * x * Real.log x := sum_vonMangoldt_sq_le x hx
  have hlog4 : Real.log 4 + 4 ≤ 6 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [h4]; linarith [Real.log_two_lt_d9]
  have hSL6 : ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2 ≤ 6 * (x : ℝ) * Real.log x := by
    refine hSL2le.trans ?_
    have hxL_nn : 0 ≤ (x : ℝ) * Real.log x := mul_nonneg hxnn hLnn
    nlinarith [hlog4, hxL_nn]
  have hL2 : (Real.log x) ^ 2 ≤ 4 * (x : ℝ) := log_sq_le (x : ℝ) hx1r
  -- Step 2: the MAIN + ERROR split
  have hsplit : ∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖psiChi x χ‖ ^ 2
      ≤ (∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
              2 * ‖psiChi x χ.primitiveCharacter‖ ^ 2)
        + (∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
              2 * ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.mem_Icc] at hq
    haveI : NeZero q := ⟨by omega⟩
    rw [← mul_add, ← Finset.sum_add_distrib]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro χ _
    have htri : ‖psiChi x χ‖
        ≤ ‖psiChi x χ.primitiveCharacter‖ + ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ := by
      have hn := norm_add_le (psiChi x χ.primitiveCharacter)
        (psiChi x χ - psiChi x χ.primitiveCharacter)
      rwa [show psiChi x χ.primitiveCharacter + (psiChi x χ - psiChi x χ.primitiveCharacter)
        = psiChi x χ from by ring] at hn
    have hstep1 : ‖psiChi x χ‖ * ‖psiChi x χ‖
        ≤ (‖psiChi x χ.primitiveCharacter‖ + ‖psiChi x χ - psiChi x χ.primitiveCharacter‖)
          * (‖psiChi x χ.primitiveCharacter‖ + ‖psiChi x χ - psiChi x χ.primitiveCharacter‖) :=
      mul_self_le_mul_self (norm_nonneg _) htri
    nlinarith [hstep1,
      sq_nonneg (‖psiChi x χ.primitiveCharacter‖ - ‖psiChi x χ - psiChi x χ.primitiveCharacter‖)]
  -- Step 3: the MAIN piece
  have hMainNum : (∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          2 * ‖psiChi x χ.primitiveCharacter‖ ^ 2)
      ≤ 5760 * ((Q : ℝ) * x + (x : ℝ) ^ 2) * (Real.log x) ^ 2 := by
    have hMbound : (∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            2 * ‖psiChi x χ.primitiveCharacter‖ ^ 2)
        ≤ 8 * (1 + Real.log Q) *
            ((8 * (Q : ℝ) + 39 * x) * ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2) := by
      calc (∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
                2 * ‖psiChi x χ.primitiveCharacter‖ ^ 2)
          ≤ ∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
              ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), 2 * primEnergy x f := by
            apply Finset.sum_le_sum
            intro q hq
            rw [Finset.mem_Icc] at hq
            haveI : NeZero q := ⟨by omega⟩
            exact mul_le_mul_of_nonneg_left (regroup hq.2) (by positivity)
        _ = ∑ q ∈ Finset.Icc 1 Q,
              ∑ f ∈ (Finset.Icc 2 Q).filter (· ∣ q), (1 / (q.totient : ℝ)) * (2 * primEnergy x f) :=
            Finset.sum_congr rfl (fun q _ => by rw [Finset.mul_sum])
        _ = ∑ f ∈ Finset.Icc 2 Q,
              ∑ q ∈ (Finset.Icc 1 Q).filter (f ∣ ·), (1 / (q.totient : ℝ)) * (2 * primEnergy x f) :=
            Finset.sum_comm' (by intro q f; simp only [Finset.mem_filter]; tauto)
        _ = ∑ f ∈ Finset.Icc 2 Q,
              (∑ q ∈ (Finset.Icc 1 Q).filter (f ∣ ·), (1 / (q.totient : ℝ)))
                * (2 * primEnergy x f) :=
            Finset.sum_congr rfl (fun f _ => by rw [Finset.sum_mul])
        _ ≤ ∑ f ∈ Finset.Icc 2 Q,
              ((4 / (f.totient : ℝ)) * (1 + Real.log Q)) * (2 * primEnergy x f) := by
            apply Finset.sum_le_sum
            intro f hf
            rw [Finset.mem_Icc] at hf
            apply mul_le_mul_of_nonneg_right (sum_inv_totient_dvd_le' (by omega) (by omega))
            have := primEnergy_nonneg x f; positivity
        _ = 8 * (1 + Real.log Q)
              * ∑ f ∈ Finset.Icc 2 Q, (1 / (f.totient : ℝ)) * primEnergy x f := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun f _ => ?_)
            ring
        _ ≤ 8 * (1 + Real.log Q) *
              ((8 * (Q : ℝ) + 39 * x) * ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2) := by
            apply mul_le_mul_of_nonneg_left (dyadic hx hQ)
            have hlogQnn : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
            positivity
    refine hMbound.trans ?_
    have h1logQ : 1 + Real.log Q ≤ 3 * Real.log x := one_add_logQ_le hQ hQx
    have hc_nn : (0 : ℝ) ≤ 8 * (Q : ℝ) + 39 * x := by positivity
    have hb_nn : (0 : ℝ) ≤ 8 * (3 * Real.log x) := by
      apply mul_nonneg (by norm_num); linarith
    calc 8 * (1 + Real.log Q) *
          ((8 * (Q : ℝ) + 39 * x) * ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2)
        ≤ 8 * (3 * Real.log x) * ((8 * (Q : ℝ) + 39 * x) * (6 * (x : ℝ) * Real.log x)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left h1logQ (by norm_num)
          · exact mul_le_mul_of_nonneg_left hSL6 hc_nn
          · exact mul_nonneg hc_nn (Finset.sum_nonneg fun n _ => sq_nonneg _)
          · exact hb_nn
      _ ≤ 5760 * ((Q : ℝ) * x + (x : ℝ) ^ 2) * (Real.log x) ^ 2 := by
          nlinarith [mul_nonneg (mul_nonneg hQnn hxnn) (sq_nonneg (Real.log (x : ℝ))),
            mul_nonneg (mul_nonneg hxnn hxnn) (sq_nonneg (Real.log (x : ℝ)))]
  -- Step 4: the ERROR piece
  have hErrNum : (∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          2 * ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ ^ 2)
      ≤ 32 * ((Q : ℝ) * x + (x : ℝ) ^ 2) * (Real.log x) ^ 2 := by
    have hpq : ∀ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            2 * ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ ^ 2
        ≤ 8 * (Real.log x) ^ 4 := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      haveI : NeZero q := ⟨by omega⟩
      have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      have hcard : ((Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1).card ≤ q.totient := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
        have hcu : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
          exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
        omega
      have hinner : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            2 * ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ ^ 2
          ≤ (q.totient : ℝ) * (8 * (Real.log x) ^ 4) := by
        calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
                2 * ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ ^ 2
            ≤ ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
                8 * (Real.log x) ^ 4 := by
              apply Finset.sum_le_sum
              intro χ _
              have hdb : ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ ≤ 2 * (Real.log x) ^ 2 := by
                have h1 := norm_psiChi_sub_primitiveCharacter_le_logb χ (by omega : 1 ≤ x)
                have h2 : Real.logb 2 q ≤ 2 * Real.log x := logb2_le (by omega) (by omega)
                calc ‖psiChi x χ - psiChi x χ.primitiveCharacter‖
                    ≤ Real.logb 2 q * Real.log x := h1
                  _ ≤ (2 * Real.log x) * Real.log x := mul_le_mul_of_nonneg_right h2 hLnn
                  _ = 2 * (Real.log x) ^ 2 := by ring
              have hnn := norm_nonneg (psiChi x χ - psiChi x χ.primitiveCharacter)
              nlinarith [hdb, hnn, sq_nonneg (Real.log x)]
            _ = (((Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ)
                  * (8 * (Real.log x) ^ 4) := by
              rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (q.totient : ℝ) * (8 * (Real.log x) ^ 4) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast hcard
      calc (1 / (q.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
              2 * ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ ^ 2
          ≤ (1 / (q.totient : ℝ)) * ((q.totient : ℝ) * (8 * (Real.log x) ^ 4)) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = 8 * (Real.log x) ^ 4 := by field_simp
    calc (∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
              2 * ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ ^ 2)
        ≤ ∑ _q ∈ Finset.Icc 1 Q, 8 * (Real.log x) ^ 4 := Finset.sum_le_sum hpq
      _ = ((Finset.Icc 1 Q).card : ℝ) * (8 * (Real.log x) ^ 4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Q : ℝ) * (8 * (Real.log x) ^ 4) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
      _ ≤ 32 * ((Q : ℝ) * x + (x : ℝ) ^ 2) * (Real.log x) ^ 2 := by
          have hkey : 8 * (Q : ℝ) * (Real.log x) ^ 2 * (Real.log x) ^ 2
              ≤ 8 * (Q : ℝ) * (Real.log x) ^ 2 * (4 * x) :=
            mul_le_mul_of_nonneg_left hL2 (by positivity)
          nlinarith [hkey, mul_nonneg (mul_nonneg hxnn hxnn) (sq_nonneg (Real.log (x : ℝ)))]
  -- assemble
  calc ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
          ‖(psiAP x q a : ℂ) - psiChi x (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖ ^ 2
      = ∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖psiChi x χ‖ ^ 2 := hvar
    _ ≤ _ := hsplit
    _ ≤ 5760 * ((Q : ℝ) * x + (x : ℝ) ^ 2) * (Real.log x) ^ 2
          + 32 * ((Q : ℝ) * x + (x : ℝ) ^ 2) * (Real.log x) ^ 2 := add_le_add hMainNum hErrNum
    _ ≤ 6000 * ((Q : ℝ) * x + (x : ℝ) ^ 2) * (Real.log x) ^ 2 := by
        nlinarith [mul_nonneg hPnn (sq_nonneg (Real.log (x : ℝ)))]

end Salt.LS
