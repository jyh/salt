/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BV.Defs
import Salt.LS.BDHPrep
import Salt.LS.Conductor

/-!
# The BV rung, node V3.2 — AP-form SW → character form at small conductor

Design: `docs/blueprints/bv.md`, node V3.2. Converts the AP-form
`SiegelWalfisz` hypothesis into a bound on the character-twisted Chebyshev
function `psiChi` for non-principal characters at small conductor
(`f ≤ (log x)^C`), the shape the V3.1 dispersion assembly consumes at the
small-modulus end of the conductor split. Four pieces:

1. `sum_dirichletCharacter_eq_zero` — first orthogonality: a non-principal
   character sums to zero over reduced residues. Route: mathlib's
   `MulChar.sum_eq_zero_of_ne_one` gives `∑ a : ZMod q, χ a = 0` (values off
   the units vanish automatically via `MulChar.map_nonunit`); reindex
   `Finset.range q` against `ZMod q` via the `Finset.sum_nbij'` idiom used in
   `Salt/LS/CharLS.lean`, then fold the coprimality filter in exactly as
   `Salt/LS/BDHPrep.lean`'s `psiChi_eq_sum_psiAP` (`step2`) does.
2. `psiChi_le_of_siegelWalfisz` — the node's main deliverable: expand
   `psiChi x χ = ∑_a χ(a) · psiAP x f a` (`psiChi_eq_sum_psiAP`), subtract and
   re-add the mean `x/φf` inside the sum; the re-added mean term vanishes for
   free by (1) since `χ` is non-principal, leaving
   `psiChi x χ = ∑_a χ(a) · (psiAP x f a − x/φf)`. Triangle inequality +
   `‖χ(a)‖ ≤ 1` (`DirichletCharacter.norm_le_one`) + the pointwise SW bound
   per `(f, a)` (the `K` from `hSW A C hA hC`), summed over the `φ(f)` reduced
   residues (`Nat.totient_eq_card_coprime`).
3. `psiChi_le_of_siegelWalfisz_absorbed` — the `φ(f) ≤ f ≤ (log x)^C`
   absorption (`Nat.totient_le`) turning the `φ(f)` factor of (2) into the
   weakened saving exponent `A − C` via `rpow` algebra (`Real.rpow_sub`,
   `Real.rpow_pos_of_pos`); this is the `A ↦ A + C` haircut the V3 assembly
   consumes.
4. `norm_psiChi_one_sub_psiTot_le` — mean-reconciliation trivia for V3.1: the
   principal-character `psiChi` differs from the unrestricted `psiTot` only
   on the non-coprime residues, all prime powers `p^k` with `p ∣ q`; this is
   the *exact* fiber-counting argument of `Salt/LS/Conductor.lean`'s
   `norm_psiChi_sub_primitiveCharacter_le` (there comparing `χ` against its
   primitive character; here comparing the principal character `χ₀` against
   the constant `1`, i.e. against the unrestricted sum) — reuses the same
   `vonMangoldt_primePow_fiber_le` fiber lemma verbatim.
-/

open Salt.LS ArithmeticFunction

namespace Salt.BV

/-! ## 1. First orthogonality: non-principal character sums vanish -/

/-- **First orthogonality.** For a non-principal `χ : DirichletCharacter ℂ q`,
the sum of `χ(a)` over reduced residues mod `q` vanishes. Route: mathlib's
`MulChar.sum_eq_zero_of_ne_one` sums `χ` over *all* of `ZMod q` and gets `0`
(non-units already contribute `0` via `MulChar.map_nonunit`); reindex
`Finset.range q` against `ZMod q` (`Finset.sum_nbij'`, the `CharLS.lean`
idiom), then fold the coprimality filter in as in `psiChi_eq_sum_psiAP`'s
`step2`. -/
theorem sum_dirichletCharacter_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), χ (a : ZMod q) = 0 := by
  have step2 : ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), χ (a : ZMod q)
      = ∑ a ∈ Finset.range q, χ (a : ZMod q) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases hc : Nat.Coprime q a
    · simp [hc]
    · have hnu : ¬ IsUnit (a : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime]; exact fun h => hc h.symm
      simp [hc, MulChar.map_nonunit χ hnu]
  rw [step2]
  have hbij : ∑ a ∈ Finset.range q, χ (a : ZMod q) = ∑ a : ZMod q, χ a := by
    refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod q)) (fun b : ZMod q => b.val)
      ?_ ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro b _; exact Finset.mem_range.mpr (ZMod.val_lt b)
    · intro a ha; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
    · intro b _; exact ZMod.natCast_zmod_val b
    · intro a _; rfl
  rw [hbij]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-! ## 2. SW in character form: the node's main deliverable -/

/-- **SW in character form.** For non-principal `χ` mod `f ≤ (log x)^C`, the
Siegel–Walfisz hypothesis gives `‖ψ(x,χ)‖ ≤ K·φ(f)·x/(log x)^A`. Route:
`ψ(x,χ) = ∑_a χ(a)·ψ(x;f,a)` (`psiChi_eq_sum_psiAP`); subtract/re-add the
mean `x/φf` inside the sum, the re-added mean term vanishing by
`sum_dirichletCharacter_eq_zero` since `χ ≠ 1`; triangle inequality +
`‖χ(a)‖ ≤ 1` + the pointwise SW bound per `(f, a)`, summed over the `φ(f)`
reduced residues. -/
theorem psiChi_le_of_siegelWalfisz (hSW : SiegelWalfisz) {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℕ) (_ : 2 ≤ f) (χ : DirichletCharacter ℂ f), χ ≠ 1 →
      ∀ x : ℕ, 2 ≤ x → ((f : ℝ) ≤ (Real.log x) ^ C) →
      ‖psiChi x χ‖ ≤ K * (f.totient : ℝ) * x / (Real.log x) ^ A := by
  obtain ⟨K, hK0, hK⟩ := hSW A C hA hC
  refine ⟨K, hK0, fun f hf2 χ hχ x hx2 hfC => ?_⟩
  haveI : NeZero f := ⟨by omega⟩
  have hf0 : 0 < f := by omega
  have hzero : ∑ a ∈ (Finset.range f).filter (Nat.Coprime f), χ (a : ZMod f) = 0 :=
    sum_dirichletCharacter_eq_zero χ hχ
  have hrewrite : psiChi x χ
      = ∑ a ∈ (Finset.range f).filter (Nat.Coprime f),
          χ (a : ZMod f) * ((psiAP x f a : ℂ) - (x : ℂ) / (f.totient : ℂ)) := by
    rw [psiChi_eq_sum_psiAP x χ]
    have hexpand : ∀ a ∈ (Finset.range f).filter (Nat.Coprime f),
        χ (a : ZMod f) * (psiAP x f a : ℂ)
          = χ (a : ZMod f) * ((psiAP x f a : ℂ) - (x : ℂ) / (f.totient : ℂ))
            + χ (a : ZMod f) * ((x : ℂ) / (f.totient : ℂ)) := fun a _ => by ring
    rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib, ← Finset.sum_mul, hzero, zero_mul,
      add_zero]
  rw [hrewrite]
  refine (norm_sum_le _ _).trans ?_
  have hbound : ∀ a ∈ (Finset.range f).filter (Nat.Coprime f),
      ‖χ (a : ZMod f) * ((psiAP x f a : ℂ) - (x : ℂ) / (f.totient : ℂ))‖
        ≤ K * (x : ℝ) / (Real.log x) ^ A := by
    intro a ha
    rw [norm_mul]
    have hcop : Nat.Coprime f a := (Finset.mem_filter.mp ha).2
    have hcop' : Nat.Coprime a f := hcop.symm
    have hχnorm : ‖χ (a : ZMod f)‖ ≤ 1 := χ.norm_le_one _
    have hSWbound : |psiAP x f a - (x : ℝ) / f.totient| ≤ K * x / (Real.log x) ^ A :=
      hK x f a hx2 hf0 hfC hcop'
    have hnorm2 : ‖(psiAP x f a : ℂ) - (x : ℂ) / (f.totient : ℂ)‖
        = |psiAP x f a - (x : ℝ) / f.totient| := by
      rw [show ((x : ℂ) / (f.totient : ℂ)) = (((x : ℝ) / f.totient : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc ‖χ (a : ZMod f)‖ * ‖(psiAP x f a : ℂ) - (x : ℂ) / (f.totient : ℂ)‖
        ≤ 1 * ‖(psiAP x f a : ℂ) - (x : ℂ) / (f.totient : ℂ)‖ :=
          mul_le_mul_of_nonneg_right hχnorm (norm_nonneg _)
      _ = ‖(psiAP x f a : ℂ) - (x : ℂ) / (f.totient : ℂ)‖ := one_mul _
      _ = |psiAP x f a - (x : ℝ) / f.totient| := hnorm2
      _ ≤ K * x / (Real.log x) ^ A := hSWbound
  calc ∑ a ∈ (Finset.range f).filter (Nat.Coprime f),
        ‖χ (a : ZMod f) * ((psiAP x f a : ℂ) - (x : ℂ) / (f.totient : ℂ))‖
      ≤ ∑ a ∈ (Finset.range f).filter (Nat.Coprime f), K * (x : ℝ) / (Real.log x) ^ A :=
        Finset.sum_le_sum hbound
    _ = ((Finset.range f).filter (Nat.Coprime f)).card * (K * (x : ℝ) / (Real.log x) ^ A) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (f.totient : ℝ) * (K * (x : ℝ) / (Real.log x) ^ A) := by
        rw [← Nat.totient_eq_card_coprime]
    _ = K * (f.totient : ℝ) * x / (Real.log x) ^ A := by ring

/-! ## 3. The φ-absorption corollary -/

/-- **The φ-absorption corollary.** Under the same hypotheses (plus
`1 ≤ log x`), the `φ(f)` factor of `psiChi_le_of_siegelWalfisz` is absorbed
into a weakened saving exponent: `‖ψ(x,χ)‖ ≤ K·x/(log x)^(A−C)`. Route:
`φ(f) ≤ f ≤ (log x)^C` (`Nat.totient_le`), then `rpow` algebra
(`Real.rpow_sub`, `Real.rpow_pos_of_pos`) folds the `(log x)^C` factor into
the exponent. This is the `A ↦ A + C` absorption the V3 assembly consumes:
to realize a saving of `A` post-absorption, invoke this lemma at `A + C`. -/
theorem psiChi_le_of_siegelWalfisz_absorbed (hSW : SiegelWalfisz) {A C : ℝ} (hA : 0 < A)
    (hC : 0 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℕ) (_ : 2 ≤ f) (χ : DirichletCharacter ℂ f), χ ≠ 1 →
      ∀ x : ℕ, 2 ≤ x → 1 ≤ Real.log x → ((f : ℝ) ≤ (Real.log x) ^ C) →
      ‖psiChi x χ‖ ≤ K * x / (Real.log x) ^ (A - C) := by
  obtain ⟨K, hK0, hK⟩ := psiChi_le_of_siegelWalfisz hSW hA hC
  refine ⟨K, hK0, fun f hf2 χ hχ x hx2 hlog1 hfC => ?_⟩
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hbase := hK f hf2 χ hχ x hx2 hfC
  have hphif : (f.totient : ℝ) ≤ (Real.log x) ^ C := by
    have h1 : (f.totient : ℝ) ≤ (f : ℝ) := by exact_mod_cast Nat.totient_le f
    linarith
  have hApos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogpos A
  have hstep : K * (f.totient : ℝ) * x / (Real.log x) ^ A
      ≤ K * (Real.log x) ^ C * x / (Real.log x) ^ A := by
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
    have h1 : K * (f.totient : ℝ) ≤ K * (Real.log x) ^ C := mul_le_mul_of_nonneg_left hphif hK0
    have hnum : K * (f.totient : ℝ) * x ≤ K * (Real.log x) ^ C * x :=
      mul_le_mul_of_nonneg_right h1 hx0
    exact div_le_div_of_nonneg_right hnum hApos.le
  have hfinal : K * (Real.log x) ^ C * x / (Real.log x) ^ A = K * x / (Real.log x) ^ (A - C) := by
    have hAne : (Real.log x) ^ A ≠ 0 := hApos.ne'
    have hCne : (Real.log x) ^ C ≠ 0 := (Real.rpow_pos_of_pos hlogpos C).ne'
    rw [show (Real.log x) ^ (A - C) = (Real.log x) ^ A / (Real.log x) ^ C from
      Real.rpow_sub hlogpos A C]
    field_simp
  calc ‖psiChi x χ‖ ≤ K * (f.totient : ℝ) * x / (Real.log x) ^ A := hbase
    _ ≤ K * (Real.log x) ^ C * x / (Real.log x) ^ A := hstep
    _ = K * x / (Real.log x) ^ (A - C) := hfinal

/-! ## 4. Mean-reconciliation trivia -/

/-- **Mean-reconciliation trivia.** The principal-character `psiChi` and the
unrestricted `psiTot` differ only on residues not coprime to `q`, all prime
powers `p^k` with `p ∣ q`; the same fiber-counting argument as
`Salt/LS/Conductor.lean`'s `norm_psiChi_sub_primitiveCharacter_le` (there
comparing `χ` to its primitive character, here comparing the principal
character `χ₀` to the constant `1`) gives the `ω(q)·log x` bound. Convenience
for V3.1's SW-at-`q=1` ↔ `psiChi x χ₀ / φq` mean reconciliation. -/
theorem norm_psiChi_one_sub_psiTot_le {q : ℕ} [NeZero q] {x : ℕ} (hx : 1 ≤ x) :
    ‖psiChi x (1 : DirichletCharacter ℂ q) - (psiTot x : ℂ)‖
      ≤ (q.primeFactors.card : ℝ) * Real.log x := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  have hdiff : psiChi x (1 : DirichletCharacter ℂ q) - (psiTot x : ℂ)
      = ∑ n ∈ Finset.Icc 1 x,
          (vonMangoldt n : ℂ) * ((1 : DirichletCharacter ℂ q) (n : ZMod q) - 1) := by
    unfold psiChi psiTot
    rw [Complex.ofReal_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [hdiff]
  refine (norm_sum_le _ _).trans ?_
  have step1 : ∑ n ∈ Finset.Icc 1 x,
        ‖(vonMangoldt n : ℂ) * ((1 : DirichletCharacter ℂ q) (n : ZMod q) - 1)‖
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n : ℕ => ¬ IsUnit (n : ZMod q)), vonMangoldt n := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun n _ => ?_)
    by_cases hu : IsUnit (n : ZMod q)
    · rw [if_neg (not_not.mpr hu), MulChar.one_apply hu, sub_self, mul_zero, norm_zero]
    · rw [if_pos hu, norm_mul]
      have hLnorm : ‖(vonMangoldt n : ℂ)‖ = vonMangoldt n := by
        rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      rw [hLnorm]
      have hcn : ‖(1 : DirichletCharacter ℂ q) (n : ZMod q) - 1‖ ≤ 1 := by
        rw [MulChar.map_nonunit _ hu, zero_sub, norm_neg, norm_one]
      calc vonMangoldt n * ‖(1 : DirichletCharacter ℂ q) (n : ZMod q) - 1‖
          ≤ vonMangoldt n * 1 := mul_le_mul_of_nonneg_left hcn vonMangoldt_nonneg
        _ = vonMangoldt n := mul_one _
  refine step1.trans ?_
  set S' := (Finset.Icc 1 x).filter (fun n : ℕ => ¬ IsUnit (n : ZMod q) ∧ IsPrimePow n) with hS'def
  have hdrop : ∑ n ∈ (Finset.Icc 1 x).filter (fun n : ℕ => ¬ IsUnit (n : ZMod q)), vonMangoldt n
      = ∑ n ∈ S', vonMangoldt n := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      rw [hS'def, Finset.mem_filter] at hn
      rw [Finset.mem_filter]
      exact ⟨hn.1, hn.2.1⟩
    · intro n hn hn'
      rw [Finset.mem_filter] at hn
      rw [hS'def, Finset.mem_filter] at hn'
      rw [vonMangoldt_eq_zero_iff]
      exact fun hpp => hn' ⟨hn.1, hn.2, hpp⟩
  rw [hdrop]
  have hmaps : ∀ n ∈ S', n.minFac ∈ q.primeFactors := by
    intro n hn
    rw [hS'def, Finset.mem_filter] at hn
    obtain ⟨_, hnu, hpp⟩ := hn
    have hp : (n.minFac).Prime := Nat.minFac_prime hpp.ne_one
    have hpdvdq : n.minFac ∣ q := by
      by_contra hnd
      have hcop_p : Nat.Coprime (n.minFac) q := (hp.coprime_iff_not_dvd).mpr hnd
      have hdecomp : (n.minFac) ^ n.factorization (n.minFac) = n := hpp.minFac_pow_factorization_eq
      have hcop_n : Nat.Coprime n q := by rw [← hdecomp]; exact hcop_p.pow_left _
      exact hnu ((ZMod.isUnit_iff_coprime n q).mpr hcop_n)
    exact (Nat.mem_primeFactors_of_ne_zero hq0).mpr ⟨hp, hpdvdq⟩
  calc ∑ n ∈ S', vonMangoldt n
      = ∑ p ∈ q.primeFactors, ∑ n ∈ S'.filter (fun n => n.minFac = p), vonMangoldt n :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log x := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        refine vonMangoldt_primePow_fiber_le (Nat.prime_of_mem_primeFactors hp) hx _ ?_
        intro n hn
        rw [Finset.mem_filter, hS'def, Finset.mem_filter, Finset.mem_Icc] at hn
        exact ⟨hn.1.1.2, hn.1.2.2, hn.2⟩
    _ = (q.primeFactors.card : ℝ) * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Salt.BV
