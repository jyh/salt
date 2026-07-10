/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.FrontierFinal

/-!
# Lemma 5.3 with TIGHT (linear-in-`k`) error constant — the sixth-fragility fix

The landed `lemma53`/`htail_bound` (Salt/Maynard/Lemma53.lean) carry an
*exponential* error constant `C ~ 12·k³·2^k` (the `2^k` from bounding each of
the `~k` non-deviating coordinate factors by `2`, the `12k²` from the loose
`euler_tail` tail).  That makes the item-6 regime `32·C·log R ≤ B₁·D₀`
impossible, blocking the atom `CompatFrontier`.

This file re-proves the whole contraction cascade with the TIGHT tail tool
`euler_tail_L` (at `L = 1`: `∑_{c>1,primes>D₀} ∏(p−1)⁻² ≤ 4/D₀`), giving:

* `phiSq_tail_tight` : `∑ μ²/φ² ≤ 4/D₀`   (was `12k²/D₀`)
* `phiSq_dvd_ne_tight`/`phiSq_dvd_tight` : deviating/non-deviating tails with
  constants `4/D₀` and `1 + 4/D₀` (was `12k²/D₀` and `2`)
* `htail_tight` : the multi-index tail with the CONCRETE constant
  `Ctail = 4·exp 4·rankinC·k`  — LINEAR in `k`
  (non-deviating product `∏(1 + 4/D₀) ≤ exp 4`, was `2^k`)
* `lemma53_tight` : `|yM − contraction| ≤ (lemma53Const·k)·log R/D₀`,
  `lemma53Const = rankinC·(2 + 4·exp 4)`  — LINEAR in `k`, EXPLICIT

Downstream (`lemma53_rel_tight`, `s2main_lower_rel_tight`,
`s2CompatFormM_ge_cheb_tight`, `s2CompatFormM_ge_sixteenth_tight`) thread the
explicit constant through, and the item-6 regime closes for `k` large,
discharging `CompatFrontier` and hence `BoundedGapsFromEH`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-! ## The shared Rankin constant (from `rankin_bound 1`) -/

/-- The Rankin `L = 1` constant `∑_{q<Q,sf} 1/φ(q) ≤ rankinC·log Q`, exposed as a
fixed real (not hidden in an `∃`) so the tight error constants are explicit. -/
noncomputable def rankinC : ℝ := (rankin_bound 1).choose

lemma rankinC_ge_one : 1 ≤ rankinC := (rankin_bound 1).choose_spec.1

lemma rankinC_nonneg : 0 ≤ rankinC := le_trans zero_le_one rankinC_ge_one

lemma rankinC_bound (Q : ℕ) (hQ : 2 ≤ Q) :
    ∑ q ∈ (Finset.range Q).filter Squarefree, 1 / (Nat.totient q : ℝ)
      ≤ rankinC * Real.log Q := by
  have h := (rankin_bound 1).choose_spec.2 Q hQ
  simpa [rankinC] using h

/-! ## Local re-proofs of the private helpers of `Lemma53.lean` -/

/-- `μ(n)² = 1` (real-valued) for squarefree `n` (local copy of the private
`moebius_sq_one`). -/
private theorem moebius_sq_one' {n : ℕ} (hn : Squarefree n) :
    ((μ n : ℤ) : ℝ) ^ 2 = 1 := by
  have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn
  have hc : ((μ n : ℤ) : ℝ) ^ 2 = (((μ n) ^ 2 : ℤ) : ℝ) := by push_cast; ring
  rw [hc, h]; norm_num

/-- Per-coordinate factorization (local copy of the private `g_factor_prod`). -/
private theorem g_factor_prod' {r : ℕ} (hr : Squarefree r)
    (hodd : ∀ p ∈ r.primeFactors, 3 ≤ p) :
    (gMult r : ℝ) * (r : ℝ) / (Nat.totient r : ℝ) ^ 2
      = ∏ p ∈ r.primeFactors, (1 - (((p : ℝ) - 1)⁻¹) ^ 2) := by
  have hrprod : (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  rw [gMult_cast hodd, hrprod, totient_squarefree_cast hr,
    ← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `g(ρ)·ρ/φ(ρ)² ∈ [0,1]` (local copy of the private `gr_ratio_mem`). -/
private theorem gr_ratio_mem' {ρ : ℕ} (hρ : Squarefree ρ)
    (hodd : ∀ p ∈ ρ.primeFactors, 3 ≤ p) :
    0 ≤ (gMult ρ : ℝ) * (ρ : ℝ) / (Nat.totient ρ : ℝ) ^ 2
      ∧ (gMult ρ : ℝ) * (ρ : ℝ) / (Nat.totient ρ : ℝ) ^ 2 ≤ 1 := by
  rw [g_factor_prod' hρ hodd]
  refine ⟨Finset.prod_nonneg (fun p hp => ?_),
    Finset.prod_le_one (fun p hp => ?_) (fun p hp => ?_)⟩
  · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : ((p : ℝ) - 1)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith
    nlinarith [h0, h1]
  · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : ((p : ℝ) - 1)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith
    nlinarith [h0, h1]
  · nlinarith [sq_nonneg (((p : ℝ) - 1)⁻¹)]

/-- The coordinate factorization (local copy of the private `tail_factor_le`). -/
private theorem tail_factor_le' (k R : ℕ) (j : Fin k) (r : Fin k → ℕ)
    (H : Fin k → ℕ → ℝ) (hH : ∀ i x, 0 ≤ H i x) :
    ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
        ∏ i, H i (a i)
      ≤ ∏ i, ∑ x ∈ tailCoordSet k R r j i, H i x := by
  classical
  rw [Finset.prod_univ_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haK, hguard, hdev⟩ := ha
    have hK := (mem_kSieveIndex_iff a).mp haK
    rw [Fintype.mem_piFinset]
    intro i
    simp only [tailCoordSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨kSieveIndex_coord_lt haK i, hK.1 i, ?_, hguard i, ?_⟩
    · intro p hp
      exact D₀_lt_of_prime_dvd_coord haK (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
    · intro hij; subst hij; exact hdev
  · intro a _ _
    exact Finset.prod_nonneg (fun i _ => hH i (a i))

/-! ## Tight `μ²/φ²` tail bounds via `euler_tail_L` at `L = 1` -/

/-- **Tight `μ²/φ²` tail (`euler_tail_L` at `L = 1`).** `∑ μ²(c)/φ(c)² ≤ 4/D₀`
over squarefree `c > 1` with all prime factors `> D₀ k`.  For squarefree `c`,
`μ²(c)/φ(c)² = 1^{ω(c)}·∏(p−1)⁻²`, so this is `euler_tail_L k M 1 …` verbatim
(the loose `phiSq_tail_bound`'s `12k²/D₀` was `euler_tail`'s `L = 3k²`). -/
theorem phiSq_tail_tight (k M : ℕ) (hD : 4 ≤ D₀ k) :
    ∑ c ∈ ((Finset.range M).filter
        (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p)).erase 1,
      ((μ c : ℤ) : ℝ) ^ 2 / (Nat.totient c : ℝ) ^ 2
      ≤ 4 / (D₀ k : ℝ) := by
  have hDR : 4 * (1 : ℝ) ≤ (D₀ k : ℝ) := by
    have : (4 : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hD
    linarith
  have heuler := euler_tail_L k M 1 le_rfl hDR
  rw [show (4 : ℝ) * 1 / (D₀ k : ℝ) = 4 / (D₀ k : ℝ) by ring] at heuler
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun c hc => ?_))) heuler
  rw [Finset.mem_erase, Finset.mem_filter] at hc
  obtain ⟨-, -, hcsq, -⟩ := hc
  have hrhs : (∏ p ∈ c.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2) = ((Nat.totient c : ℝ) ^ 2)⁻¹ := by
    rw [Finset.prod_pow, Finset.prod_inv_distrib, ← totient_squarefree_cast hcsq, inv_pow]
  rw [one_pow, one_mul, hrhs, moebius_sq_one' hcsq, one_div]

/-- **Tight deviating-coordinate tail.** The analog of `phiSq_dvd_ne_bound` with
the tight RHS `(1/φ(ρ)²)·(4/D₀)` (was `(1/φ(ρ)²)·(12k²/D₀)`): reindex `x = ρ·c`
(`c ≠ 1`, coprime to `ρ`) and apply `phiSq_tail_tight`. -/
theorem phiSq_dvd_ne_tight (k R : ℕ) (hD : 4 ≤ D₀ k)
    (ρ : ℕ) (_hρsq : Squarefree ρ) :
    ∑ x ∈ (Finset.range R).filter
        (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ ρ ∣ x ∧ x ≠ ρ),
      1 / (Nat.totient x : ℝ) ^ 2
      ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * (4 / (D₀ k : ℝ)) := by
  classical
  set S := (Finset.range R).filter
      (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ ρ ∣ x ∧ x ≠ ρ) with hSdef
  set T := ((Finset.range R).filter
      (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p)).erase 1 with hTdef
  have hxmem : ∀ x ∈ S, ρ ∣ x ∧ Squarefree x ∧ x < R
      ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ x ≠ ρ := by
    intro x hx
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hx
    exact ⟨hx.2.2.2.1, hx.2.1, hx.1, hx.2.2.1, hx.2.2.2.2⟩
  have hφfac : ∀ x ∈ S, (Nat.totient x : ℝ) = (Nat.totient ρ : ℝ) * (Nat.totient (x / ρ) : ℝ) := by
    intro x hx
    obtain ⟨hdvd, hxsq, _, _, _⟩ := hxmem x hx
    have hxeq : ρ * (x / ρ) = x := Nat.mul_div_cancel' hdvd
    have hcop : Nat.Coprime ρ (x / ρ) := by
      have hx' : Squarefree (ρ * (x / ρ)) := by rw [hxeq]; exact hxsq
      exact (Nat.squarefree_mul_iff.mp hx').1
    have hh := Nat.totient_mul hcop
    rw [hxeq] at hh
    rw [hh]; push_cast; ring
  have hinj : Set.InjOn (fun x => x / ρ) ↑S := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    obtain ⟨hdx, _⟩ := hxmem x hx
    obtain ⟨hdy, _⟩ := hxmem y hy
    have e1 : ρ * (x / ρ) = x := Nat.mul_div_cancel' hdx
    have e2 : ρ * (y / ρ) = y := Nat.mul_div_cancel' hdy
    simp only at hxy
    rw [← e1, ← e2, hxy]
  have himg : S.image (fun x => x / ρ) ⊆ T := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    obtain ⟨hdvd, hxsq, hxR, hxp, hxne⟩ := hxmem x hx
    have hxeq : ρ * (x / ρ) = x := Nat.mul_div_cancel' hdvd
    have hcdvd : (x / ρ) ∣ x := ⟨ρ, by rw [mul_comm]; exact hxeq.symm⟩
    rw [hTdef, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, lt_of_le_of_lt (Nat.div_le_self x ρ) hxR,
      hxsq.squarefree_of_dvd hcdvd, ?_⟩
    · intro h1
      exact hxne (by rw [← hxeq, h1, mul_one])
    · intro p hp
      exact hxp p (Nat.primeFactors_mono hcdvd hxsq.ne_zero hp)
  calc ∑ x ∈ S, 1 / (Nat.totient x : ℝ) ^ 2
      = ∑ x ∈ S, (1 / (Nat.totient ρ : ℝ) ^ 2) * (1 / (Nat.totient (x / ρ) : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [hφfac x hx, mul_pow]
        simp only [one_div, mul_inv]
    _ = (1 / (Nat.totient ρ : ℝ) ^ 2) * ∑ x ∈ S, 1 / (Nat.totient (x / ρ) : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (1 / (Nat.totient ρ : ℝ) ^ 2)
          * ∑ c ∈ S.image (fun x => x / ρ), 1 / (Nat.totient c : ℝ) ^ 2 := by
        rw [Finset.sum_image hinj]
    _ ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * ∑ c ∈ T, 1 / (Nat.totient c : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg himg (fun c _ _ => by positivity)
    _ = (1 / (Nat.totient ρ : ℝ) ^ 2) * ∑ c ∈ T, ((μ c : ℤ) : ℝ) ^ 2 / (Nat.totient c : ℝ) ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl (fun c hc => ?_)
        rw [hTdef, Finset.mem_erase, Finset.mem_filter] at hc
        rw [moebius_sq_one' hc.2.2.1]
    _ ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * (4 / (D₀ k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hTdef]
        exact phiSq_tail_tight k R hD

/-- **Tight non-deviating-coordinate tail.** Without the `x ≠ ρ` constraint, the
tail is `≤ (1/φ(ρ)²)·(1 + 4/D₀)` (the `x = ρ` term gives `1/φ(ρ)²`, the `x ≠ ρ`
tail `(4/D₀)/φ(ρ)²` by `phiSq_dvd_ne_tight`).  Was `≤ (1/φ(ρ)²)·2`. -/
theorem phiSq_dvd_tight (k R : ℕ) (hD : 4 ≤ D₀ k)
    (ρ : ℕ) (hρsq : Squarefree ρ) (hρp : ∀ p ∈ ρ.primeFactors, D₀ k < p) (hρR : ρ < R) :
    ∑ x ∈ (Finset.range R).filter
        (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ ρ ∣ x),
      1 / (Nat.totient x : ℝ) ^ 2
      ≤ (1 / (Nat.totient ρ : ℝ) ^ 2) * (1 + 4 / (D₀ k : ℝ)) := by
  classical
  set B := (Finset.range R).filter
      (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ ρ ∣ x) with hBdef
  have hρmem : ρ ∈ B := by
    rw [hBdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨hρR, hρsq, hρp, dvd_refl ρ⟩
  have hsplit : ∑ x ∈ B, 1 / (Nat.totient x : ℝ) ^ 2
      = 1 / (Nat.totient ρ : ℝ) ^ 2 + ∑ x ∈ B.erase ρ, 1 / (Nat.totient x : ℝ) ^ 2 :=
    (Finset.add_sum_erase B (fun x => 1 / (Nat.totient x : ℝ) ^ 2) hρmem).symm
  have hBerase : B.erase ρ = (Finset.range R).filter
      (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ ρ ∣ x ∧ x ≠ ρ) := by
    rw [hBdef]
    ext x
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    tauto
  have htail := phiSq_dvd_ne_tight k R hD ρ hρsq
  rw [← hBerase] at htail
  have hexp : (1 / (Nat.totient ρ : ℝ) ^ 2) * (1 + 4 / (D₀ k : ℝ))
      = 1 / (Nat.totient ρ : ℝ) ^ 2 + (1 / (Nat.totient ρ : ℝ) ^ 2) * (4 / (D₀ k : ℝ)) := by
    ring
  rw [hsplit, hexp]
  linarith [htail]

/-! ## The tight multi-index tail `htail_tight` (LINEAR constant) -/

/-- **Maynard's (5.31) multi-index tail, TIGHT constant.**  Same structure as the
landed `htail_bound`, but the error constant is the CONCRETE
`Ctail = 4·exp 4·rankinC·k` — LINEAR in `k`, not `12·k³·2^k`.  The two tight
inputs: the deviating factor is now `4/D₀` (`phiSq_dvd_ne_tight`, was `12k²/D₀`),
and the non-deviating product `∏(gMult·U) ≤ exp 4` (each factor `≤ 1 + 4/D₀` via
`phiSq_dvd_tight`, and `∏(1 + 4/D₀) ≤ exp(k·4/D₀) ≤ exp 4` for `k ≤ D₀`, was
`2^k`). -/
theorem htail_tight (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (_hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (r : Fin k → ℕ) (hrm : r m = 1) (hR : 2 ≤ R) (hrsupp : r ∈ kSieveIndex k R (W k))
    (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    |(∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
        * (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
              ((kSieveIndex k R (W k)).filter
                (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
            (y a / ∏ i, (Nat.totient (a i) : ℝ))
              * ∏ i ∈ Finset.univ.erase m,
                  (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))))|
      ≤ (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := by
  classical
  obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff r).mp hrsupp
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega)
  have hD12 : 12 ≤ D₀ k := by omega
  have hD4 : 4 ≤ D₀ k := by omega
  have hkD : k ≤ D₀ k := by nlinarith [hD]
  have hD0 : 0 < D₀ k := by omega
  have hD0R : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hD0
  have hD0ne : (D₀ k : ℝ) ≠ 0 := hD0R.ne'
  have hkD0R : (k : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hkD
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hC₁0 : (0 : ℝ) ≤ rankinC := rankinC_nonneg
  have hexp4 : (0 : ℝ) ≤ Real.exp 4 := (Real.exp_pos 4).le
  have hodd : ∀ i, ∀ p ∈ (r i).primeFactors, 3 ≤ p := by
    intro i p hp
    have := D₀_lt_of_prime_dvd_coord hrsupp (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  have hrp : ∀ i, ∀ p ∈ (r i).primeFactors, D₀ k < p := fun i p hp =>
    D₀_lt_of_prime_dvd_coord hrsupp (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  have hRankin : ∑ q ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient q : ℝ)
      ≤ rankinC * Real.log R := rankinC_bound R hR
  set H : Fin k → ℕ → ℝ := fun i x =>
    if i = m then 1 / (Nat.totient x : ℝ) else (r i : ℝ) / (Nat.totient x : ℝ) ^ 2 with hHdef
  have hHnn : ∀ i x, 0 ≤ H i x := by
    intro i x; simp only [hHdef]; split_ifs <;> positivity
  set P : ℝ := ∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ) with hPdef
  set INNER : (Fin k → ℕ) → ℝ := fun a =>
    (y a / ∏ i, (Nat.totient (a i) : ℝ))
      * ∏ i ∈ Finset.univ.erase m,
          (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))) with hINNERdef
  set FG := (kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i) with hFGdef
  set Df := (kSieveIndex k R (W k)).filter
      (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i) with hDfdef
  -- per-`a` pointwise bound `|INNER a| ≤ ∏ᵢ Hᵢ(aᵢ)`
  have hbound : ∀ a ∈ kSieveIndex k R (W k), |INNER a| ≤ ∏ i, H i (a i) := by
    intro a haK
    have hφa : ∀ i, (0 : ℝ) < (Nat.totient (a i) : ℝ) := fun i => by
      exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos haK i)
    have hΦsplit : (∏ i, (Nat.totient (a i) : ℝ))
        = (Nat.totient (a m) : ℝ) * ∏ i ∈ Finset.univ.erase m, (Nat.totient (a i) : ℝ) :=
      (Finset.mul_prod_erase Finset.univ (fun i => (Nat.totient (a i) : ℝ))
        (Finset.mem_univ m)).symm
    have hprodH : (∏ i, H i (a i))
        = (1 / (Nat.totient (a m) : ℝ))
          * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => H i (a i)) (Finset.mem_univ m)]
      congr 1
      · simp only [hHdef]; rw [if_true]
      · exact Finset.prod_congr rfl (fun i hi => by
          simp only [hHdef]; rw [if_neg (Finset.ne_of_mem_erase hi)])
    rw [hprodH]
    simp only [hINNERdef]
    rw [abs_mul, abs_div, abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hφa i).le)),
      Finset.abs_prod]
    have hstep2 : ∀ i ∈ Finset.univ.erase m,
        |((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))|
          ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ) := by
      intro i _
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ))]
      have h1 := abs_moebius_real_le_one (a i)
      have h2 : (0 : ℝ) ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ) := by positivity
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - |((μ (a i) : ℤ) : ℝ)|) h2]
    calc |y a| / (∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                |((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))|
        ≤ 1 / (∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ)) := by
          apply mul_le_mul
          · rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
            calc |y a| * (∏ i, (Nat.totient (a i) : ℝ))⁻¹
                ≤ 1 * (∏ i, (Nat.totient (a i) : ℝ))⁻¹ :=
                  mul_le_mul_of_nonneg_right (hy1 a) (by positivity)
              _ = (∏ i, (Nat.totient (a i) : ℝ))⁻¹ := one_mul _
          · exact Finset.prod_le_prod (fun i _ => abs_nonneg _) hstep2
          · exact Finset.prod_nonneg (fun i _ => abs_nonneg _)
          · positivity
      _ = (1 / (Nat.totient (a m) : ℝ))
            * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2) := by
          rw [hΦsplit, Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_pow]
          have hPFne : (∏ i ∈ Finset.univ.erase m, (Nat.totient (a i) : ℝ)) ≠ 0 :=
            (Finset.prod_pos (fun i _ => hφa i)).ne'
          have hφamne : (Nat.totient (a m) : ℝ) ≠ 0 := (hφa m).ne'
          field_simp
  -- per-`j` product bound (all `R`-free except the single `log R`)
  have hjbound : ∀ j ∈ Finset.univ.erase m,
      |P| * ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
              ∏ i, H i (a i)
        ≤ rankinC * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4 := by
    intro j hj
    have hfact := tail_factor_le' k R j r H hHnn
    set U : Fin k → ℝ := fun i =>
      (r i : ℝ) * (if i = j then (1 / (Nat.totient (r i) : ℝ) ^ 2) * (4 / (D₀ k : ℝ))
        else (1 / (Nat.totient (r i) : ℝ) ^ 2) * (1 + 4 / (D₀ k : ℝ))) with hUdef
    -- factor bound per coordinate `i ≠ m`
    have hUbound : ∀ i ∈ Finset.univ.erase m, (∑ x ∈ tailCoordSet k R r j i, H i x) ≤ U i := by
      intro i hi
      have him : i ≠ m := Finset.ne_of_mem_erase hi
      have hHi : ∀ x, H i x = (r i : ℝ) / (Nat.totient x : ℝ) ^ 2 := by
        intro x; simp only [hHdef]; rw [if_neg him]
      rw [Finset.sum_congr rfl (fun x _ => hHi x)]
      rw [show (∑ x ∈ tailCoordSet k R r j i, (r i : ℝ) / (Nat.totient x : ℝ) ^ 2)
            = (r i : ℝ) * ∑ x ∈ tailCoordSet k R r j i, 1 / (Nat.totient x : ℝ) ^ 2 from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by rw [mul_one_div])]
      simp only [hUdef]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      by_cases hij : i = j
      · rw [if_pos hij]
        have hset : tailCoordSet k R r j i = (Finset.range R).filter
            (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ r i ∣ x ∧ x ≠ r i) := by
          simp only [tailCoordSet]; apply Finset.filter_congr; intro x _; simp [hij]
        rw [hset]
        exact phiSq_dvd_ne_tight k R hD4 (r i) (hsq i)
      · rw [if_neg hij]
        have hset : tailCoordSet k R r j i = (Finset.range R).filter
            (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ r i ∣ x) := by
          simp only [tailCoordSet]; apply Finset.filter_congr; intro x _; simp [hij]
        rw [hset]
        exact phiSq_dvd_tight k R hD4 (r i) (hsq i) (hrp i) (kSieveIndex_coord_lt hrsupp i)
    -- the `m`-coordinate factor `≤ rankinC log R`
    have hmfac : (∑ x ∈ tailCoordSet k R r j m, H m x) ≤ rankinC * Real.log R := by
      have hHm : ∀ x, H m x = 1 / (Nat.totient x : ℝ) := by
        intro x; simp only [hHdef]; rw [if_true]
      rw [Finset.sum_congr rfl (fun x _ => hHm x)]
      refine le_trans
        (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => by positivity)) hRankin
      intro x hx
      simp only [tailCoordSet, Finset.mem_filter, Finset.mem_range] at hx
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hx.1, hx.2.1⟩
    -- `|P| ≤ ∏_{i≠m} g(rᵢ)`
    have hPabs : |P| ≤ ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ) := by
      rw [hPdef]
      calc |∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)|
          = ∏ i, |((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)| := Finset.abs_prod _ _
        _ ≤ ∏ i, (gMult (r i) : ℝ) := by
            refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gMult (r i) : ℝ))]
            calc |((μ (r i) : ℤ) : ℝ)| * (gMult (r i) : ℝ)
                ≤ 1 * (gMult (r i) : ℝ) := by
                  apply mul_le_mul_of_nonneg_right (abs_moebius_real_le_one _) (by positivity)
              _ = (gMult (r i) : ℝ) := one_mul _
        _ = ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ) := by
            rw [← Finset.mul_prod_erase Finset.univ (fun i => (gMult (r i) : ℝ))
              (Finset.mem_univ m), hrm]
            simp [gMult, Nat.primeFactors_one]
    -- combine per-coordinate factors
    have hprodU : (∏ i, ∑ x ∈ tailCoordSet k R r j i, H i x)
        ≤ (∑ x ∈ tailCoordSet k R r j m, H m x) * ∏ i ∈ Finset.univ.erase m, U i := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ x ∈ tailCoordSet k R r j i, H i x)
        (Finset.mem_univ m)]
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun x _ => hHnn m x))
      exact Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun x _ => hHnn i x)) hUbound
    -- `(g·U) j ≤ 4/D₀`
    have hjfac : (gMult (r j) : ℝ) * U j ≤ 4 / (D₀ k : ℝ) := by
      simp only [hUdef]; rw [if_true]
      rw [show (gMult (r j) : ℝ) * ((r j : ℝ)
              * ((1 / (Nat.totient (r j) : ℝ) ^ 2) * (4 / (D₀ k : ℝ))))
            = ((gMult (r j) : ℝ) * (r j : ℝ) / (Nat.totient (r j) : ℝ) ^ 2)
              * (4 / (D₀ k : ℝ)) from by ring]
      calc ((gMult (r j) : ℝ) * (r j : ℝ) / (Nat.totient (r j) : ℝ) ^ 2)
              * (4 / (D₀ k : ℝ))
          ≤ 1 * (4 / (D₀ k : ℝ)) :=
            mul_le_mul_of_nonneg_right (gr_ratio_mem' (hsq j) (hodd j)).2 (by positivity)
        _ = 4 / (D₀ k : ℝ) := one_mul _
    -- the rest of the coordinates `≤ exp 4`
    have hrestfac : ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i)
        ≤ Real.exp 4 := by
      have hcard : ((Finset.univ.erase m).erase j).card ≤ k := by
        calc ((Finset.univ.erase m).erase j).card
            ≤ (Finset.univ : Finset (Fin k)).card :=
              Finset.card_le_card ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
          _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      have hfac_le : (1 : ℝ) + 4 / (D₀ k : ℝ) ≤ Real.exp (4 / (D₀ k : ℝ)) := by
        have h := Real.add_one_le_exp (4 / (D₀ k : ℝ)); linarith
      have hcard_le : (((Finset.univ.erase m).erase j).card : ℝ) * (4 / (D₀ k : ℝ)) ≤ 4 := by
        have h1 : (((Finset.univ.erase m).erase j).card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcard
        calc (((Finset.univ.erase m).erase j).card : ℝ) * (4 / (D₀ k : ℝ))
            ≤ (k : ℝ) * (4 / (D₀ k : ℝ)) := by gcongr
          _ ≤ (D₀ k : ℝ) * (4 / (D₀ k : ℝ)) := by gcongr
          _ = 4 := by field_simp
      calc ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i)
          ≤ ∏ _i ∈ (Finset.univ.erase m).erase j, (1 + 4 / (D₀ k : ℝ)) := by
            refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
            · have hijne : i ≠ j := Finset.ne_of_mem_erase hi
              simp only [hUdef]; rw [if_neg hijne]; positivity
            · have hijne : i ≠ j := Finset.ne_of_mem_erase hi
              simp only [hUdef]; rw [if_neg hijne]
              rw [show (gMult (r i) : ℝ) * ((r i : ℝ)
                    * ((1 / (Nat.totient (r i) : ℝ) ^ 2) * (1 + 4 / (D₀ k : ℝ))))
                    = ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2)
                      * (1 + 4 / (D₀ k : ℝ)) from by ring]
              have hge := (gr_ratio_mem' (hsq i) (hodd i)).2
              nlinarith [hge, (by positivity : (0:ℝ) ≤ 1 + 4 / (D₀ k : ℝ))]
        _ = (1 + 4 / (D₀ k : ℝ)) ^ ((Finset.univ.erase m).erase j).card := by
            rw [Finset.prod_const]
        _ ≤ (Real.exp (4 / (D₀ k : ℝ))) ^ ((Finset.univ.erase m).erase j).card :=
            pow_le_pow_left₀ (by positivity) hfac_le _
        _ = Real.exp ((((Finset.univ.erase m).erase j).card : ℝ) * (4 / (D₀ k : ℝ))) :=
            (Real.exp_nat_mul (4 / (D₀ k : ℝ)) _).symm
        _ ≤ Real.exp 4 := Real.exp_le_exp.mpr hcard_le
    have hrestnn : (0 : ℝ) ≤ ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i) := by
      refine Finset.prod_nonneg (fun i hi => ?_)
      have hijne : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [hUdef]; rw [if_neg hijne]; positivity
    -- assemble
    calc |P| * ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
              ∏ i, H i (a i)
        ≤ |P| * ∏ i, ∑ x ∈ tailCoordSet k R r j i, H i x :=
          mul_le_mul_of_nonneg_left hfact (abs_nonneg _)
      _ ≤ |P| * ((∑ x ∈ tailCoordSet k R r j m, H m x) * ∏ i ∈ Finset.univ.erase m, U i) :=
          mul_le_mul_of_nonneg_left hprodU (abs_nonneg _)
      _ = (∑ x ∈ tailCoordSet k R r j m, H m x) * (|P| * ∏ i ∈ Finset.univ.erase m, U i) := by ring
      _ ≤ (rankinC * Real.log R) * ((4 / (D₀ k : ℝ)) * Real.exp 4) := by
          refine mul_le_mul hmfac ?_ ?_ (mul_nonneg hC₁0 hlogR)
          · calc |P| * ∏ i ∈ Finset.univ.erase m, U i
                ≤ (∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
                    * ∏ i ∈ Finset.univ.erase m, U i := by
                  refine mul_le_mul_of_nonneg_right hPabs (Finset.prod_nonneg (fun i _ => ?_))
                  simp only [hUdef]; split_ifs <;> positivity
              _ = ∏ i ∈ Finset.univ.erase m, ((gMult (r i) : ℝ) * U i) :=
                  (Finset.prod_mul_distrib).symm
              _ = ((gMult (r j) : ℝ) * U j)
                    * ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i) :=
                  (Finset.mul_prod_erase (Finset.univ.erase m)
                    (fun i => (gMult (r i) : ℝ) * U i) hj).symm
              _ ≤ (4 / (D₀ k : ℝ)) * Real.exp 4 :=
                  mul_le_mul hjfac hrestfac hrestnn (by positivity)
          · exact mul_nonneg (abs_nonneg _)
              (Finset.prod_nonneg (fun i _ => by simp only [hUdef]; split_ifs <;> positivity))
      _ = rankinC * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4 := by ring
  -- main bound
  rw [abs_mul]
  calc |P| * |∑ a ∈ FG \ Df, INNER a|
      ≤ |P| * ∑ a ∈ FG \ Df, |INNER a| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ |P| * ∑ a ∈ FG \ Df, ∏ i, H i (a i) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a ha => ?_)) (abs_nonneg _)
        rw [Finset.mem_sdiff, hFGdef, Finset.mem_filter] at ha
        exact hbound a ha.1.1
    _ ≤ |P| * ∑ j ∈ Finset.univ.erase m,
          ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
            ∏ i, H i (a i) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hunion : ∀ a ∈ FG \ Df, (∏ i, H i (a i))
            ≤ ∑ j ∈ Finset.univ.erase m, (if a j ≠ r j then ∏ i, H i (a i) else 0) := by
          intro a ha
          rw [Finset.mem_sdiff] at ha
          obtain ⟨haFG, haDf⟩ := ha
          rw [hFGdef, Finset.mem_filter] at haFG
          obtain ⟨j, hjmem, hjne⟩ : ∃ j ∈ Finset.univ.erase m, a j ≠ r j := by
            by_contra hcon
            apply haDf
            rw [hDfdef, Finset.mem_filter]
            refine ⟨haFG.1, haFG.2, fun i hi => ?_⟩
            by_contra hne
            exact hcon ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hne⟩
          calc (∏ i, H i (a i)) = if a j ≠ r j then ∏ i, H i (a i) else 0 := by rw [if_pos hjne]
            _ ≤ ∑ j ∈ Finset.univ.erase m, (if a j ≠ r j then ∏ i, H i (a i) else 0) := by
                refine Finset.single_le_sum
                  (f := fun j => if a j ≠ r j then ∏ i, H i (a i) else 0) (fun j _ => ?_) hjmem
                split_ifs
                · exact Finset.prod_nonneg (fun i _ => hHnn i (a i))
                · exact le_refl 0
        calc ∑ a ∈ FG \ Df, ∏ i, H i (a i)
            ≤ ∑ a ∈ FG \ Df, ∑ j ∈ Finset.univ.erase m,
                (if a j ≠ r j then ∏ i, H i (a i) else 0) := Finset.sum_le_sum hunion
          _ = ∑ j ∈ Finset.univ.erase m, ∑ a ∈ FG \ Df,
                (if a j ≠ r j then ∏ i, H i (a i) else 0) := Finset.sum_comm
          _ ≤ ∑ j ∈ Finset.univ.erase m,
                ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
                  ∏ i, H i (a i) := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              rw [← Finset.sum_filter]
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_
                (fun a _ _ => Finset.prod_nonneg (fun i _ => hHnn i (a i)))
              intro a ha
              rw [Finset.mem_filter, Finset.mem_sdiff, hFGdef, Finset.mem_filter] at ha
              rw [Finset.mem_filter]
              exact ⟨ha.1.1.1, ha.1.1.2, ha.2⟩
    _ = ∑ j ∈ Finset.univ.erase m,
          |P| * ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
            ∏ i, H i (a i) := Finset.mul_sum _ _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase m, rankinC * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4 :=
        Finset.sum_le_sum hjbound
    _ = ((Finset.univ.erase m).card : ℝ)
          * (rankinC * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := by
        have hcardle : ((Finset.univ.erase m).card : ℝ) ≤ (k : ℝ) := by
          have : (Finset.univ.erase m).card ≤ k := by
            calc (Finset.univ.erase m).card ≤ (Finset.univ : Finset (Fin k)).card :=
                  Finset.card_le_card (Finset.erase_subset _ _)
              _ = k := by rw [Finset.card_univ, Fintype.card_fin]
          exact_mod_cast this
        have hXnn : (0 : ℝ) ≤ rankinC * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4 :=
          mul_nonneg (mul_nonneg (mul_nonneg hC₁0 hlogR) (by positivity)) hexp4
        have heq : (k : ℝ) * (rankinC * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4)
            = (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := by
          field_simp
        exact le_trans (mul_le_mul_of_nonneg_right hcardle hXnn) (le_of_eq heq)

/-! ## The tight main-sum size bound and Lemma 5.3 assembly -/

/-- Tight `|∑ y_{r;m→aₘ}/φ(aₘ)| ≤ rankinC·log R` (explicit `rankinC`, copy of
`abs_mainSum_le` with the constant exposed). -/
theorem abs_mainSum_le_tight (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (r : Fin k → ℕ) (hR : 2 ≤ R) :
    |∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
      ≤ rankinC * Real.log R := by
  classical
  have hRankin := rankinC_bound R hR
  have hterm : ∀ am ∈ Finset.range R,
      |y (Function.update r m am) / (Nat.totient am : ℝ)|
        ≤ if Squarefree am then 1 / (Nat.totient am : ℝ) else 0 := by
    intro am _
    by_cases hsf : Squarefree am
    · have hampos : 0 < am := Nat.pos_of_ne_zero hsf.ne_zero
      have hφpos : (0 : ℝ) < (Nat.totient am : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hampos
      rw [if_pos hsf, abs_div, abs_of_nonneg hφpos.le]
      gcongr
      exact hy1 _
    · rw [if_neg hsf]
      have hnotmem : Function.update r m am ∉ kSieveIndex k R (W k) := fun hmem =>
        hsf (by
          have := ((mem_kSieveIndex_iff _).mp hmem).1 m
          rwa [Function.update_self] at this)
      rw [hysupp _ hnotmem, zero_div, abs_zero]
  calc |∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
      ≤ ∑ am ∈ Finset.range R, |y (Function.update r m am) / (Nat.totient am : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ am ∈ Finset.range R, (if Squarefree am then 1 / (Nat.totient am : ℝ) else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ am ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient am : ℝ) :=
        (Finset.sum_filter _ _).symm
    _ ≤ rankinC * Real.log R := hRankin

/-- The explicit linear-in-`k` Lemma 5.3 constant `rankinC·(2 + 4·exp 4)`. -/
noncomputable def lemma53Const : ℝ := rankinC * (2 + 4 * Real.exp 4)

lemma lemma53Const_nonneg : 0 ≤ lemma53Const := by
  rw [lemma53Const]
  have := rankinC_nonneg
  have : (0:ℝ) ≤ Real.exp 4 := (Real.exp_pos 4).le
  positivity

/-- **Lemma 5.3, TIGHT explicit constant.** `|yM − contraction| ≤
(lemma53Const·k)·log R/D₀` with `lemma53Const = rankinC·(2 + 4·exp 4)` — LINEAR
in `k`, EXPLICIT (not `∃`-hidden).  Same assembly as `lemma53` (`stepB_identity`
+ `gProd_bound` + `abs_mainSum_le_tight` + `htail_tight`); the error constant
`C = 2·rankinC + Ctail ≤ 2·rankinC + 4·exp 4·rankinC·k ≤ lemma53Const·k`. -/
theorem lemma53_tight (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (r : Fin k → ℕ) (hrm : r m = 1) (hR : 2 ≤ R) (hrsupp : r ∈ kSieveIndex k R (W k))
    (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    |yM k R (W k) m y r
        - ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
      ≤ (lemma53Const * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := by
  classical
  have hSb := abs_mainSum_le_tight k R m y hy1 hysupp r hR
  have hTb := htail_tight k R m y hy1 hysupp r hrm hR hrsupp hk hD
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hD0R : (0 : ℝ) < (D₀ k : ℝ) := by
    have : 0 < D₀ k := by have : 1 ≤ k^2 := Nat.one_le_pow 2 k (by omega); omega
    exact_mod_cast this
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hC₁0 : (0 : ℝ) ≤ rankinC := rankinC_nonneg
  have hexp4 : (0 : ℝ) ≤ Real.exp 4 := (Real.exp_pos 4).le
  have hsub : (kSieveIndex k R (W k)).filter
        (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)
      ⊆ (kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.1⟩
  have hlpc : lamPhiContractM k R (W k) m y r
      = (∑ a ∈ (kSieveIndex k R (W k)).filter
            (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i),
          (y a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))))
        + (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
              ((kSieveIndex k R (W k)).filter
                (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
            (y a / ∏ i, (Nat.totient (a i) : ℝ))
              * ∏ i ∈ Finset.univ.erase m,
                  (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) := by
    rw [lamPhiContractM_collapse k R (W k) m y r hrm, ← Finset.sum_filter, add_comm]
    exact (Finset.sum_sdiff hsub).symm
  have hdiff : yM k R (W k) m y r
        - ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)
      = ((∏ i ∈ Finset.univ.erase m,
            ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2)) - 1)
          * (∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ))
        + (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
          * (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
                ((kSieveIndex k R (W k)).filter
                  (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
              (y a / ∏ i, (Nat.totient (a i) : ℝ))
                * ∏ i ∈ Finset.univ.erase m,
                    (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) := by
    rw [show yM k R (W k) m y r
          = (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
            * lamPhiContractM k R (W k) m y r from rfl,
      hlpc, mul_add, stepB_identity k R m y hysupp r hrsupp hrm]
    ring
  rw [hdiff]
  set G := ∏ i ∈ Finset.univ.erase m,
    ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2) with hGdef
  set S := ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ) with hSdef
  set PT := (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
      * (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
            ((kSieveIndex k R (W k)).filter
              (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
          (y a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) with hPTdef
  have hG : |G - 1| ≤ 2 / (D₀ k : ℝ) := gProd_bound k R hk hD r hrsupp m
  have e2 : |G - 1| * |S| ≤ (2 / (D₀ k : ℝ)) * (rankinC * Real.log R) :=
    mul_le_mul hG hSb (abs_nonneg _) (by positivity)
  -- the two error pieces, then absorb into `lemma53Const·k`
  have hfinal : (2 / (D₀ k : ℝ)) * (rankinC * Real.log R)
        + (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D₀ k : ℝ)
      ≤ (lemma53Const * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := by
    have hnum : 2 * (rankinC * Real.log R)
          + 4 * Real.exp 4 * rankinC * (k : ℝ) * Real.log R
        ≤ (lemma53Const * (k : ℝ)) * Real.log R := by
      rw [lemma53Const]
      nlinarith [hC₁0, hlogR, hexp4, hkR, mul_nonneg hC₁0 hlogR,
        mul_nonneg (mul_nonneg hexp4 hC₁0) hlogR]
    have hLHSeq : (2 / (D₀ k : ℝ)) * (rankinC * Real.log R)
          + (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D₀ k : ℝ)
        = (2 * (rankinC * Real.log R)
            + 4 * Real.exp 4 * rankinC * (k : ℝ) * Real.log R) / (D₀ k : ℝ) := by
      field_simp
    rw [hLHSeq]
    gcongr
  calc |(G - 1) * S + PT|
      ≤ |(G - 1) * S| + |PT| := abs_add_le _ _
    _ = |G - 1| * |S| + |PT| := by rw [abs_mul]
    _ ≤ (2 / (D₀ k : ℝ)) * (rankinC * Real.log R)
          + (4 * Real.exp 4 * rankinC * (k : ℝ)) * Real.log R / (D₀ k : ℝ) :=
        add_le_add e2 hTb
    _ ≤ (lemma53Const * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := hfinal

/-! ## The relative (tensor) form, TIGHT -/

/-- **Lemma 5.3, relative form, TIGHT constant.** Copy of `lemma53_rel` using
`lemma53_tight`: the contraction error carries the tensor weight `∏_{i≠m}
fTilde(vᵢ)` and the LINEAR explicit constant `lemma53Const·k`. -/
theorem lemma53_rel_tight (k R : ℕ) (T : ℝ) (m : Fin k)
    (v : Fin k → ℕ) (hvm : v m = 1) (hR : 2 ≤ R)
    (hvsupp : v ∈ kSieveIndex k R (W k)) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    |yM k R (W k) m (yTensor k R T) v
        - ∑ am ∈ Finset.range R,
            yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)|
      ≤ (∏ i ∈ Finset.univ.erase m, fTilde k R T (v i))
          * ((lemma53Const * (k : ℝ)) * Real.log R / (D₀ k : ℝ)) := by
  classical
  set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (v i) with hPdef
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
  by_cases hP0 : P = 0
  · obtain ⟨i₀, hi₀mem, hi₀0⟩ := Finset.prod_eq_zero_iff.mp hP0
    have hi₀ne : i₀ ≠ m := Finset.ne_of_mem_erase hi₀mem
    have hyM0 : yM k R (W k) m (yTensor k R T) v = 0 := by
      have hV0 : lamPhiContractM k R (W k) m (yTensor k R T) v = 0 := by
        rw [lamPhiContractM_collapse k R (W k) m (yTensor k R T) v hvm]
        apply Finset.sum_eq_zero
        intro a ha
        by_cases hcond : ∀ i, v i ∣ a i
        · rw [if_pos hcond]
          have hya : yTensor k R T a = 0 := by
            simp only [yTensor, if_pos ha]
            refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
            have hpos : 0 < a i₀ :=
              Nat.pos_of_ne_zero (((mem_kSieveIndex_iff a).mp ha).1 i₀).ne_zero
            have hle : fTilde k R T (a i₀) ≤ fTilde k R T (v i₀) :=
              fTilde_anti k R T hR (v i₀) (a i₀) hpos (hcond i₀)
            rw [hi₀0] at hle
            exact le_antisymm hle (fTilde_nonneg k R T _ hR)
          rw [hya]; ring
        · rw [if_neg hcond]
      simp only [yM, hV0, mul_zero]
    have hC0sum : (∑ am ∈ Finset.range R,
        yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro am _
      have hya : yTensor k R T (Function.update v m am) = 0 := by
        simp only [yTensor]
        split_ifs with hmem
        · refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
          rw [Function.update_of_ne hi₀ne]; exact hi₀0
        · rfl
      rw [hya, zero_div]
    rw [hyM0, hC0sum, hP0]; simp
  · have hP : 0 < P := lt_of_le_of_ne hPnn (Ne.symm hP0)
    set z : (Fin k → ℕ) → ℝ :=
      fun a => if (∀ i, v i ∣ a i) then yTensor k R T a / P else 0 with hzdef
    have hza : ∀ a, z a = if (∀ i, v i ∣ a i) then yTensor k R T a / P else 0 :=
      fun a => rfl
    have hy1 : ∀ s, |z s| ≤ 1 := by
      intro s
      rw [hza s]
      split_ifs with hcond
      · rw [abs_div, abs_of_pos hP, div_le_one hP,
          abs_of_nonneg (yTensor_nonneg k R T hR s)]
        simp only [yTensor]
        split_ifs with hmem
        · have hsq : ∀ i, Squarefree (s i) := fun i => ((mem_kSieveIndex_iff s).mp hmem).1 i
          calc ∏ i, fTilde k R T (s i)
              = fTilde k R T (s m) * ∏ i ∈ Finset.univ.erase m, fTilde k R T (s i) :=
                (Finset.mul_prod_erase Finset.univ (fun i => fTilde k R T (s i))
                  (Finset.mem_univ m)).symm
            _ ≤ 1 * ∏ i ∈ Finset.univ.erase m, fTilde k R T (v i) := by
                refine mul_le_mul (fTilde_le_one k R T hR (s m)) ?_
                  (Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)) zero_le_one
                refine Finset.prod_le_prod (fun i _ => fTilde_nonneg k R T _ hR) ?_
                intro i _
                exact fTilde_anti k R T hR (v i) (s i)
                  (Nat.pos_of_ne_zero (hsq i).ne_zero) (hcond i)
            _ = P := by rw [one_mul, hPdef]
        · exact hPnn
      · simp
    have hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → z s = 0 := by
      intro s hs
      rw [hza s]
      split_ifs with hcond
      · rw [show yTensor k R T s = 0 by simp only [yTensor]; rw [if_neg hs], zero_div]
      · rfl
    have hV : lamPhiContractM k R (W k) m z v
        = lamPhiContractM k R (W k) m (yTensor k R T) v / P := by
      rw [lamPhiContractM_collapse k R (W k) m z v hvm,
          lamPhiContractM_collapse k R (W k) m (yTensor k R T) v hvm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hcond : ∀ i, v i ∣ a i
      · rw [if_pos hcond, if_pos hcond, hza a, if_pos hcond]; ring
      · rw [if_neg hcond, if_neg hcond, zero_div]
    have hyM : yM k R (W k) m z v = yM k R (W k) m (yTensor k R T) v / P := by
      simp only [yM]; rw [hV]; ring
    have hContr : (∑ am ∈ Finset.range R, z (Function.update v m am) / (Nat.totient am : ℝ))
        = (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)) / P := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro am _
      have hcond : ∀ i, v i ∣ (Function.update v m am) i := by
        intro i
        by_cases hi : i = m
        · subst hi; rw [Function.update_self, hvm]; exact one_dvd _
        · rw [Function.update_of_ne hi]
      rw [hza (Function.update v m am), if_pos hcond]; ring
    have hbound := lemma53_tight k R m z hy1 hysupp v hvm hR hvsupp hk hD
    rw [hyM, hContr, ← sub_div, abs_div, abs_of_pos hP, div_le_iff₀ hP] at hbound
    calc |yM k R (W k) m (yTensor k R T) v
            - ∑ am ∈ Finset.range R,
                yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)|
        ≤ (lemma53Const * (k : ℝ)) * Real.log R / (D₀ k : ℝ) * P := hbound
      _ = P * ((lemma53Const * (k : ℝ)) * Real.log R / (D₀ k : ℝ)) := by ring

/-! ## The S₂ main lower bound, relative + TIGHT constant

Local copies of the constant-independent private helpers of
`Salt/Maynard/S2MainLowerRel.lean` (`sumFTilde_le_B1`, `yTensor_update_le`,
`contraction_nonneg`, `contraction_le`, `errbox_le`), then `s2main_lower_rel_tight`
with the fixed explicit constant `C = lemma53Const·k`. -/

private lemma sumFTilde_le_B1' (k R : ℕ) (T : ℝ) (hR : 2 ≤ R) :
    (∑ am ∈ Finset.range R, fTilde k R T am / (Nat.totient am : ℝ)) ≤ B1 k R (W k) T := by
  classical
  have hfe : ∀ am : ℕ, fTilde k R T am / (Nat.totient am : ℝ)
      = if am ∈ sqfCop (R0 k R T) (W k) then fWt k R am / (Nat.totient am : ℝ) else 0 := by
    intro am
    simp only [fTilde]
    split_ifs <;> simp
  have hrewrite : (∑ am ∈ Finset.range R, fTilde k R T am / (Nat.totient am : ℝ))
      = ∑ am ∈ Finset.range R,
          if am ∈ sqfCop (R0 k R T) (W k) then fWt k R am / (Nat.totient am : ℝ) else 0 :=
    Finset.sum_congr rfl (fun am _ => hfe am)
  rw [hrewrite, ← Finset.sum_filter]
  unfold B1
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro am ham
    rw [Finset.mem_filter] at ham
    exact ham.2
  · intro am ham _
    have hr : 1 ≤ am := by
      rw [sqfCop, Finset.mem_filter] at ham
      exact Nat.one_le_iff_ne_zero.mpr ham.2.1.ne_zero
    exact div_nonneg (fWt_nonneg hr hR) (Nat.cast_nonneg _)

private lemma yTensor_update_le' (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (u : Fin k → ℕ) (am : ℕ) :
    yTensor k R T (Function.update u m am)
      ≤ fTilde k R T am * ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) := by
  have hprodeq : (∏ i, fTilde k R T ((Function.update u m am) i))
      = fTilde k R T am * ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => fTilde k R T ((Function.update u m am) i)) (Finset.mem_univ m)]
    rw [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [yTensor]
  split_ifs with hmem
  · exact le_of_eq hprodeq
  · exact mul_nonneg (fTilde_nonneg k R T am hR)
      (Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR))

private lemma contraction_nonneg' (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (u : Fin k → ℕ) :
    0 ≤ ∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ) := by
  apply Finset.sum_nonneg
  intro am _
  exact div_nonneg (yTensor_nonneg k R T hR _) (Nat.cast_nonneg _)

private lemma contraction_le' (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (u : Fin k → ℕ) :
    (∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ))
      ≤ (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i)) * B1 k R (W k) T := by
  set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) with hP
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
  calc (∑ am ∈ Finset.range R,
          yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ))
      ≤ ∑ am ∈ Finset.range R, (fTilde k R T am * P) / (Nat.totient am : ℝ) := by
        apply Finset.sum_le_sum
        intro am _
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (yTensor_update_le' k R T m hR u am)
          (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = P * ∑ am ∈ Finset.range R, fTilde k R T am / (Nat.totient am : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro am _
        rw [mul_comm (fTilde k R T am) P, mul_div_assoc]
    _ ≤ P * B1 k R (W k) T :=
        mul_le_mul_of_nonneg_left (sumFTilde_le_B1' k R T hR) hPnn

private lemma errbox_le' (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (hD : 12 * k ^ 2 ≤ D₀ k) :
    (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
          * |∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≤ B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1)) := by
  classical
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k m.pos
  have hD12 : 12 ≤ D₀ k := by omega
  have hB1nn : 0 ≤ B1 k R (W k) T := B1_nonneg k R (W k) T hR
  have hclaimA : ∀ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
      (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
        * |∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
        / ∏ i, (Nat.totient (u i) : ℝ)
      ≤ B1 k R (W k) T
          * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨husupp, hum⟩ := hu
    have hsq : ∀ i, Squarefree (u i) := fun i => ((mem_kSieveIndex_iff u).mp husupp).1 i
    have hodd : ∀ i, ∀ p ∈ (u i).primeFactors, 3 ≤ p := by
      intro i p hp
      have := D₀_lt_of_prime_dvd_coord husupp (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
      omega
    have hgpos : ∀ i, 0 < (gMult (u i) : ℝ) := by
      intro i
      have hpos : 0 < gMult (u i) := by
        rw [gMult]; apply Finset.prod_pos; intro p hp; have := hodd i p hp; omega
      exact_mod_cast hpos
    have hφpos : ∀ i, 0 < (Nat.totient (u i) : ℝ) := by
      intro i; exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos husupp i)
    set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) with hPdef
    have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
    set Φ := ∏ i, (Nat.totient (u i) : ℝ) with hΦdef
    have hΦpos : 0 < Φ := Finset.prod_pos (fun i _ => hφpos i)
    have hbnn := contraction_nonneg' k R T m hR u
    have hble := contraction_le' k R T m hR u
    set b := ∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ) with hbdef
    rw [abs_of_nonneg hbnn]
    have hΦerase : Φ = ∏ i ∈ Finset.univ.erase m, (Nat.totient (u i) : ℝ) := by
      rw [hΦdef, ← Finset.mul_prod_erase Finset.univ
        (fun i => (Nat.totient (u i) : ℝ)) (Finset.mem_univ m), hum]
      simp
    have hP2Φ : P ^ 2 / Φ
        = ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
      rw [hPdef, hΦerase, ← Finset.prod_pow, ← Finset.prod_div_distrib]
    calc P * b / Φ
        = (P / Φ) * b := by ring
      _ ≤ (P / Φ) * (P * B1 k R (W k) T) :=
          mul_le_mul_of_nonneg_left hble (div_nonneg hPnn hΦpos.le)
      _ = B1 k R (W k) T * (P ^ 2 / Φ) := by ring
      _ = B1 k R (W k) T
            * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
          rw [hP2Φ]
      _ ≤ B1 k R (W k) T
            * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hB1nn
          apply Finset.prod_le_prod
          · intro i _; exact div_nonneg (sq_nonneg _) (hφpos i).le
          · intro i _
            exact div_le_div_of_nonneg_left (sq_nonneg _) (hgpos i)
              (gMult_le_totient (hsq i) (hodd i))
  calc (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
            * |∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
            / ∏ i, (Nat.totient (u i) : ℝ))
      ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          B1 k R (W k) T
            * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) :=
        Finset.sum_le_sum hclaimA
    _ = B1 k R (W k) T
          * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
              ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) := by
        rw [← Finset.mul_sum]
    _ = B1 k R (W k) T * Gdiag k R T m := by simp only [Gdiag]
    _ ≤ B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left (Gdiag_le k R T m hR hD) hB1nn

/-- **S₂ main lower bound, relative + TIGHT.** Copy of `s2main_lower_rel` with
the FIXED explicit constant `C = lemma53Const·k` (via `lemma53_rel_tight`) rather
than the `∃`-hidden loose constant.  The error term is now manifestly
`∝ k·log R/D₀·B₁·A₁^{k-1}`. -/
theorem s2main_lower_rel_tight (k R : ℕ) (m : Fin k) (T : ℝ)
    (hR : 2 ≤ R) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    Qdiag_m k R m (yTensor k R T)
      ≥ (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
           (∑ am ∈ Finset.range R,
               yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
             / ∏ i, (Nat.totient (u i) : ℝ))
        - (2 * (lemma53Const * (k : ℝ)) * Real.log R / (D₀ k : ℝ)) * (B1 k R (W k) T)
            * (2 * (A1 k R (W k) T) ^ (k - 1)) := by
  classical
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega)
  have hD12 : 12 ≤ D₀ k := by omega
  have hD0pos : 0 < D₀ k := by omega
  have hD0R : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hD0pos
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ R)
  have hlognn : 0 ≤ Real.log R := Real.log_nonneg hR1
  set C := lemma53Const * (k : ℝ) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]; exact mul_nonneg lemma53Const_nonneg (Nat.cast_nonneg k)
  have hspec : ∀ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
      |yM k R (W k) m (yTensor k R T) u
          - ∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
        ≤ (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
            * (C * Real.log R / (D₀ k : ℝ)) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    exact lemma53_rel_tight k R T m u hu.2 hR hu.1 hk hD
  set K := 2 * C * Real.log R / (D₀ k : ℝ) with hKdef
  have hmain_rel :
      (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          ((∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ)
            - K * ((∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
                    * |∑ am ∈ Finset.range R,
                        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
                    / ∏ i, (Nat.totient (u i) : ℝ))))
        ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R (W k) m (yTensor k R T) u) ^ 2 := by
    apply Finset.sum_le_sum
    intro u hu
    have hmem := hu
    rw [Finset.mem_filter] at hu
    obtain ⟨husupp, hum⟩ := hu
    obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff u).mp husupp
    have hodd : ∀ i, ∀ p ∈ (u i).primeFactors, 3 ≤ p := by
      intro i p hp
      have := D₀_lt_of_prime_dvd_coord husupp (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
      omega
    have hgcoord_pos : ∀ i, 0 < (gMult (u i) : ℝ) := by
      intro i
      have hpos : 0 < gMult (u i) := by
        rw [gMult]; apply Finset.prod_pos; intro p hp; have := hodd i p hp; omega
      exact_mod_cast hpos
    have hφcoord_pos : ∀ i, 0 < (Nat.totient (u i) : ℝ) := by
      intro i; exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos husupp i)
    set V := lamPhiContractM k R (W k) m (yTensor k R T) u with hVdef
    set G := ∏ i, (gMult (u i) : ℝ) with hGdef
    set Φ := ∏ i, (Nat.totient (u i) : ℝ) with hΦdef
    set a := yM k R (W k) m (yTensor k R T) u with hadef
    set b := ∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ) with hbdef
    set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) with hPdef
    have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
    have hGpos : 0 < G := Finset.prod_pos (fun i _ => hgcoord_pos i)
    have hΦpos : 0 < Φ := Finset.prod_pos (fun i _ => hφcoord_pos i)
    have hGleΦ : G ≤ Φ := by
      apply Finset.prod_le_prod
      · intro i _; exact (hgcoord_pos i).le
      · intro i _; exact gMult_le_totient (hsq i) (hodd i)
    have hμsq : (∏ i, ((μ (u i) : ℤ) : ℝ)) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      apply Finset.prod_eq_one
      intro i _
      have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hsq i)
      have hc : ((μ (u i) : ℤ) : ℝ) ^ 2 = (((μ (u i)) ^ 2 : ℤ) : ℝ) := by push_cast; ring
      rw [hc, h]; norm_num
    have hyMsq : a ^ 2 = G ^ 2 * V ^ 2 := by
      have hdef : a = (∏ i, ((μ (u i) : ℤ) : ℝ) * (gMult (u i) : ℝ)) * V := rfl
      rw [hdef, mul_pow, Finset.prod_mul_distrib, mul_pow, hμsq, one_mul]
    have herr : |a - b| ≤ P * (C * Real.log R / (D₀ k : ℝ)) := hspec u hmem
    have hsqb : b ^ 2 - 2 * |b| * (P * (C * Real.log R / (D₀ k : ℝ))) ≤ a ^ 2 := by
      have h1b : -(|b| * |a - b|) ≤ b * (a - b) := by
        have := neg_abs_le (b * (a - b)); rwa [abs_mul] at this
      have hstep : b ^ 2 - 2 * |b| * |a - b| ≤ a ^ 2 := by
        nlinarith [sq_nonneg (a - b), h1b]
      have h2b0 : (0 : ℝ) ≤ 2 * |b| := by positivity
      have hmul := mul_le_mul_of_nonneg_left herr h2b0
      linarith [hstep, hmul]
    have heq : b ^ 2 / Φ - K * ((P * |b|) / Φ)
        = (b ^ 2 - 2 * |b| * (P * (C * Real.log R / (D₀ k : ℝ)))) / Φ := by
      rw [sub_div, hKdef]; ring
    have hle1 : (b ^ 2 - 2 * |b| * (P * (C * Real.log R / (D₀ k : ℝ)))) / Φ ≤ a ^ 2 / Φ :=
      (div_le_div_iff_of_pos_right hΦpos).mpr hsqb
    have hle2 : a ^ 2 / Φ ≤ G * V ^ 2 := by
      rw [hyMsq, div_le_iff₀ hΦpos]
      nlinarith [mul_nonneg (mul_nonneg hGpos.le (sq_nonneg V)) (sub_nonneg.mpr hGleΦ)]
    rw [heq]; exact le_trans hle1 hle2
  have hrw' :
      (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
            / ∏ i, (Nat.totient (u i) : ℝ))
        - K * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
              * |∑ am ∈ Finset.range R,
                  yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
              / ∏ i, (Nat.totient (u i) : ℝ)
      = ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          ((∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ)
            - K * ((∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
                    * |∑ am ∈ Finset.range R,
                        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
                    / ∏ i, (Nat.totient (u i) : ℝ))) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hQ : Qdiag_m k R m (yTensor k R T)
      = ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R (W k) m (yTensor k R T) u) ^ 2 := by
    unfold Qdiag_m
    exact s2_diag_lam_restricted k R (W k) m (yTensor k R T)
  have hE := errbox_le' k R T m hR hD
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hlognn) hD0R.le
  have hcombine :
      (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
            / ∏ i, (Nat.totient (u i) : ℝ))
        - K * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
              * |∑ am ∈ Finset.range R,
                  yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
              / ∏ i, (Nat.totient (u i) : ℝ)
        ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R (W k) m (yTensor k R T) u) ^ 2 := by
    rw [hrw']; exact hmain_rel
  rw [ge_iff_le, hQ]
  have hKE :
      K * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
            * |∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
            / ∏ i, (Nat.totient (u i) : ℝ)
        ≤ K * (B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1))) :=
    mul_le_mul_of_nonneg_left hE hK0
  have hassoc : K * B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1))
      = K * (B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1))) := by ring
  rw [hassoc]
  linarith [hcombine, hKE]

/-! ## Item 6 with the tight constant -/

/-- **C4 item 6 (assembled), TIGHT.** Copy of `s2CompatFormM_ge_cheb` using
`s2main_lower_rel_tight`: the P2 relative error carries the FIXED explicit
constant `lemma53Const·k` (was `∃ C`). -/
theorem s2CompatFormM_ge_cheb_tight (k R : ℕ) (T : ℝ) (m : Fin k)
    (hR : 2 ≤ R) (hk : 1 ≤ k) (hD : 24 * k ^ 2 ≤ D₀ k)
    (hcheb : (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≥ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)) :
    s2CompatFormM k R (W k) m (yTensor k R T)
      ≥ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)
        - (4 * (lemma53Const * (k : ℝ)) * Real.log R / (D₀ k : ℝ))
            * ((B1 k R (W k) T) * (A1 k R (W k) T) ^ (k - 1))
        - 192 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
            * ((B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)) := by
  have hP2 := s2main_lower_rel_tight k R m T hR hk (by omega)
  have h6a := s2CompatFormM_ge_Qdiag k R T m hR hD
  have heq : (2 * (lemma53Const * (k : ℝ)) * Real.log R / (D₀ k : ℝ)) * (B1 k R (W k) T)
        * (2 * (A1 k R (W k) T) ^ (k - 1))
      = (4 * (lemma53Const * (k : ℝ)) * Real.log R / (D₀ k : ℝ))
          * ((B1 k R (W k) T) * (A1 k R (W k) T) ^ (k - 1)) := by ring
  rw [heq] at hP2
  linarith [h6a, hP2, hcheb]

/-- **Item 6 discharged to `(1/16)`, TIGHT.** From `s2CompatFormM_ge_cheb_tight`,
with the regime `32·(lemma53Const·k)·log R ≤ B₁·D₀` now DISCHARGED (it closes for
`k` large — the tight constant is `O(k)`, not `O(2^k)`), `k ≥ 3072`, `k³ ≤ D₀`,
the two error terms consume `1/8 + 1/16` of the main, leaving
`s2CompatFormM ≥ (1/16)B₁²A₁^{k-1}`.  Unlike the landed
`s2CompatFormM_ge_sixteenth` the regime is a *provable* input, not an
unreachable antecedent. -/
theorem s2CompatFormM_ge_sixteenth_tight (k R : ℕ) (T : ℝ) (m : Fin k)
    (hR : 2 ≤ R) (hk : 3072 ≤ k) (hD : k ^ 3 ≤ D₀ k)
    (hB1pos : 0 < B1 k R (W k) T) (hA1nn : 0 ≤ A1 k R (W k) T)
    (hcheb : (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≥ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1))
    (hreg : 32 * (lemma53Const * (k : ℝ)) * Real.log R ≤ B1 k R (W k) T * (D₀ k : ℝ)) :
    (1 / 16 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)
      ≤ s2CompatFormM k R (W k) m (yTensor k R T) := by
  have h24 : 24 * k ^ 2 ≤ D₀ k := by
    refine le_trans ?_ hD
    calc 24 * k ^ 2 ≤ k * k ^ 2 := by gcongr; omega
      _ = k ^ 3 := by ring
  have hbound := s2CompatFormM_ge_cheb_tight k R T m hR (by omega) h24 hcheb
  have hkpos : 0 < k := by omega
  have hD0pos : (0 : ℝ) < (D₀ k : ℝ) := by
    have : 0 < D₀ k := lt_of_lt_of_le (pow_pos hkpos 3) hD
    exact_mod_cast this
  set C := lemma53Const * (k : ℝ) with hCdef
  set M := (A1 k R (W k) T) ^ (k - 1) with hMdef
  have hM : 0 ≤ M := pow_nonneg hA1nn _
  have hB1M : 0 ≤ B1 k R (W k) T * M := mul_nonneg hB1pos.le hM
  have hB2M : 0 ≤ (B1 k R (W k) T) ^ 2 * M := mul_nonneg (sq_nonneg _) hM
  have h1 : 4 * C * Real.log R / (D₀ k : ℝ) ≤ B1 k R (W k) T / 8 := by
    rw [div_le_iff₀ hD0pos] at *
    nlinarith [hreg]
  have he1 : 4 * C * Real.log R / (D₀ k : ℝ) * (B1 k R (W k) T * M)
      ≤ 1 / 8 * ((B1 k R (W k) T) ^ 2 * M) := by
    have := mul_le_mul_of_nonneg_right h1 hB1M
    nlinarith [this]
  have h2 : 192 * (k : ℝ) ^ 2 / (D₀ k : ℝ) ≤ 1 / 16 := by
    rw [div_le_iff₀ hD0pos]
    have hk3 : (k : ℝ) ^ 3 ≤ (D₀ k : ℝ) := by exact_mod_cast hD
    have hkR : (3072 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [hk3, hkR, sq_nonneg (k : ℝ)]
  have he2 : 192 * (k : ℝ) ^ 2 / (D₀ k : ℝ) * ((B1 k R (W k) T) ^ 2 * M)
      ≤ 1 / 16 * ((B1 k R (W k) T) ^ 2 * M) :=
    mul_le_mul_of_nonneg_right h2 hB2M
  nlinarith [hbound, he1, he2]

/-! ## `D₀ k = k³` and the Mertens `φ(W)/W` lower bound (for the regime discharge)

To DISCHARGE the regime `32·(lemma53Const·k)·log R ≤ B₁·D₀` we need a lower bound
on `B₁` (via `B1_ratio_lower`, `B₁ ≥ (φW/W)·log R/(18k)`) and hence a lower bound
on `φ(W k)/W k`.  Two ingredients: `D₀ k = k³` (so `log D₀ = 3 log k`; needs a
Chebyshev prime-count bound to show the admissible tuple `H k` fits under `k³`),
and the Mertens third-theorem style bound `W/φW ≤ exp(mertensC)·log D₀`. -/

/-- Chebyshev count bound: `π(k) + k ≤ π(k³)` (there are `≥ k` primes in `(k, k³]`),
via `Chebyshev.pi_ge`.  Holds for `k ≥ 20`. -/
private lemma count_le_count_cube (k : ℕ) (hk : 20 ≤ k) :
    Nat.count Nat.Prime (k + 1) + k ≤ Nat.count Nat.Prime (k ^ 3 + 1) := by
  have hk1 : 1 < k := by omega
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hk20R : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogk : 0 < Real.log k := Real.log_pos hkR
  have hlogcube : Real.log ((k:ℝ)^3) = 3 * Real.log k := by rw [Real.log_pow]; push_cast; ring
  have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog2le : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hL : Real.log k ≤ (k:ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (k:ℝ) by linarith); linarith
  have hk3nn : (0:ℝ) ≤ (k:ℝ)^3 := by positivity
  have hk3one : (1:ℝ) ≤ (k:ℝ)^3 := one_le_pow₀ (by linarith)
  have hlogcube1 : Real.log ((k:ℝ)^3 + 1) ≤ Real.log 2 + 3 * Real.log k := by
    have h1 : (k:ℝ)^3 + 1 ≤ 2 * (k:ℝ)^3 := by linarith [hk3one]
    calc Real.log ((k:ℝ)^3+1) ≤ Real.log (2 * (k:ℝ)^3) := Real.log_le_log (by positivity) h1
      _ = Real.log 2 + Real.log ((k:ℝ)^3) := by rw [Real.log_mul (by norm_num) (by positivity)]
      _ = Real.log 2 + 3 * Real.log k := by rw [hlogcube]
  have hcubic : 6*(k:ℝ)^2 + 6*(k:ℝ) + 1 ≤ (k:ℝ)^3 / 2 := by
    nlinarith [hk20R, sq_nonneg (k:ℝ),
      mul_nonneg (show (0:ℝ) ≤ (k:ℝ) - 20 by linarith) (sq_nonneg (k:ℝ))]
  have e2 : 6*(k:ℝ)*Real.log k ≤ 6*(k:ℝ)^2 := by nlinarith [hL, hlogk.le, hk20R]
  have e4 : Real.log ((k:ℝ)^3+1) ≤ 1 + 3*(k:ℝ) := by nlinarith [hlogcube1, hlog2le, hL]
  have hk3log2 : (k:ℝ)^3/2 ≤ (k:ℝ)^3 * Real.log 2 := by nlinarith [hlog2, hk3nn]
  have hkey : (2*(k:ℝ)+1)*(3*Real.log k) ≤ (k:ℝ)^3 * Real.log 2 - Real.log ((k:ℝ)^3+1) := by
    nlinarith [e2, e4, hcubic, hk3log2, hL, hlogk.le]
  have hpi := Chebyshev.pi_ge (k ^ 3)
  rw [show ((k ^ 3 : ℕ) : ℝ) = (k : ℝ) ^ 3 by norm_cast] at hpi
  rw [hlogcube] at hpi
  have h3logk : 0 < 3 * Real.log k := by linarith
  have hpi2 : 2*(k:ℝ)+1 ≤ (Nat.primeCounting (k^3):ℝ) := by
    refine le_trans ?_ hpi
    rw [le_div_iff₀ h3logk]; exact hkey
  have hpc : Nat.primeCounting (k ^ 3) = Nat.count Nat.Prime (k ^ 3 + 1) := rfl
  have hnat : 2 * k + 1 ≤ Nat.primeCounting (k^3) := by
    have : (2*k+1 : ℝ) ≤ (Nat.primeCounting (k^3):ℝ) := by linarith [hpi2]
    exact_mod_cast this
  have hcnt : Nat.count Nat.Prime (k + 1) ≤ k + 1 := Nat.count_le Nat.Prime
  rw [← hpc]; omega

/-- `(H k).sup id ≤ k³`: the largest shift of the admissible tuple `H k` (the
`k`-th prime above `k`) is `≤ k³`, since `π(k³) − π(k) ≥ k`.  Holds for `k ≥ 20`. -/
private lemma H_sup_le_cube (k : ℕ) (hk : 20 ≤ k) : (H k).sup id ≤ k ^ 3 := by
  have hcnt := count_le_count_cube k hk
  apply Finset.sup_le
  intro h hh
  simp only [id_eq]
  unfold H at hh
  simp only [Finset.mem_image, Finset.mem_range] at hh
  obtain ⟨i, hi, rfl⟩ := hh
  rw [← Nat.lt_succ_iff]
  refine (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).mp ?_
  change firstIdxAboveK k + i < Nat.count Nat.Prime (k ^ 3 + 1)
  unfold firstIdxAboveK
  omega

/-- `D₀ k = k³` for `k ≥ 20` (the `k³` floor dominates the admissible-tuple sup). -/
theorem D0_eq_cube (k : ℕ) (hk : 20 ≤ k) : D₀ k = k ^ 3 := by
  unfold D₀
  exact max_eq_left (H_sup_le_cube k hk)

/-- The Mertens constant `∑_{p≤n} 1/(p−1) ≤ loglog n + mertensC`. -/
noncomputable def mertensC : ℝ := (sum_inv_prime_sub_one_le).choose

/-- **Mertens `W/φ(W)` bound.** `W k/φ(W k) = ∏_{p ≤ D₀} p/(p−1) ≤
exp(mertensC)·log(D₀ k)`.  The primes dividing `W = primorial(D₀)` are exactly
the primes `≤ D₀`, so the Euler product is controlled by Mertens at `n = D₀`
(unlike `phi_ratio_le`, which uses `W < R` and loses to `loglog R`). -/
theorem W_div_totient_le (k : ℕ) (hD : 2 ≤ D₀ k) :
    (W k : ℝ) / (Nat.totient (W k) : ℝ) ≤ Real.exp mertensC * Real.log (D₀ k) := by
  have hWsq : Squarefree (W k) := W_squarefree k
  have hWfac : (W k).primeFactors = (Finset.range (D₀ k + 1)).filter Nat.Prime := by
    change (primorial (D₀ k)).primeFactors = _
    rw [primorial, Nat.primeFactors_prod (fun p hp => (Finset.mem_filter.mp hp).2)]
  have hlogD : 0 < Real.log (D₀ k) := Real.log_pos (by exact_mod_cast (by omega : 1 < D₀ k))
  have ratio_eq : (W k : ℝ) / (Nat.totient (W k) : ℝ)
      = ∏ p ∈ (W k).primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    have hnum : (W k : ℝ) = ∏ p ∈ (W k).primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hWsq]
    rw [hnum, totient_squarefree_cast hWsq, ← Finset.prod_div_distrib]
  have hStepB : ∏ p ∈ (W k).primeFactors, (p : ℝ) / ((p : ℝ) - 1)
      ≤ ∏ p ∈ (W k).primeFactors, Real.exp (1 / ((p : ℝ) - 1)) := by
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      apply div_nonneg <;> linarith
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hsplit : (p : ℝ) / ((p : ℝ) - 1) = 1 / ((p : ℝ) - 1) + 1 := by
        field_simp; ring
      rw [hsplit]; linarith [Real.add_one_le_exp (1 / ((p : ℝ) - 1))]
  have hStepC : ∏ p ∈ (W k).primeFactors, Real.exp (1 / ((p : ℝ) - 1))
      = Real.exp (∑ p ∈ (W k).primeFactors, 1 / ((p : ℝ) - 1)) :=
    (Real.exp_sum _ _).symm
  have hMert : ∑ p ∈ (W k).primeFactors, 1 / ((p : ℝ) - 1)
      ≤ Real.log (Real.log (D₀ k)) + mertensC := by
    rw [hWfac]
    exact (sum_inv_prime_sub_one_le).choose_spec (D₀ k) hD
  calc (W k : ℝ) / (Nat.totient (W k) : ℝ)
      = ∏ p ∈ (W k).primeFactors, (p : ℝ) / ((p : ℝ) - 1) := ratio_eq
    _ ≤ ∏ p ∈ (W k).primeFactors, Real.exp (1 / ((p : ℝ) - 1)) := hStepB
    _ = Real.exp (∑ p ∈ (W k).primeFactors, 1 / ((p : ℝ) - 1)) := hStepC
    _ ≤ Real.exp (Real.log (Real.log (D₀ k)) + mertensC) := Real.exp_le_exp.mpr hMert
    _ = Real.log (D₀ k) * Real.exp mertensC := by rw [Real.exp_add, Real.exp_log hlogD]
    _ = Real.exp mertensC * Real.log (D₀ k) := mul_comm _ _

end Salt.Maynard
