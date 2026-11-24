/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.W3Prep
import Salt.Twelve.BudgetMomentG
import Salt.Maynard.PhiAtom
import Salt.Maynard.GFunction

/-!
# W4-1 (RelEngines) — constant-FREE relative engines

Card W4-1 of the `explicit12` wave-4 dispatch
(`docs/blueprints/explicit12-design.md`). Each of the three theorems below is
a TRUNCATION of an already-landed proof (`Salt.Twelve.marked_sqf_phi` in
`W3Prep.lean`, and `Salt.Twelve.marked_sqf_g` / `Salt.Twelve.budget_moment_g`
in `BudgetMomentG.lean`), stopping BEFORE the atom-constant step
(`Salt.Maynard.phiAtom_upper_lossy`) so that the bound is stated relative to
the a=0 crude atom `Salt.Maynard.phiAtomSum z W'` instead of an opaque
`∃ c, ...` constant. No `∃` appears anywhere; every coefficient is a literal
(`1`, `2`, `4/D`).

The Euler tail bound, the box and `h/φ` facts and `gMult_mul_coprime` are read
from `BudgetMomentG.lean`. The rest of the shared machinery (log/reindex facts,
the `1/g` divisor expansion) is `private` to its own files, so it is
re-derived here verbatim.
-/

open Finset

namespace Salt.Twelve

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Maynard

/-! ## Local helpers, re-derived from `Salt.Twelve.W3Prep` (there: `private`) -/

/-- `0 ≤ log n` for every natural `n` (`log 0 = 0`; `Real.log_nonneg` for `n ≥ 1`). -/
private lemma log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- `log m ≤ log n` for naturals `m ≤ n` (`h`), the case `m = 0` through `log_nat_nonneg`. -/
private lemma log_nat_mono_le {m n : ℕ} (h : m ≤ n) :
    Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simpa using log_nat_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

/-- A divisor `s` of a square-free `r` (`hrsf`, `hsr`) splits it as `r = s·(r/s)` with the two
factors coprime (`Nat.squarefree_mul_iff`). -/
private lemma reindex_coprime {s r : ℕ} (hrsf : Squarefree r) (hsr : s ∣ r) :
    r = s * (r / s) ∧ Nat.Coprime s (r / s) := by
  have hrs : r = s * (r / s) := by
    rw [mul_comm]; exact (Nat.div_mul_cancel hsr).symm
  have hsf : Squarefree (s * (r / s)) := hrs ▸ hrsf
  exact ⟨hrs, (Nat.squarefree_mul_iff.mp hsf).1⟩

/-- `φ(r) = φ(s)·φ(r/s)` for a divisor `s` of a square-free `r` (`hrsf`, `hsr`):
`Nat.totient_mul` on the coprime factorisation `reindex_coprime`. -/
private lemma totient_reindex {s r : ℕ} (hrsf : Squarefree r) (hsr : s ∣ r) :
    (Nat.totient r : ℝ) = (Nat.totient s : ℝ) * (Nat.totient (r / s) : ℝ) := by
  obtain ⟨hrs, hcop⟩ := reindex_coprime hrsf hsr
  have heq : Nat.totient r = Nat.totient s * Nat.totient (r / s) := by
    conv_lhs => rw [hrs]
    exact Nat.totient_mul hcop
  exact_mod_cast heq

/-! ## Local helpers, re-derived from `Salt.Twelve.BudgetMomentG` (there: `private`) -/

/-- Divisors of a squarefree `r` are the products of subsets of its prime
factors. -/
private lemma divisors_eq_powerset_image {r : ℕ} (hr : Squarefree r) :
    r.divisors = r.primeFactors.powerset.image (fun S => ∏ p ∈ S, p) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hdvd, -⟩
    exact ⟨d.primeFactors, Nat.primeFactors_mono hdvd hr.ne_zero,
      Nat.prod_primeFactors_of_squarefree (hr.squarefree_of_dvd hdvd)⟩
  · rintro ⟨S, hS, rfl⟩
    refine ⟨?_, hr.ne_zero⟩
    calc ∏ p ∈ S, p ∣ ∏ p ∈ r.primeFactors, p :=
          Finset.prod_dvd_prod_of_subset _ _ _ hS
      _ = r := Nat.prod_primeFactors_of_squarefree hr

/-- Divisor sums over a squarefree `r` are powerset sums over its prime
factors. -/
private lemma sum_divisors_eq_sum_powerset {r : ℕ} (hr : Squarefree r)
    (f : ℕ → ℝ) :
    ∑ d ∈ r.divisors, f d
      = ∑ S ∈ r.primeFactors.powerset, f (∏ p ∈ S, p) := by
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p)
      ↑r.primeFactors.powerset := by
    intro X hX Y hY hXY
    rw [Finset.mem_coe, Finset.mem_powerset] at hX hY
    have hXp : ∀ p ∈ X, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors (hX hp)
    have hYp : ∀ p ∈ Y, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors (hY hp)
    calc X = (∏ p ∈ X, p).primeFactors := (Nat.primeFactors_prod hXp).symm
      _ = (∏ p ∈ Y, p).primeFactors := congrArg Nat.primeFactors hXY
      _ = Y := Nat.primeFactors_prod hYp
  rw [divisors_eq_powerset_image hr, Finset.sum_image hinj]

/-- **The `h`-expansion.** For squarefree `r` with all prime factors `≥ 3`,
`1/g(r) = (∑_{d ∣ r} ∏_{p ∣ d} (p−2)⁻¹) · (1/φ(r))`. -/
private lemma inv_gMult_expand {r : ℕ} (hrsq : Squarefree r)
    (hp3 : ∀ p ∈ r.primeFactors, 3 ≤ p) :
    ((gMult r : ℝ))⁻¹
      = (∑ d ∈ r.divisors, ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * ((Nat.totient r : ℝ))⁻¹ := by
  have hsum : (∑ d ∈ r.divisors, ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
      = ∑ S ∈ r.primeFactors.powerset, ∏ p ∈ S, ((p : ℝ) - 2)⁻¹ := by
    rw [sum_divisors_eq_sum_powerset hrsq]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.mem_powerset] at hS
    rw [Nat.primeFactors_prod
      (fun p hp => Nat.prime_of_mem_primeFactors (hS hp))]
  have hpow : (∑ S ∈ r.primeFactors.powerset, ∏ p ∈ S, ((p : ℝ) - 2)⁻¹)
      = ∏ p ∈ r.primeFactors, (1 + ((p : ℝ) - 2)⁻¹) := by
    have h := Finset.prod_add (fun p : ℕ => ((p : ℝ) - 2)⁻¹)
      (fun _ => (1 : ℝ)) r.primeFactors
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl fun p _ => by ring
  rw [hsum, hpow, gMult_cast hp3, totient_squarefree_cast hrsq,
    ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3 p hp
  have h2 : ((p : ℝ) - 2) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  have h1 : ((p : ℝ) - 1) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  field_simp
  ring

/-- `phiAtomSum` is nonnegative (a sum of nonnegative terms). -/
private lemma phiAtomSum_nonneg (z W' : ℕ) : 0 ≤ Salt.Maynard.phiAtomSum z W' := by
  unfold Salt.Maynard.phiAtomSum
  exact Finset.sum_nonneg fun r _ => by positivity

/-! ## `marked_sqf_phi_rel`

Truncation of `Salt.Twelve.marked_sqf_phi`'s proof (`W3Prep.lean`): steps 1–6
(bound `(log r)^a` by `(log z)^a`, factor it out, apply the exact reindex
identity `1/φ(r) = (1/φ(s))·(1/φ(r/s))`, reindex `r ↦ r/s` injectively, and
extend the image to `sqfCop z W'`), STOPPING there instead of continuing on
to invoke `Salt.Maynard.phiAtom_upper_lossy` for an opaque `(W',a)`-constant. -/

omit [Salt.Maynard.TupleChoice] in
/-- **The constant-free marked φ-moment** (card W4-1). Over the square-free `r < z` coprime to
`W'` with `s ∣ r`, `Σ (log r)^a/φ(r) ≤ (log z)^a/φ(s)·phiAtomSum z W'`. The truncation of
`W3Prep`'s `marked_sqf_phi` at its steps 1–6: `(log r)^a ≤ (log z)^a` termwise,
`1/φ(r) = (1/φ(s))·(1/φ(r/s))` (`totient_reindex`), the reindex `r ↦ r/s` (injective on the
marked set), its image inside `sqfCop z W'`, whose `1/φ` sum is `phiAtomSum z W'` by definition
— stopping before the atom-constant step, so no `∃ c` appears. `hW'`, `hpos`, `hs` and `hz` are
carried for the frozen signature and not consumed. -/
theorem marked_sqf_phi_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (a : ℕ) (s z : ℕ) (hs : 0 < s) (hz : 2 ≤ z) :
    (∑ r ∈ (Finset.range z).filter
        (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ a / (Nat.totient r : ℝ))
      ≤ (1 / (Nat.totient s : ℝ)) * (Real.log z) ^ a
          * Salt.Maynard.phiAtomSum z W' := by
  -- `hW'`, `hpos`, `hs`, `hz` are not needed once the atom-constant step is
  -- dropped; keep them referenced (frozen signature) to silence the linter.
  have _hW' := hW'
  have _hpos := hpos
  have _hs := hs
  have _hz := hz
  classical
  set S : Finset ℕ :=
    (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r) with hSdef
  have hsinv0 : 0 ≤ (1 / (Nat.totient s : ℝ)) := by positivity
  -- Step 1: bound `(log r)^a` by `(log z)^a` termwise.
  have step1 : ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
      ≤ ∑ r ∈ S, (Real.log z) ^ a / (Nat.totient r : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrz, _hrsf, _hrW', _hsr⟩ := hr
    have hlogr0 : 0 ≤ Real.log (r : ℝ) := log_nat_nonneg r
    have hlogrz : Real.log (r : ℝ) ≤ Real.log (z : ℝ) := log_nat_mono_le hrz.le
    have hpow : (Real.log r) ^ a ≤ (Real.log z) ^ a := pow_le_pow_left₀ hlogr0 hlogrz a
    exact div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)
  -- Step 2: factor out the (constant, over `S`) `(log z)^a`.
  have step2 : ∑ r ∈ S, (Real.log z) ^ a / (Nat.totient r : ℝ)
      = (Real.log z) ^ a * ∑ r ∈ S, (1:ℝ) / (Nat.totient r : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  -- Step 3: the exact reindex identity `1/φ(r) = (1/φ(s)) * (1/φ(r/s))`.
  have step3 : ∑ r ∈ S, (1:ℝ) / (Nat.totient r : ℝ)
      = (1 / (Nat.totient s : ℝ)) * ∑ r ∈ S, (1:ℝ) / (Nat.totient (r / s) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨_hrz, hrsf, _hrW', hsr⟩ := hr
    rw [totient_reindex hrsf hsr, ← one_div_mul_one_div]
  -- Step 4: reindex the sum over `S` (via `r ↦ r / s`) as a sum over its image.
  have hinj : Set.InjOn (fun r => r / s) (S : Set ℕ) := by
    intro r1 hr1 r2 hr2 heq
    rw [Finset.mem_coe, hSdef, Finset.mem_filter, Finset.mem_range] at hr1 hr2
    obtain ⟨hr1z, hr1sf, hr1W', hsr1⟩ := hr1
    obtain ⟨hr2z, hr2sf, hr2W', hsr2⟩ := hr2
    have e1 : r1 = s * (r1 / s) := (reindex_coprime hr1sf hsr1).1
    have e2 : r2 = s * (r2 / s) := (reindex_coprime hr2sf hsr2).1
    have heq' : r1 / s = r2 / s := heq
    rw [e1, e2, heq']
  have step4 : ∑ r ∈ S, (1:ℝ) / (Nat.totient (r / s) : ℝ)
      = ∑ u ∈ S.image (fun r => r / s), (1:ℝ) / (Nat.totient u : ℝ) :=
    (Finset.sum_image (f := fun u => (1:ℝ) / (Nat.totient u : ℝ)) hinj).symm
  -- Step 5: extend the sum to `sqfCop z W'` (a superset, nonnegative summands).
  have hsub : S.image (fun r => r / s) ⊆ Salt.Maynard.sqfCop z W' := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨r, hr, hru⟩ := hu
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrz, hrsf, hrW', hsr⟩ := hr
    obtain ⟨hreq, -⟩ := reindex_coprime hrsf hsr
    have hru' : r / s = u := hru
    have hudvd : u ∣ r := by
      refine ⟨s, ?_⟩
      rw [hreq, hru']
      ring
    have hult : u < z := by
      have hle : u ≤ r := by
        rw [← hru']; exact Nat.div_le_self r s
      omega
    have husf : Squarefree u := hrsf.squarefree_of_dvd hudvd
    have huW' : u.Coprime W' := hrW'.coprime_dvd_left hudvd
    unfold Salt.Maynard.sqfCop
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hult, husf, huW'⟩
  have step5 : ∑ u ∈ S.image (fun r => r / s), (1:ℝ) / (Nat.totient u : ℝ)
      ≤ ∑ u ∈ Salt.Maynard.sqfCop z W', (1:ℝ) / (Nat.totient u : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro u _ _
    positivity
  -- Step 6: `sqfCop`-sum is `phiAtomSum` by definition.
  have step6 : ∑ u ∈ Salt.Maynard.sqfCop z W', (1:ℝ) / (Nat.totient u : ℝ)
      = Salt.Maynard.phiAtomSum z W' := rfl
  have hlogz0 : 0 ≤ (Real.log z : ℝ) ^ a := pow_nonneg (log_nat_nonneg z) a
  have main : ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
      ≤ (Real.log z) ^ a * ((1 / (Nat.totient s : ℝ)) * Salt.Maynard.phiAtomSum z W') := by
    calc ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
        ≤ ∑ r ∈ S, (Real.log z) ^ a / (Nat.totient r : ℝ) := step1
      _ = (Real.log z) ^ a * ∑ r ∈ S, (1:ℝ) / (Nat.totient r : ℝ) := step2
      _ = (Real.log z) ^ a
            * ((1 / (Nat.totient s : ℝ)) * ∑ r ∈ S, (1:ℝ) / (Nat.totient (r / s) : ℝ)) := by
          rw [step3]
      _ = (Real.log z) ^ a
            * ((1 / (Nat.totient s : ℝ))
                * ∑ u ∈ S.image (fun r => r / s), (1:ℝ) / (Nat.totient u : ℝ)) := by
          rw [step4]
      _ ≤ (Real.log z) ^ a
            * ((1 / (Nat.totient s : ℝ))
                * ∑ u ∈ Salt.Maynard.sqfCop z W', (1:ℝ) / (Nat.totient u : ℝ)) := by
          have := mul_le_mul_of_nonneg_left step5 hsinv0
          exact mul_le_mul_of_nonneg_left this hlogz0
      _ = (Real.log z) ^ a * ((1 / (Nat.totient s : ℝ)) * Salt.Maynard.phiAtomSum z W') := by
          rw [step6]
  calc ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
      ≤ (Real.log z) ^ a * ((1 / (Nat.totient s : ℝ)) * Salt.Maynard.phiAtomSum z W') := main
    _ = (1 / (Nat.totient s : ℝ)) * (Real.log z) ^ a * Salt.Maynard.phiAtomSum z W' := by ring

/-! ## `marked_sqf_g_rel`

Truncation of `Salt.Twelve.marked_sqf_g`'s proof (`BudgetMomentG.lean`): the
`r = s·b` reindex/multiplicativity step (Step A, unchanged) followed by the
divisor-swap bound on `∑_{b} 1/g(b)` (Step B), with the constant-bearing
`marked_sqf_phi` call replaced by `marked_sqf_phi_rel`, landing the tail at
`2 · phiAtomSum z W'` (the `2` is the same `exp(2/D) ≤ 2`-shaped Euler-tail
factor as the landed proof, from `tail_full_le`). -/

omit [Salt.Maynard.TupleChoice] in
/-- **The constant-free marked `g`-moment** (card W4-1). Over the square-free `r < z` coprime to
`W'` with `s ∣ r`, `Σ (log r)^a/g(r) ≤ 2·(log z)^a/g(s)·phiAtomSum z W'`, for square-free
`W' > 0` (`hW'`, `hpos`), `3 ≤ D` below every prime not dividing `W'` (`hD`, `hDp`) and `2 ≤ z`
(`hz`). Step A, unchanged from `BudgetMomentG`'s `marked_sqf_g`: reindex `r = s·b`,
`g(r) = g(s)·g(b)` on the coprime factorisation, `(log r)^a ≤ (log z)^a`, the image inside the
`b < z` square-free, coprime to `W'` and to `s`. Step B, relative: expand
`1/g(b) = Σ_{d ∣ b} h(d)/φ(b)`, `h(d) = ∏_{p ∣ d} (p − 2)⁻¹` (`inv_gMult_expand`), swap to the
moduli `d` (square-free, every prime factor `> D`), bound each `d`-marked `1/φ` sum by
`marked_sqf_phi_rel` at `a = 0` (`PAS/φ(d)`), and sum `h(d)/φ(d) = ∏_{p ∣ d} ((p − 1)(p − 2))⁻¹`
over the moduli by the Euler tail `tail_full_le` (`≤ 2`). `hs` is carried for the frozen
signature and not consumed. -/
theorem marked_sqf_g_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (a : ℕ) (D s z : ℕ) (hD : 3 ≤ D)
    (hDp : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) (hs : 0 < s) (hz : 2 ≤ z) :
    (∑ r ∈ (Finset.range z).filter
        (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ a / (gMult r : ℝ))
      ≤ (1 / (gMult s : ℝ)) * 2 * (Real.log z) ^ a
          * Salt.Maynard.phiAtomSum z W' := by
  -- `hs` is not needed (the reindex/divisor-swap argument is `s`-uniform,
  -- with the even-`s` degeneracy self-consistent via `x/0 = 0`); keep it
  -- referenced (frozen signature) to silence the linter.
  have _hs := hs
  classical
  set Fs := (Finset.range z).filter
    (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r) with hFs
  set B := (Finset.range z).filter
    (fun b => Squarefree b ∧ b.Coprime W' ∧ b.Coprime s) with hB
  have hlogz0 : (0 : ℝ) ≤ Real.log z :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
  -- Step A (unchanged from `marked_sqf_g`): reindex `r = s·b`, factor
  -- `g(r) = g(s)·g(b)`, bound `(log r)^a ≤ (log z)^a`.
  have hStepA : ∑ r ∈ Fs, (Real.log r) ^ a / (gMult r : ℝ)
      ≤ (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * ∑ b ∈ B, (gMult b : ℝ)⁻¹ := by
    have hmap_inj : Set.InjOn (fun r => r / s) (Fs : Set ℕ) := by
      intro r1 h1 r2 h2 heq
      rw [Finset.mem_coe, hFs, Finset.mem_filter, Finset.mem_range] at h1 h2
      obtain ⟨_, _, _, hsr1⟩ := h1
      obtain ⟨_, _, _, hsr2⟩ := h2
      have e1 : s * (r1 / s) = r1 := Nat.mul_div_cancel' hsr1
      have e2 : s * (r2 / s) = r2 := Nat.mul_div_cancel' hsr2
      have hh : r1 / s = r2 / s := heq
      rw [← e1, ← e2, hh]
    have himg_sub : Fs.image (fun r => r / s) ⊆ B := by
      refine Finset.forall_mem_image.2 fun r hr => ?_
      rw [hFs, Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨hrz, hrsf, hrW', hsr⟩ := hr
      have hrsb : r = s * (r / s) := (Nat.mul_div_cancel' hsr).symm
      have hbdvd : (r / s) ∣ r :=
        ⟨s, by rw [mul_comm]; exact (Nat.mul_div_cancel' hsr).symm⟩
      rw [hB, Finset.mem_filter, Finset.mem_range]
      refine ⟨lt_of_le_of_lt (Nat.div_le_self r s) hrz,
        hrsf.squarefree_of_dvd hbdvd, hrW'.coprime_dvd_left hbdvd, ?_⟩
      have hsqsb : Squarefree (s * (r / s)) := hrsb ▸ hrsf
      exact (Nat.coprime_of_squarefree_mul hsqsb).symm
    have hper : ∀ r ∈ Fs, (Real.log r) ^ a / (gMult r : ℝ)
        ≤ (Real.log z) ^ a * ((gMult s : ℝ)⁻¹ * (gMult (r / s) : ℝ)⁻¹) := by
      intro r hr
      rw [hFs, Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨hrz, hrsf, _hrW', hsr⟩ := hr
      have hrsb : r = s * (r / s) := (Nat.mul_div_cancel' hsr).symm
      have hcop_s_b : Nat.Coprime s (r / s) := by
        have hsqsb : Squarefree (s * (r / s)) := hrsb ▸ hrsf
        exact Nat.coprime_of_squarefree_mul hsqsb
      have hgmul : gMult r = gMult s * gMult (r / s) := by
        have h := gMult_mul_coprime hcop_s_b
        rwa [← hrsb] at h
      have hinv : (gMult r : ℝ)⁻¹ = (gMult s : ℝ)⁻¹ * (gMult (r / s) : ℝ)⁻¹ := by
        rw [hgmul, Nat.cast_mul, mul_inv]
      rw [div_eq_mul_inv, hinv]
      have hr1 : (1 : ℕ) ≤ r := Nat.pos_of_ne_zero hrsf.ne_zero
      have hlogr0 : (0 : ℝ) ≤ Real.log r :=
        Real.log_nonneg (by exact_mod_cast hr1)
      have hlogrz : Real.log r ≤ Real.log z :=
        Real.log_le_log (by exact_mod_cast hr1) (by exact_mod_cast hrz.le)
      have hpow : (Real.log r) ^ a ≤ (Real.log z) ^ a :=
        pow_le_pow_left₀ hlogr0 hlogrz a
      have hK0 : (0 : ℝ) ≤ (gMult s : ℝ)⁻¹ * (gMult (r / s) : ℝ)⁻¹ :=
        mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact mul_le_mul_of_nonneg_right hpow hK0
    have himg : ∑ b ∈ Fs.image (fun r => r / s), (gMult b : ℝ)⁻¹
        = ∑ r ∈ Fs, (gMult (r / s) : ℝ)⁻¹ := Finset.sum_image hmap_inj
    calc ∑ r ∈ Fs, (Real.log r) ^ a / (gMult r : ℝ)
        ≤ ∑ r ∈ Fs, (Real.log z) ^ a * ((gMult s : ℝ)⁻¹ * (gMult (r / s) : ℝ)⁻¹) :=
          Finset.sum_le_sum hper
      _ = (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * ∑ r ∈ Fs, (gMult (r / s) : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun r _ => by ring)
      _ = (gMult s : ℝ)⁻¹ * (Real.log z) ^ a
            * ∑ b ∈ Fs.image (fun r => r / s), (gMult b : ℝ)⁻¹ := by rw [himg]
      _ ≤ (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * ∑ b ∈ B, (gMult b : ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hlogz0 a))
          exact Finset.sum_le_sum_of_subset_of_nonneg himg_sub
            (fun b _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  -- Step B (relative): `∑_{b∈B} 1/g(b) ≤ 2 · phiAtomSum z W'`.
  have hPASnn : 0 ≤ Salt.Maynard.phiAtomSum z W' := phiAtomSum_nonneg z W'
  have hStepB : ∑ b ∈ B, (gMult b : ℝ)⁻¹ ≤ 2 * Salt.Maynard.phiAtomSum z W' := by
    have hexp : ∀ b ∈ B, (gMult b : ℝ)⁻¹
        = ∑ d ∈ Finset.range (z + 1),
            if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (Nat.totient b : ℝ)⁻¹ else 0 := by
      intro b hb
      rw [hB, Finset.mem_filter, Finset.mem_range] at hb
      obtain ⟨hbz, hbsf, hbW', _⟩ := hb
      have hp3 : ∀ p ∈ b.primeFactors, 3 ≤ p := by
        intro p hp
        have := box_prime_gt hbW' hDp (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp)
        omega
      calc (gMult b : ℝ)⁻¹
          = (∑ d ∈ b.divisors, ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (Nat.totient b : ℝ)⁻¹ := inv_gMult_expand hbsf hp3
        _ = ∑ d ∈ b.divisors,
              (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹) * (Nat.totient b : ℝ)⁻¹ := by
            rw [Finset.sum_mul]
        _ = _ := sum_divisors_eq_sum_range hbsf.ne_zero (by omega) _
    have hswap : ∑ b ∈ B, (gMult b : ℝ)⁻¹
        = ∑ d ∈ Finset.range (z + 1), ∑ b ∈ B,
            if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (Nat.totient b : ℝ)⁻¹ else 0 := by
      rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    rw [hswap]
    have hvanish : ∀ d ∈ Finset.range (z + 1),
        (∑ b ∈ B, if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * (Nat.totient b : ℝ)⁻¹ else 0) ≠ 0 →
        (Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p) := by
      intro d _ hne
      by_contra hnot
      apply hne
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [if_neg]
      intro hdb
      rw [hB, Finset.mem_filter] at hb
      obtain ⟨_, hbsf, hbW', _⟩ := hb
      exact hnot ⟨hbsf.squarefree_of_dvd hdb, fun p hp =>
        box_prime_gt hbW' hDp (Nat.prime_of_mem_primeFactors hp)
          (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdb)⟩
    rw [← Finset.sum_filter_of_ne hvanish]
    have hbound : ∀ d ∈ (Finset.range (z + 1)).filter
        (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
        (∑ b ∈ B, if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * (Nat.totient b : ℝ)⁻¹ else 0)
          ≤ (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_range] at hd
      obtain ⟨_hdz1, hdsf, hdbig⟩ := hd
      have hpull : (∑ b ∈ B, if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (Nat.totient b : ℝ)⁻¹ else 0)
          = (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ∑ b ∈ B, (if d ∣ b then (Nat.totient b : ℝ)⁻¹ else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b _ => by rw [mul_ite, mul_zero])
      rw [hpull]
      have hHnn : (0 : ℝ) ≤ ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹ := by
        refine Finset.prod_nonneg fun p hp => ?_
        have hpD : (D : ℝ) < (p : ℝ) := by exact_mod_cast hdbig p hp
        have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
        exact inv_nonneg.mpr (by linarith)
      have hmarked : ∑ b ∈ B, (if d ∣ b then (Nat.totient b : ℝ)⁻¹ else 0)
          ≤ (Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W' := by
        have hd0 : 0 < d := Nat.pos_of_ne_zero hdsf.ne_zero
        rw [← Finset.sum_filter]
        have hsub : B.filter (fun b => d ∣ b) ⊆ (Finset.range z).filter
            (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r) := by
          intro b hb
          rw [Finset.mem_filter, hB, Finset.mem_filter, Finset.mem_range] at hb
          obtain ⟨⟨hbz, hbsf, hbW', _⟩, hdb⟩ := hb
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hbz, hbsf, hbW', hdb⟩
        calc ∑ b ∈ B.filter (fun b => d ∣ b), (Nat.totient b : ℝ)⁻¹
            ≤ ∑ r ∈ (Finset.range z).filter
                (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r), (Nat.totient r : ℝ)⁻¹ := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun r _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
          _ = ∑ r ∈ (Finset.range z).filter
                (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r),
                (Real.log r) ^ 0 / (Nat.totient r : ℝ) := by
              exact Finset.sum_congr rfl (fun r _ => by rw [pow_zero, one_div])
          _ ≤ (1 / (Nat.totient d : ℝ)) * (Real.log z) ^ 0
                * Salt.Maynard.phiAtomSum z W' :=
              marked_sqf_phi_rel W' hW' hpos 0 d z hd0 hz
          _ = (Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W' := by
              rw [one_div, pow_zero, mul_one]
      calc (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ∑ b ∈ B, (if d ∣ b then (Nat.totient b : ℝ)⁻¹ else 0)
          ≤ (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ((Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W') :=
            mul_le_mul_of_nonneg_left hmarked hHnn
        _ = (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' := by
            rw [← h_over_phi hdsf]; ring
    calc ∑ d ∈ (Finset.range (z + 1)).filter
          (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
          (∑ b ∈ B, if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (Nat.totient b : ℝ)⁻¹ else 0)
        ≤ ∑ d ∈ (Finset.range (z + 1)).filter
            (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
            (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' :=
          Finset.sum_le_sum hbound
      _ = (∑ d ∈ (Finset.range (z + 1)).filter
            (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
            ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' := by
          rw [Finset.sum_mul]
      _ ≤ 2 * Salt.Maynard.phiAtomSum z W' :=
          mul_le_mul_of_nonneg_right (tail_full_le D (z + 1) hD (by omega)) hPASnn
  calc ∑ r ∈ Fs, (Real.log r) ^ a / (gMult r : ℝ)
      ≤ (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * ∑ b ∈ B, (gMult b : ℝ)⁻¹ := hStepA
    _ ≤ (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * (2 * Salt.Maynard.phiAtomSum z W') := by
        exact mul_le_mul_of_nonneg_left hStepB
          (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hlogz0 a))
    _ = 1 / (gMult s : ℝ) * 2 * (Real.log z) ^ a * Salt.Maynard.phiAtomSum z W' := by
        rw [one_div]; ring

/-! ## `g_gap_rel`

Truncation of `Salt.Twelve.budget_moment_g`'s proof (`BudgetMomentG.lean`):
only the UPPER half of the two-sided sandwich (the `LOWER` half, `φ-sum ≤
g-sum`, needs `box_g_pos`/`gMult_le_totient` positivity and is not part of
this frozen deliverable). The `d ≠ 1` divisor tail is bounded via
`marked_sqf_phi_rel` instead of the constant-bearing `marked_sqf_phi`, and
since `marked_sqf_phi_rel` at `a = 0` carries no `log z`/`log R` factor at
all, the tail lands directly at `(4/D)·phiAtomSum z W'` with no `log R`
multiplier (unlike the landed `Cg/D · log R` correction). -/

omit [Salt.Maynard.TupleChoice] in
/-- **The constant-free `g → φ` gap of the budget moment** (card W4-1; the UPPER half of
`BudgetMomentG`'s `budget_moment_g` sandwich). Over the square-free `r < z` coprime to `W'`,
with the budget weight `w(r) = (log r/log R)^c·((log z − log r)/log R)^b`,
`Σ w(r)/g(r) ≤ Σ w(r)/φ(r) + (4/D)·phiAtomSum z W'`, for square-free `W' > 0` (`hW'`, `hpos`),
`3 ≤ D` below every prime not dividing `W'` (`hD`, `hDp`), `2 ≤ z ≤ R` (`hz`, `hzR`) and
`1 ≤ log R` (`hlR`). Expand `1/g(r)` by `inv_gMult_expand`: the `d = 1` modulus is the φ-sum,
and the `d ≠ 1` tail — with `w(r) ≤ 1` and `marked_sqf_phi_rel` at `a = 0` for each `d` — is at
most `Σ_{d ≠ 1} h(d)/φ(d)·PAS ≤ 2/(D − 1)·PAS ≤ (4/D)·PAS` (`tail_erase_le`). No `log R` factor
rides on the tail, where the landed sandwich carries `Cg/D·log R`. -/
theorem g_gap_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (c b : ℕ) (D z R : ℕ) (hD : 3 ≤ D)
    (hDp : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p)
    (hz : 2 ≤ z) (hzR : z ≤ R) (hlR : 1 ≤ Real.log R) :
    (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
        (Real.log r / Real.log R) ^ c
          * ((Real.log z - Real.log r) / Real.log R) ^ b / (gMult r : ℝ))
      ≤ (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r / Real.log R) ^ c
            * ((Real.log z - Real.log r) / Real.log R) ^ b
            / (Nat.totient r : ℝ))
        + (4 / (D : ℝ)) * Salt.Maynard.phiAtomSum z W' := by
  classical
  set F := (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W') with hF
  set w : ℕ → ℝ := fun r => (Real.log r / Real.log R) ^ c
    * ((Real.log z - Real.log r) / Real.log R) ^ b with hw
  have hLpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le zero_lt_one hlR
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hZnn : (0 : ℝ) ≤ Real.log z := Real.log_nonneg hz1
  have hZL : Real.log z ≤ Real.log R :=
    Real.log_le_log (by linarith) (by exact_mod_cast hzR)
  have hmemF : ∀ r ∈ F, r < z ∧ Squarefree r ∧ r.Coprime W' := by
    intro r hr; rw [hF, Finset.mem_filter, Finset.mem_range] at hr; exact hr
  have hlogr_facts : ∀ r ∈ F, 0 ≤ Real.log r ∧ Real.log r ≤ Real.log z := by
    intro r hr
    obtain ⟨hrz, hrsf, _⟩ := hmemF r hr
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hrsf.ne_zero)
    exact ⟨Real.log_nonneg hr1, Real.log_le_log (by linarith) (by exact_mod_cast hrz.le)⟩
  have hw_nonneg : ∀ r ∈ F, 0 ≤ w r := by
    intro r hr
    obtain ⟨hlr0, hlrz⟩ := hlogr_facts r hr
    rw [hw]
    exact mul_nonneg (pow_nonneg (div_nonneg hlr0 hLpos.le) c)
      (pow_nonneg (div_nonneg (by linarith) hLpos.le) b)
  have hw_le1 : ∀ r ∈ F, w r ≤ 1 := by
    intro r hr
    obtain ⟨hlr0, hlrz⟩ := hlogr_facts r hr
    rw [hw]
    refine mul_le_one₀ ?_ (pow_nonneg (div_nonneg (by linarith) hLpos.le) b) ?_
    · exact pow_le_one₀ (div_nonneg hlr0 hLpos.le) ((div_le_one hLpos).mpr (by linarith))
    · exact pow_le_one₀ (div_nonneg (by linarith) hLpos.le)
        ((div_le_one hLpos).mpr (by linarith))
  have hPASnn : 0 ≤ Salt.Maynard.phiAtomSum z W' := phiAtomSum_nonneg z W'
  -- `w r / g(r) = w r / φ(r) + tail`, `tail ≤ (4/D) · phiAtomSum z W'`.
  have hexp : ∀ r ∈ F, w r / (gMult r : ℝ)
      = ∑ d ∈ Finset.range (z + 1),
          if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (w r * (Nat.totient r : ℝ)⁻¹) else 0 := by
    intro r hr
    obtain ⟨_hrz, hrsf, hrW'⟩ := hmemF r hr
    have hp3 : ∀ p ∈ r.primeFactors, 3 ≤ p := by
      intro p hp
      have := box_prime_gt hrW' hDp (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
      omega
    calc w r / (gMult r : ℝ)
        = w r * (gMult r : ℝ)⁻¹ := div_eq_mul_inv _ _
      _ = (∑ d ∈ r.divisors, ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (w r * (Nat.totient r : ℝ)⁻¹) := by rw [inv_gMult_expand hrsf hp3]; ring
      _ = ∑ d ∈ r.divisors,
            (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹) * (w r * (Nat.totient r : ℝ)⁻¹) := by
          rw [Finset.sum_mul]
      _ = _ := sum_divisors_eq_sum_range hrsf.ne_zero (by omega) _
  have hswap : ∑ r ∈ F, w r / (gMult r : ℝ)
      = ∑ d ∈ Finset.range (z + 1), ∑ r ∈ F,
          if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (w r * (Nat.totient r : ℝ)⁻¹) else 0 := by
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  have h1mem : (1 : ℕ) ∈ Finset.range (z + 1) := by
    rw [Finset.mem_range]; omega
  have hd1 : (∑ r ∈ F, if (1 : ℕ) ∣ r then
        (∏ p ∈ (1 : ℕ).primeFactors, ((p : ℝ) - 2)⁻¹)
          * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
      = ∑ r ∈ F, w r / (Nat.totient r : ℝ) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [if_pos (one_dvd r), Nat.primeFactors_one, Finset.prod_empty, one_mul,
      div_eq_mul_inv]
  have hsplit := Finset.add_sum_erase (Finset.range (z + 1))
    (fun d => ∑ r ∈ F, if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
      * (w r * (Nat.totient r : ℝ)⁻¹) else 0) h1mem
  rw [hd1] at hsplit
  have hvanish : ∀ d ∈ (Finset.range (z + 1)).erase 1,
      (∑ r ∈ F, if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
        * (w r * (Nat.totient r : ℝ)⁻¹) else 0) ≠ 0 →
      (Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p) := by
    intro d _ hne
    by_contra hnot
    apply hne
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [if_neg]
    intro hdr
    obtain ⟨_, hrsf, hrW'⟩ := hmemF r hr
    exact hnot ⟨hrsf.squarefree_of_dvd hdr, fun p hp =>
      box_prime_gt hrW' hDp (Nat.prime_of_mem_primeFactors hp)
        (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdr)⟩
  have hbound : ∀ d ∈ ((Finset.range (z + 1)).filter
      (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1,
      (∑ r ∈ F, if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
        * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
        ≤ (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
            * Salt.Maynard.phiAtomSum z W' := by
    intro d hd
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨_hd1, _hdz1, hdsf, hdbig⟩ := hd
    have hpull : (∑ r ∈ F, if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
        = (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ∑ r ∈ F, (if d ∣ r then w r * (Nat.totient r : ℝ)⁻¹ else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun r _ => by rw [mul_ite, mul_zero])
    rw [hpull]
    have hHnn : (0 : ℝ) ≤ ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹ := by
      refine Finset.prod_nonneg fun p hp => ?_
      have hpD : (D : ℝ) < (p : ℝ) := by exact_mod_cast hdbig p hp
      have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
      exact inv_nonneg.mpr (by linarith)
    have hmarked : ∑ r ∈ F, (if d ∣ r then w r * (Nat.totient r : ℝ)⁻¹ else 0)
        ≤ (Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W' := by
      have hd0 : 0 < d := Nat.pos_of_ne_zero hdsf.ne_zero
      rw [← Finset.sum_filter]
      have hsub : F.filter (fun r => d ∣ r) ⊆ (Finset.range z).filter
          (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r) := by
        intro r hr
        rw [Finset.mem_filter, hF, Finset.mem_filter, Finset.mem_range] at hr
        obtain ⟨⟨hrz, hrsf, hrW'⟩, hdr⟩ := hr
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hrz, hrsf, hrW', hdr⟩
      calc ∑ r ∈ F.filter (fun r => d ∣ r), w r * (Nat.totient r : ℝ)⁻¹
          ≤ ∑ r ∈ F.filter (fun r => d ∣ r), (Nat.totient r : ℝ)⁻¹ := by
            refine Finset.sum_le_sum fun r hr => ?_
            rw [Finset.mem_filter] at hr
            have hwr := hw_le1 r hr.1
            have hφnn : (0 : ℝ) ≤ (Nat.totient r : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
            calc w r * (Nat.totient r : ℝ)⁻¹
                ≤ 1 * (Nat.totient r : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hwr hφnn
              _ = (Nat.totient r : ℝ)⁻¹ := one_mul _
        _ ≤ ∑ r ∈ (Finset.range z).filter
              (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r), (Nat.totient r : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun r _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
        _ = ∑ r ∈ (Finset.range z).filter
              (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r),
              (Real.log r) ^ 0 / (Nat.totient r : ℝ) :=
            Finset.sum_congr rfl (fun r _ => by rw [pow_zero, one_div])
        _ ≤ (1 / (Nat.totient d : ℝ)) * (Real.log z) ^ 0 * Salt.Maynard.phiAtomSum z W' :=
            marked_sqf_phi_rel W' hW' hpos 0 d z hd0 hz
        _ = (Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W' := by
            rw [one_div, pow_zero, mul_one]
    calc (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * ∑ r ∈ F, (if d ∣ r then w r * (Nat.totient r : ℝ)⁻¹ else 0)
        ≤ (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ((Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W') :=
          mul_le_mul_of_nonneg_left hmarked hHnn
      _ = (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
            * Salt.Maynard.phiAtomSum z W' := by
          rw [← h_over_phi hdsf]; ring
  have htail :
      (∑ d ∈ (Finset.range (z + 1)).erase 1, ∑ r ∈ F,
        if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
      ≤ (4 : ℝ) / D * Salt.Maynard.phiAtomSum z W' := by
    have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
    have hDm1 : (0 : ℝ) < (D : ℝ) - 1 := by linarith
    calc (∑ d ∈ (Finset.range (z + 1)).erase 1, ∑ r ∈ F,
            if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
        = ∑ d ∈ ((Finset.range (z + 1)).filter
            (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1,
            ∑ r ∈ F, if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (w r * (Nat.totient r : ℝ)⁻¹) else 0 := by
          rw [← Finset.filter_erase, Finset.sum_filter_of_ne hvanish]
      _ ≤ ∑ d ∈ ((Finset.range (z + 1)).filter
            (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1,
            (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' :=
          Finset.sum_le_sum hbound
      _ = (∑ d ∈ ((Finset.range (z + 1)).filter
            (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1,
            ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' := by
          rw [Finset.sum_mul]
      _ ≤ (2 / ((D : ℝ) - 1)) * Salt.Maynard.phiAtomSum z W' :=
          mul_le_mul_of_nonneg_right (tail_erase_le D (z + 1) hD) hPASnn
      _ ≤ (4 : ℝ) / D * Salt.Maynard.phiAtomSum z W' := by
          have hfrac : (2 : ℝ) / ((D : ℝ) - 1) ≤ 4 / (D : ℝ) := by
            rw [div_le_div_iff₀ hDm1 hDpos]; linarith
          exact mul_le_mul_of_nonneg_right hfrac hPASnn
  have heq : ∑ r ∈ F, w r / (gMult r : ℝ)
      = (∑ r ∈ F, w r / (Nat.totient r : ℝ))
        + ∑ d ∈ (Finset.range (z + 1)).erase 1, ∑ r ∈ F,
          if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (w r * (Nat.totient r : ℝ)⁻¹) else 0 := by
    rw [hswap, ← hsplit]
  rw [heq]
  linarith [htail]

end Salt.Twelve
