/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.MarkedPrime
import Salt.Twelve.BudgetPoly

/-!
# W3-0 (prep) — composite marked-sqf atom, `eval` multiplicativity, floor-slip

Card W3-0 of the `explicit12` wave-3 dispatch
(`docs/blueprints/explicit12-design.md`). Everything downstream (`MvMoment`,
`BudgetMomentG`, `MvMomentG`, `MvI`, `MvJ`) imports this file, so its three
deliverables are landed with no `sorry`:

* `marked_sqf_phi` — the `marked_prime_phi` route
  (`Salt/Twelve/MarkedPrime.lean`) generalized from a prime divisor `p` to an
  arbitrary divisor `s`. The reindex lemmas `reindex_coprime`/`totient_reindex`
  in that file never actually used primality of `p` (only `Squarefree r` and
  `s ∣ r`), so the generalization is a direct port with `s` in place of `p`
  and `Nat.totient s` in place of `p - 1`.
* `eval_mul`/`eval_sq` — multiplicativity of `BudgetPoly.eval` under `mul`/`sq`
  (`Salt/Twelve/BudgetPoly.lean`), by the same `List.flatMap`/`map`/`sum`
  induction used there for `simplexInt_mul`.
* `log_natCap_slip` — the floor-slip helper bounding the gap between
  `Real.log` of a ℕ-division cap `(z - 1) / r + 1` and the real ratio
  `log z - log r`, by exactly `Real.log 2` (as frozen).
-/

open Finset

namespace Salt.Twelve

open Salt.Maynard

/-! ## Log helpers (as in `Salt/Twelve/MarkedPrime.lean`/`MomentAtom.lean`) -/

private lemma log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

private lemma log_nat_mono_le {m n : ℕ} (h : m ≤ n) :
    Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simpa using log_nat_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

/-! ## `marked_sqf_phi`: the composite-`s` marked atom -/

/-- Given `s ∣ r` with `r` squarefree: `r = s·(r/s)`, and `s` is coprime to
`r/s` (this falls straight out of squarefreeness of `r`, as in
`Salt.Twelve.MarkedPrime.reindex_coprime`, but no primality of `s` is needed
anywhere in that argument — it is a direct generalization). -/
private lemma reindex_coprime {s r : ℕ} (hrsf : Squarefree r) (hsr : s ∣ r) :
    r = s * (r / s) ∧ Nat.Coprime s (r / s) := by
  have hrs : r = s * (r / s) := by
    rw [mul_comm]; exact (Nat.div_mul_cancel hsr).symm
  have hsf : Squarefree (s * (r / s)) := hrs ▸ hrsf
  exact ⟨hrs, (Nat.squarefree_mul_iff.mp hsf).1⟩

/-- The reindexed totient identity: `φ(r) = φ(s)·φ(r/s)` in `ℝ`, for `s ∣ r`
with `r` squarefree. -/
private lemma totient_reindex {s r : ℕ} (hrsf : Squarefree r) (hsr : s ∣ r) :
    (Nat.totient r : ℝ) = (Nat.totient s : ℝ) * (Nat.totient (r / s) : ℝ) := by
  obtain ⟨hrs, hcop⟩ := reindex_coprime hrsf hsr
  have heq : Nat.totient r = Nat.totient s * Nat.totient (r / s) := by
    conv_lhs => rw [hrs]
    exact Nat.totient_mul hcop
  exact_mod_cast heq

/-- **W3-0, deliverable 1.** The `φ`-weighted marked-sqf sum, for an arbitrary
divisor `s` (not necessarily prime): the sub-sum of the one-dimensional
moment atom restricted to multiples of `s` is at most `(1/φ(s))` times an
explicit `(W', a)`-uniform constant `c` (independent of `s` and `z`) times
`(log z)^{a+1}`.

Route: verbatim `Salt.Twelve.marked_prime_phi`, replacing the prime `p` by a
general `s > 0` and `p - 1` by `φ(s)`. If `s` is not squarefree, or shares a
prime factor with `W'`, the filtered sum is automatically empty — but this
never needs a separate case split: every `r` in the sum already carries
`Squarefree r ∧ s ∣ r ∧ r.Coprime W'`, from which `Squarefree s` and
`s.Coprime W'` are derived locally (as in `hsub` below), so the argument goes
through uniformly whether or not the ambient `s` "looks" squarefree/coprime
from the outside. -/
theorem marked_sqf_phi (W' : ℕ) (_hW' : Squarefree W') (hpos : 0 < W') (a : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s z : ℕ, 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter
          (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
          (Real.log r) ^ a / (Nat.totient r : ℝ))
        ≤ (1 / (Nat.totient s : ℝ)) * c * (Real.log z) ^ (a + 1) := by
  have hWne : W' ≠ 0 := hpos.ne'
  obtain ⟨C, hC⟩ := Salt.Maynard.phiAtom_upper_lossy W' hWne
  set C' : ℝ := max C 0 with hC'def
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCC' : ∀ x : ℕ, 2 ≤ x → Salt.Maynard.phiAtomSum x W'
      ≤ 4 * ((Nat.totient W' / W' : ℝ) * Real.log x) + C' := by
    intro x hx
    have h1 := hC x hx
    have h2 : C ≤ C' := le_max_left _ _
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := 4 * (Nat.totient W' / W' : ℝ) + C' / Real.log 2 with hcdef
  have hc0 : 0 ≤ c := by
    have h1 : (0:ℝ) ≤ (Nat.totient W' : ℝ) / W' := by positivity
    have h2 : 0 ≤ C' / Real.log 2 := div_nonneg hC'0 hlog2pos.le
    rw [hcdef]; linarith
  refine ⟨c, hc0, fun s z _hs hz => ?_⟩
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
  -- Step 3: the exact reindex identity `1/φ(r) = (1/φ(s)) * (1/φ(r/s))`,
  -- termwise, then factor out `1/φ(s)`.
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
  -- Assemble the whole chain.
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
  have hstep7 : Salt.Maynard.phiAtomSum z W'
      ≤ 4 * ((Nat.totient W' / W' : ℝ) * Real.log z) + C' := hCC' z hz
  have hlogzge : Real.log 2 ≤ Real.log z := log_nat_mono_le hz
  have hCbound : C' * (Real.log z) ^ a ≤ (C' / Real.log 2) * (Real.log z) ^ (a + 1) := by
    have hlogzpow0 : (0:ℝ) ≤ (Real.log z) ^ a := hlogz0
    have hsucc : (Real.log z) ^ (a + 1) = (Real.log z) ^ a * Real.log z := pow_succ _ _
    have hratio : (1:ℝ) ≤ Real.log z / Real.log 2 := (one_le_div hlog2pos).mpr hlogzge
    have hkey : C' ≤ C' * (Real.log z / Real.log 2) := le_mul_of_one_le_right hC'0 hratio
    have hstep : C' * (Real.log z) ^ a
        ≤ (C' * (Real.log z / Real.log 2)) * (Real.log z) ^ a :=
      mul_le_mul_of_nonneg_right hkey hlogzpow0
    calc C' * (Real.log z) ^ a
        ≤ (C' * (Real.log z / Real.log 2)) * (Real.log z) ^ a := hstep
      _ = (C' / Real.log 2) * (Real.log z) ^ (a + 1) := by rw [hsucc]; ring
  have hfinal : (Real.log z) ^ a * ((1 / (Nat.totient s : ℝ)) * Salt.Maynard.phiAtomSum z W')
      ≤ (1 / (Nat.totient s : ℝ)) * c * (Real.log z) ^ (a + 1) := by
    have hchain : (Real.log z) ^ a * Salt.Maynard.phiAtomSum z W'
        ≤ 4 * (Nat.totient W' / W' : ℝ) * (Real.log z) ^ (a + 1)
          + (C' / Real.log 2) * (Real.log z) ^ (a + 1) := by
      have h1 : (Real.log z) ^ a * Salt.Maynard.phiAtomSum z W'
          ≤ (Real.log z) ^ a
              * (4 * ((Nat.totient W' / W' : ℝ) * Real.log z) + C') :=
        mul_le_mul_of_nonneg_left hstep7 hlogz0
      have h2 : (Real.log z) ^ a
          * (4 * ((Nat.totient W' / W' : ℝ) * Real.log z) + C')
          = 4 * (Nat.totient W' / W' : ℝ) * (Real.log z) ^ (a + 1)
            + C' * (Real.log z) ^ a := by
        rw [pow_succ]; ring
      rw [h2] at h1
      linarith [hCbound]
    calc (Real.log z) ^ a * ((1 / (Nat.totient s : ℝ)) * Salt.Maynard.phiAtomSum z W')
        = (1 / (Nat.totient s : ℝ)) * ((Real.log z) ^ a * Salt.Maynard.phiAtomSum z W') := by
          ring
      _ ≤ (1 / (Nat.totient s : ℝ)) * (4 * (Nat.totient W' / W' : ℝ) * (Real.log z) ^ (a + 1)
            + (C' / Real.log 2) * (Real.log z) ^ (a + 1)) :=
          mul_le_mul_of_nonneg_left hchain hsinv0
      _ = (1 / (Nat.totient s : ℝ)) * c * (Real.log z) ^ (a + 1) := by
          rw [hcdef]; ring
  calc ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
      ≤ (Real.log z) ^ a * ((1 / (Nat.totient s : ℝ)) * Salt.Maynard.phiAtomSum z W') := main
    _ ≤ (1 / (Nat.totient s : ℝ)) * c * (Real.log z) ^ (a + 1) := hfinal

/-! ## `eval_mul`, `eval_sq`: multiplicativity of `BudgetPoly.eval` -/

/-- `eval` is additive over list append (as `simplexInt_append`). -/
private lemma eval_append {n : ℕ} (p q : BPoly n) (t : Fin n → ℝ) :
    eval (p ++ q) t = eval p t + eval q t := by
  simp only [eval, List.map_append, List.sum_append]

/-- The evaluation of a product expands as a double sum over the two factors
(mirrors `simplexInt_mul`). -/
private lemma eval_mul_expand {n : ℕ} (p q : BPoly n) (t : Fin n → ℝ) :
    eval (mul p q) t
    = (p.map (fun a =>
        (q.map (fun b => (a.2.2 * b.2.2 : ℝ) * (∏ i, t i ^ (a.1 i + b.1 i))
            * (1 - ∑ i, t i) ^ (a.2.1 + b.2.1))).sum)).sum := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p' ih =>
    have step : mul (a :: p') q
        = q.map (fun b => (a.1 + b.1, a.2.1 + b.2.1, a.2.2 * b.2.2)) ++ mul p' q := by
      simp only [mul, List.flatMap_cons]
    rw [step, eval_append, ih]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    simp [eval, List.map_map, Function.comp_def, Pi.add_apply]

/-- **W3-0, deliverable 2a.** `eval` is multiplicative under `mul`. -/
theorem eval_mul {n : ℕ} (p q : BPoly n) (t : Fin n → ℝ) :
    eval (mul p q) t = eval p t * eval q t := by
  have hprod : ∀ a b : (Fin n → ℕ) × ℕ × ℚ,
      (∏ i, t i ^ (a.1 i + b.1 i)) = (∏ i, t i ^ a.1 i) * (∏ i, t i ^ b.1 i) := by
    intro a b
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => pow_add _ _ _)
  have hterm : ∀ a b : (Fin n → ℕ) × ℕ × ℚ,
      (a.2.2 * b.2.2 : ℝ) * (∏ i, t i ^ (a.1 i + b.1 i)) * (1 - ∑ i, t i) ^ (a.2.1 + b.2.1)
      = ((a.2.2 : ℝ) * (∏ i, t i ^ a.1 i) * (1 - ∑ i, t i) ^ a.2.1)
        * ((b.2.2 : ℝ) * (∏ i, t i ^ b.1 i) * (1 - ∑ i, t i) ^ b.2.1) := by
    intro a b
    rw [hprod a b, pow_add]
    ring
  have hinner : ∀ a : (Fin n → ℕ) × ℕ × ℚ,
      (q.map (fun b => (a.2.2 * b.2.2 : ℝ) * (∏ i, t i ^ (a.1 i + b.1 i))
          * (1 - ∑ i, t i) ^ (a.2.1 + b.2.1))).sum
      = ((a.2.2 : ℝ) * (∏ i, t i ^ a.1 i) * (1 - ∑ i, t i) ^ a.2.1) * eval q t := by
    intro a
    have hfun : (fun b : (Fin n → ℕ) × ℕ × ℚ =>
          (a.2.2 * b.2.2 : ℝ) * (∏ i, t i ^ (a.1 i + b.1 i)) * (1 - ∑ i, t i) ^ (a.2.1 + b.2.1))
        = (fun b => ((a.2.2 : ℝ) * (∏ i, t i ^ a.1 i) * (1 - ∑ i, t i) ^ a.2.1)
            * ((b.2.2 : ℝ) * (∏ i, t i ^ b.1 i) * (1 - ∑ i, t i) ^ b.2.1)) :=
      funext (fun b => hterm a b)
    rw [hfun, List.sum_map_mul_left]
    rfl
  rw [eval_mul_expand]
  calc (p.map (fun a => (q.map (fun b => (a.2.2 * b.2.2 : ℝ) * (∏ i, t i ^ (a.1 i + b.1 i))
        * (1 - ∑ i, t i) ^ (a.2.1 + b.2.1))).sum)).sum
      = (p.map (fun a => ((a.2.2 : ℝ) * (∏ i, t i ^ a.1 i) * (1 - ∑ i, t i) ^ a.2.1)
            * eval q t)).sum :=
        congrArg List.sum (List.map_congr_left fun a _ => hinner a)
    _ = (p.map (fun a => (a.2.2 : ℝ) * (∏ i, t i ^ a.1 i) * (1 - ∑ i, t i) ^ a.2.1)).sum
          * eval q t := List.sum_map_mul_right p _ (eval q t)
    _ = eval p t * eval q t := by simp only [eval]

/-- **W3-0, deliverable 2b.** `eval` turns `sq` into squaring. -/
theorem eval_sq {n : ℕ} (p : BPoly n) (t : Fin n → ℝ) :
    eval (sq p) t = eval p t ^ 2 := by
  rw [sq, eval_mul, pow_two]

/-! ## `log_natCap_slip`: the floor-slip helper -/

/-- If `x, y > 0` and `y ≤ 2x` and `x ≤ 2y`, then `log x` and `log y` are
within `log 2` of each other. -/
private lemma abs_log_sub_le_log_two {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : y ≤ 2 * x) (h2 : x ≤ 2 * y) : |Real.log x - Real.log y| ≤ Real.log 2 := by
  have e1 : Real.log (2 * x) = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx.ne'
  have e2 : Real.log (2 * y) = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy.ne'
  have b1 : Real.log x ≤ Real.log (2 * y) := Real.log_le_log hx h2
  have b2 : Real.log y ≤ Real.log (2 * x) := Real.log_le_log hy h1
  rw [e2] at b1
  rw [e1] at b2
  rw [abs_le]
  constructor <;> linarith

/-- **W3-0, deliverable 3.** The floor-slip helper: the ℕ-division cap
`(z - 1) / r + 1` (Nat division) and the real ratio `z / r`, after taking
`Real.log`, differ by at most `Real.log 2`. Needed downstream to convert
between the ℕ-capped recursive peel (`z' = (z-1)/r + 1`) and its real
budget `log z - log r`. -/
theorem log_natCap_slip (r z : ℕ) (hr : 1 ≤ r) (hrz : r < z) :
    |Real.log (((z - 1) / r + 1 : ℕ) : ℝ) - (Real.log z - Real.log r)| ≤ Real.log 2 := by
  have hrpos : 0 < r := hr
  have hzpos : 0 < z := by omega
  -- Two ℕ bounds on the cap `(z - 1) / r + 1`, kept as one fixed syntactic
  -- term throughout so `omega` treats it as a single consistent atom.
  have hA : (z - 1) / r * r ≤ z - 1 := Nat.div_mul_le_self (z - 1) r
  have hB : z - 1 < ((z - 1) / r + 1) * r :=
    (Nat.div_lt_iff_lt_mul hrpos).mp (Nat.lt_succ_self _)
  have hexp : ((z - 1) / r + 1) * r = (z - 1) / r * r + r := by ring
  have hupper : ((z - 1) / r + 1) * r ≤ 2 * z := by rw [hexp]; omega
  have hlower : z ≤ 2 * (((z - 1) / r + 1) * r) := by omega
  have hm1 : 1 ≤ (z - 1) / r + 1 := Nat.le_add_left 1 _
  -- Cast to `ℝ`.
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hrpos
  have hzR : (0:ℝ) < (z:ℝ) := by exact_mod_cast hzpos
  have hmR : (0:ℝ) < (((z - 1) / r + 1 : ℕ) : ℝ) := by exact_mod_cast hm1
  have hzrpos : (0:ℝ) < (z:ℝ) / r := div_pos hzR hrR
  have hcu : (((z - 1) / r + 1 : ℕ) : ℝ) * r ≤ 2 * z := by exact_mod_cast hupper
  have hcl : (z:ℝ) ≤ 2 * ((((z - 1) / r + 1 : ℕ) : ℝ) * r) := by exact_mod_cast hlower
  have h2 : (((z - 1) / r + 1 : ℕ) : ℝ) ≤ 2 * ((z:ℝ) / r) := by
    rw [show (2:ℝ) * ((z:ℝ)/r) = (2*(z:ℝ))/r by ring, le_div_iff₀ hrR]
    nlinarith [hcu]
  have h1 : (z:ℝ) / r ≤ 2 * (((z - 1) / r + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hrR]
    nlinarith [hcl]
  have hkey : |Real.log (((z - 1) / r + 1 : ℕ) : ℝ) - Real.log ((z:ℝ)/r)| ≤ Real.log 2 :=
    abs_log_sub_le_log_two hmR hzrpos h1 h2
  have hdiv : Real.log ((z:ℝ)/r) = Real.log z - Real.log r :=
    Real.log_div hzR.ne' hrR.ne'
  rw [hdiv] at hkey
  exact hkey

end Salt.Twelve
