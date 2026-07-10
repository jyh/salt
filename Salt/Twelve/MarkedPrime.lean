/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.PhiAtom

/-!
# W2-2 (P3.b) — the marked-prime engine (explicit-gaps sieve, card W2-2)

For a fixed modulus `W'` and a prime `p ∤ W'`, bound the sub-sum of the
one-dimensional moment atom restricted to `r` DIVISIBLE by `p` (the "marked
prime" sum that appears in the Möbius/inclusion-exclusion expansion of the
`u`-coprimality coupling, Crux 1 of `docs/blueprints/explicit12-design.md`'s
wave-2 design):

`∑_{r < z, sqf, (r,W')=1, p∣r} (log r)^a / φ(r) ≤ (1/(p−1))·c_up·(log z)^{a+1}`.

## Route (elementary reindex)

Every such `r` is `r = p·s` with `s` squarefree, `(s,W')=1` (the modulus
coupling — from `(r,W')=1` and `s ∣ r`), and (crucially, for `φ`) `s` is
automatically coprime to `p` — this falls straight out of `Squarefree r`
(`Nat.squarefree_mul_iff` applied to `r = p·s`), no case split needed.
Hence `φ(r) = (p−1)·φ(s)` EXACTLY (`Nat.totient_mul`), so

`1/φ(r) = (1/(p−1))·(1/φ(s))`.

Crudely `(log r)^a ≤ (log z)^a` (since `0 < r < z`), so the marked sum is at
most `(1/(p−1))·(log z)^a·∑_{s < z/p, sqf, (s,W')=1} 1/φ(s)`, and relaxing
the range `z/p ≤ z` (dropping terms only grows a sum of nonnegative
summands) bounds this by `(1/(p−1))·(log z)^a·phiAtomSum z W'`. Feed in the
landed 4×-lossy upper bound `phiAtom_upper_lossy` (`Salt/Maynard/PhiAtom.lean`)
and absorb the resulting ABSOLUTE `(1+log z)^a`-shaped error into a single
`(log z)^{a+1}`-relative constant `c_up` (valid since `log z ≥ log 2 > 0` for
`z ≥ 2`, so `(log z)^a ≤ (log z)^{a+1}/log 2`).

## PORT-BLOCKER: `marked_prime_g`

The `g`-weighted analogue (`gMult r` in the denominator, `1/(p−2)` in front,
card W2-2's second target) does NOT land here. The φ-route's key fact —
`φ(r) = (p−1)·φ(s)` for EVERY `s` arising from a squarefree `r = p·s` — has
no `g`-analogue over an unrestricted modulus `W'`: `gMult` is only
multiplicative on COPRIME factors (`gMult(p·s) = gMult(p)·gMult(s)` when
`(p,s) = 1`, `Salt.Maynard.gMult`-shaped), and the reindexed upper bound
needs `∑_{s < z, sqf, (s,W')=1} 1/gMult(s) = O(log z)`. No such bound is
landed (`Salt/Maynard/PhiAtom.lean`/`GFunction.lean`/`S2Collision.lean` have
no `g`-harmonic sum estimate), and — more fundamentally — no UNIFORM
constant can exist without restricting `W'` so that every prime `q ∤ W'`
exceeds a fixed threshold `D`: `φ(s)/gMult(s) = ∏_{q ∣ s} (q−1)/(q−2)`, and
for `s` with several small odd prime factors (`3, 5, 7, …`) this ratio grows
with `s`'s number of distinct prime factors (unbounded over `s < z` as
`z → ∞`, since squarefree `s < z` can have `Θ(log z / log log z)` prime
factors). The design doc's own fallback
(`docs/blueprints/explicit12-design.md`, card W2-2) anticipates exactly this:
*"prefer `1/gMult ≤ C/φ` only if primes `> D` make it clean; else
PORT-BLOCKER `marked_prime_g` and land `marked_prime_phi`"* — this file
takes that fallback. The missing atom (a `D`-parameterized `g`-harmonic
upper bound, or equivalently a `budget_moment_g`-style sandwich proved
DIRECTLY at the sum level rather than per-term) is a wave-2 W2-1
(`budget_moment_g`, Crux 2) / spine concern, not a W2-2 one.
-/

open Finset

namespace Salt.Twelve

/-! ## Log helpers (as in `Salt/Twelve/MomentAtom.lean`) -/

private lemma log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

private lemma log_nat_mono_le {m n : ℕ} (h : m ≤ n) :
    Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simpa using log_nat_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

/-! ## The reindex `r = p · s` -/

/-- Given `p` prime dividing squarefree `r`: `r = p·(r/p)`, and `r/p` is
coprime to `p` (this is the whole point — it costs nothing, it falls
straight out of `r`'s squarefreeness). -/
private lemma reindex_coprime {p r : ℕ} (hrsf : Squarefree r) (hpr : p ∣ r) :
    r = p * (r / p) ∧ Nat.Coprime p (r / p) := by
  have hrp : r = p * (r / p) := by
    rw [mul_comm]; exact (Nat.div_mul_cancel hpr).symm
  have hsf : Squarefree (p * (r / p)) := hrp ▸ hrsf
  exact ⟨hrp, (Nat.squarefree_mul_iff.mp hsf).1⟩

/-- The reindexed totient identity: `φ(r) = (p−1)·φ(r/p)` in `ℝ`, for `p`
prime dividing squarefree `r`. -/
private lemma totient_reindex {p r : ℕ} (hp : p.Prime) (hrsf : Squarefree r)
    (hpr : p ∣ r) :
    (Nat.totient r : ℝ) = ((p : ℝ) - 1) * (Nat.totient (r / p) : ℝ) := by
  obtain ⟨hrp, hcop⟩ := reindex_coprime hrsf hpr
  have heq : Nat.totient r = Nat.totient p * Nat.totient (r / p) := by
    conv_lhs => rw [hrp]
    exact Nat.totient_mul hcop
  rw [heq, Nat.totient_prime hp]
  push_cast [Nat.cast_sub hp.one_lt.le]
  ring

/-! ## `marked_prime_phi` -/

/-- **W2-2 (P3.b), the `φ`-weighted marked-prime sum.** For a prime `p ∤ W'`,
the sub-sum of the one-dimensional moment atom restricted to multiples of
`p` is at most `(1/(p−1))` times an explicit `(W', a)`-uniform constant
times `(log z)^{a+1}`. -/
theorem marked_prime_phi (W' : ℕ) (_hW' : Squarefree W') (hpos : 0 < W')
    (p : ℕ) (hp : p.Prime) (_hpW' : ¬ p ∣ W') (a : ℕ) :
    ∃ c_up : ℝ, 0 ≤ c_up ∧ ∀ z : ℕ, 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r),
          (Real.log r) ^ a / (Nat.totient r : ℝ))
        ≤ (1 / (p - 1 : ℝ)) * c_up * (Real.log z) ^ (a + 1) := by
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
  set c_up : ℝ := 4 * (Nat.totient W' / W' : ℝ) + C' / Real.log 2 with hcupdef
  have hcup0 : 0 ≤ c_up := by
    have h1 : (0:ℝ) ≤ (Nat.totient W' : ℝ) / W' := by positivity
    have h2 : 0 ≤ C' / Real.log 2 := div_nonneg hC'0 hlog2pos.le
    rw [hcupdef]; linarith
  refine ⟨c_up, hcup0, fun z hz => ?_⟩
  classical
  set S : Finset ℕ :=
    (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r) with hSdef
  have hp2 : (2:ℕ) ≤ p := hp.two_le
  have hp1R : (0:ℝ) < (p:ℝ) - 1 := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    linarith
  have hcpinv0 : 0 ≤ (1 / ((p:ℝ) - 1)) := div_nonneg (by norm_num) hp1R.le
  -- Step 1: bound `(log r)^a` by `(log z)^a` termwise.
  have step1 : ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
      ≤ ∑ r ∈ S, (Real.log z) ^ a / (Nat.totient r : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrz, _hrsf, _hrW', _hrp⟩ := hr
    have hlogr0 : 0 ≤ Real.log (r : ℝ) := log_nat_nonneg r
    have hlogrz : Real.log (r : ℝ) ≤ Real.log (z : ℝ) := log_nat_mono_le hrz.le
    have hpow : (Real.log r) ^ a ≤ (Real.log z) ^ a := pow_le_pow_left₀ hlogr0 hlogrz a
    exact div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)
  -- Step 2: factor out the (constant, over `S`) `(log z)^a`.
  have step2 : ∑ r ∈ S, (Real.log z) ^ a / (Nat.totient r : ℝ)
      = (Real.log z) ^ a * ∑ r ∈ S, (1:ℝ) / (Nat.totient r : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  -- Step 3: the exact reindex identity `1/φ(r) = (1/(p-1)) * (1/φ(r/p))`,
  -- termwise, then factor out `1/(p-1)`.
  have step3 : ∑ r ∈ S, (1:ℝ) / (Nat.totient r : ℝ)
      = (1 / ((p:ℝ) - 1)) * ∑ r ∈ S, (1:ℝ) / (Nat.totient (r / p) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨_hrz, hrsf, _hrW', hrp⟩ := hr
    rw [totient_reindex hp hrsf hrp, ← one_div_mul_one_div]
  -- Step 4: reindex the sum over `S` (via `r ↦ r / p`) as a sum over its image.
  have hinj : Set.InjOn (fun r => r / p) (S : Set ℕ) := by
    intro r1 hr1 r2 hr2 heq
    rw [Finset.mem_coe, hSdef, Finset.mem_filter, Finset.mem_range] at hr1 hr2
    obtain ⟨hr1z, hr1sf, hr1W', hr1p⟩ := hr1
    obtain ⟨hr2z, hr2sf, hr2W', hr2p⟩ := hr2
    have e1 : r1 = p * (r1 / p) := (reindex_coprime hr1sf hr1p).1
    have e2 : r2 = p * (r2 / p) := (reindex_coprime hr2sf hr2p).1
    have heq' : r1 / p = r2 / p := heq
    rw [e1, e2, heq']
  have step4 : ∑ r ∈ S, (1:ℝ) / (Nat.totient (r / p) : ℝ)
      = ∑ s ∈ S.image (fun r => r / p), (1:ℝ) / (Nat.totient s : ℝ) :=
    (Finset.sum_image (f := fun s => (1:ℝ) / (Nat.totient s : ℝ)) hinj).symm
  -- Step 5: extend the sum to `sqfCop z W'` (a superset, nonnegative summands).
  have hsub : S.image (fun r => r / p) ⊆ Salt.Maynard.sqfCop z W' := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨r, hr, hrs⟩ := hs
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrz, hrsf, hrW', hrp⟩ := hr
    obtain ⟨hreq, -⟩ := reindex_coprime hrsf hrp
    have hrs' : r / p = s := hrs
    have hsdvd : s ∣ r := by
      refine ⟨p, ?_⟩
      rw [hreq, hrs']
      ring
    have hslt : s < z := by
      have hle : s ≤ r := by
        rw [← hrs']; exact Nat.div_le_self r p
      omega
    have hssf : Squarefree s := hrsf.squarefree_of_dvd hsdvd
    have hsW' : s.Coprime W' := hrW'.coprime_dvd_left hsdvd
    unfold Salt.Maynard.sqfCop
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hslt, hssf, hsW'⟩
  have step5 : ∑ s ∈ S.image (fun r => r / p), (1:ℝ) / (Nat.totient s : ℝ)
      ≤ ∑ s ∈ Salt.Maynard.sqfCop z W', (1:ℝ) / (Nat.totient s : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro s _ _
    positivity
  -- Step 6: `sqfCop`-sum is `phiAtomSum` by definition.
  have step6 : ∑ s ∈ Salt.Maynard.sqfCop z W', (1:ℝ) / (Nat.totient s : ℝ)
      = Salt.Maynard.phiAtomSum z W' := rfl
  -- Assemble the whole chain.
  have hlogz0 : 0 ≤ (Real.log z : ℝ) ^ a := pow_nonneg (log_nat_nonneg z) a
  have main : ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
      ≤ (Real.log z) ^ a * ((1 / ((p:ℝ) - 1)) * Salt.Maynard.phiAtomSum z W') := by
    calc ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
        ≤ ∑ r ∈ S, (Real.log z) ^ a / (Nat.totient r : ℝ) := step1
      _ = (Real.log z) ^ a * ∑ r ∈ S, (1:ℝ) / (Nat.totient r : ℝ) := step2
      _ = (Real.log z) ^ a
            * ((1 / ((p:ℝ) - 1)) * ∑ r ∈ S, (1:ℝ) / (Nat.totient (r / p) : ℝ)) := by
          rw [step3]
      _ = (Real.log z) ^ a
            * ((1 / ((p:ℝ) - 1))
                * ∑ s ∈ S.image (fun r => r / p), (1:ℝ) / (Nat.totient s : ℝ)) := by
          rw [step4]
      _ ≤ (Real.log z) ^ a
            * ((1 / ((p:ℝ) - 1))
                * ∑ s ∈ Salt.Maynard.sqfCop z W', (1:ℝ) / (Nat.totient s : ℝ)) := by
          have := mul_le_mul_of_nonneg_left step5 hcpinv0
          exact mul_le_mul_of_nonneg_left this hlogz0
      _ = (Real.log z) ^ a * ((1 / ((p:ℝ) - 1)) * Salt.Maynard.phiAtomSum z W') := by
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
  have hfinal : (Real.log z) ^ a * ((1 / ((p:ℝ) - 1)) * Salt.Maynard.phiAtomSum z W')
      ≤ (1 / ((p:ℝ) - 1)) * c_up * (Real.log z) ^ (a + 1) := by
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
    calc (Real.log z) ^ a * ((1 / ((p:ℝ) - 1)) * Salt.Maynard.phiAtomSum z W')
        = (1 / ((p:ℝ) - 1)) * ((Real.log z) ^ a * Salt.Maynard.phiAtomSum z W') := by ring
      _ ≤ (1 / ((p:ℝ) - 1)) * (4 * (Nat.totient W' / W' : ℝ) * (Real.log z) ^ (a + 1)
            + (C' / Real.log 2) * (Real.log z) ^ (a + 1)) :=
          mul_le_mul_of_nonneg_left hchain hcpinv0
      _ = (1 / ((p:ℝ) - 1)) * c_up * (Real.log z) ^ (a + 1) := by
          rw [hcupdef]; ring
  calc ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
      ≤ (Real.log z) ^ a * ((1 / ((p:ℝ) - 1)) * Salt.Maynard.phiAtomSum z W') := main
    _ ≤ (1 / ((p:ℝ) - 1)) * c_up * (Real.log z) ^ (a + 1) := hfinal

end Salt.Twelve
