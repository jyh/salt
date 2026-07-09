/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S1Bound
import Salt.Maynard.S2CompatEH
import Salt.Maynard.ChebyshevInterval

/-!
# Endgame (C5) — S₁ wiring, the `Δπ` shift, and the pigeonhole to bounded gaps

Design: `docs/blueprints/endgame-design.md`, C5.  This file collects the
end-of-proof building blocks:

* `S1_upper_tensor` (P3) — `S1_upper` specialized to the concrete tensor
  `y = yTensor`, with its solvability hypothesis discharged by `cong_solvable`
  (compat pairs are simultaneously solvable) via `compat_lcm_coprime`.
* `deltaPi_ge` (P4) — the window prime difference `Δπ = π(64N+hₘ) − π(N+hₘ)`
  is `≥ (c/2)·N/log N` for `N` large, absorbing the fixed shift `hₘ` into the
  `primes_in_interval_ge` lower bound.
-/

namespace Salt.Maynard

open Finset

/-- **P3 — S₁ upper bound for the concrete tensor.** `fTilde` is in `[0,1]` and
divisor-antitone, and compat pairs are simultaneously solvable (`cong_solvable`
via `compat_lcm_coprime`), discharging every hypothesis of `S1_upper`. -/
theorem S1_upper_tensor (k K₀ N R ν₀ : ℕ) (T : ℝ)
    (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) (hK₀ : 1 ≤ K₀) (hR : 2 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ S1 k K₀ N R (W k) ν₀ (yTensor k R T)
      ≤ 2 * ((K₀ - 1) * N / (W k) : ℝ)
          * (∑ r ∈ kSieveIndex k R (W k),
              (yTensor k R T r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + C * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
  have hWpos : 0 < W k := Nat.pos_of_ne_zero (W_squarefree k).ne_zero
  refine S1_upper k K₀ N R (W k) ν₀ (yTensor k R T) (fTilde k R T)
    (fun n => ⟨fTilde_nonneg k R T n hR, fTilde_le_one k R T hR n⟩) ?_ (fun r => rfl) rfl
    hk hD hK₀ hR ?_
  · -- `fTilde` is divisor-antitone (with the `m = 0` degenerate case).
    intro d n hdn hd0
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : (0 : ℕ) ∉ sqfCop (R0 k R T) (W k) := by
        rw [sqfCop, Finset.mem_filter]
        rintro ⟨-, hsq, -⟩
        exact hsq.ne_zero rfl
      rw [show fTilde k R T 0 = 0 by simp only [fTilde, if_neg h0]]
      exact fTilde_nonneg k R T d hR
    · exact fTilde_anti k R T hR d n hn hdn
  · -- compat pairs are simultaneously solvable.
    intro d hd e he hcompat
    obtain ⟨hdsq, -, hdcopW, -⟩ := (mem_kSieveIndex_iff d).mp hd
    obtain ⟨hesq, -, hecopW, -⟩ := (mem_kSieveIndex_iff e).mp he
    exact cong_solvable k d e ν₀ hWpos
      (fun i => Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hdsq i).ne_zero (hesq i).ne_zero))
      (fun i => ((hdcopW i).symm.mul_right (hecopW i).symm).coprime_dvd_right
        (Nat.lcm_dvd_mul (d i) (e i)))
      (fun i j hij => compat_lcm_coprime k R hd he hcompat hij)

/-- `Nat.count p` grows by at most `h` over a window of length `h`. -/
theorem count_le_count_add (p : ℕ → Prop) [DecidablePred p] (a h : ℕ) :
    Nat.count p (a + h) ≤ Nat.count p a + h := by
  induction h with
  | zero => simp
  | succ n ih =>
    rw [← Nat.add_assoc, Nat.count_succ]
    split_ifs <;> omega

/-- `Nat.primeCounting` is monotone. -/
theorem primeCounting_mono : Monotone Nat.primeCounting := by
  intro a b hab
  unfold Nat.primeCounting Nat.primeCounting'
  exact Nat.count_monotone _ (Nat.succ_le_succ hab)

/-- `π(N+h) ≤ π(N) + h`: at most `h` primes appear in a window of length `h`. -/
theorem primeCounting_shift_le (N h : ℕ) :
    Nat.primeCounting (N + h) ≤ Nat.primeCounting N + h := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [show N + h + 1 = (N + 1) + h by ring]
  exact count_le_count_add _ (N + 1) h

/-- `primesCount x 1 0 = π(x)` (all naturals are `≡ 0 [MOD 1]`). -/
theorem primesCount_one_zero_eq (x : ℕ) : primesCount x 1 0 = Nat.primeCounting x := by
  rw [primesCount_one_zero]; rfl

/-- `Δπ ≥ 0`: the window `(N, K₀N]` (for `K₀ ≥ 1`) contains no fewer primes than
the empty window. -/
theorem deltaPi_nonneg (k K₀ N : ℕ) (m : Fin k) (hK₀ : 1 ≤ K₀) : 0 ≤ deltaPi k K₀ N m := by
  rw [deltaPi, primesCount_one_zero_eq, primesCount_one_zero_eq, sub_nonneg]
  exact_mod_cast primeCounting_mono
    (Nat.add_le_add_right (Nat.le_mul_of_pos_left N (by omega)) (hSeq k m))

/-- **P4 — the `Δπ` shift.** For `K₀ = 64`, the window prime difference is
`≥ c·N/log N − hₘ` for `N` large: `π(64N+hₘ) − π(N+hₘ) ≥ (π(64N) − π(N)) − hₘ`
(monotonicity + `primeCounting_shift_le`), and `π(64N) − π(N) ≥ c·N/log N`
(`primes_in_interval_ge`).  The fixed shift `hₘ` is carried explicitly. -/
theorem deltaPi_ge (k : ℕ) (m : Fin k) :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧ ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) / Real.log N - (hSeq k m : ℝ) ≤ deltaPi k 64 N m := by
  obtain ⟨c, N₀, hc, hkey⟩ := primes_in_interval_ge
  refine ⟨c, N₀, hc, fun N hN => ?_⟩
  have hkeyN := hkey N hN
  rw [deltaPi, primesCount_one_zero_eq, primesCount_one_zero_eq]
  -- `π(64N+hₘ) ≥ π(64N)` and `π(N+hₘ) ≤ π(N) + hₘ`.
  have hlo : (Nat.primeCounting (64 * N) : ℝ) ≤ (Nat.primeCounting (64 * N + hSeq k m) : ℝ) :=
    by exact_mod_cast primeCounting_mono (Nat.le_add_right _ _)
  have hhi : (Nat.primeCounting (N + hSeq k m) : ℝ)
      ≤ (Nat.primeCounting N : ℝ) + (hSeq k m : ℝ) := by
    exact_mod_cast primeCounting_shift_le N (hSeq k m)
  linarith [hkeyN, hlo, hhi]

end Salt.Maynard
