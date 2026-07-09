/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S1Bound
import Salt.Maynard.S2CompatEH
import Salt.Maynard.S2MainLowerRel
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

/-- **C4 item 6 (diagonal side).** The compat diagonal is the full diagonal
`Qdiag_m` minus a `(192k²/D₀)·B₁²A₁^{k-1}` collision correction: Wave 2's signed
bound `s2Compat_ge_N`, with `s2FullFormM = Qdiag_m` (definitional) and
`Ndiag = 4B₁²·Gdiag ≤ 8B₁²A₁^{k-1}` (`Gdiag_le`).  No coupling to the P2/EH
constants — those enter in the final `C5` assembly. -/
theorem s2CompatFormM_ge_Qdiag (k R : ℕ) (T : ℝ) (m : Fin k)
    (hR : 2 ≤ R) (hD : 24 * k ^ 2 ≤ D₀ k) :
    s2CompatFormM k R (W k) m (yTensor k R T)
      ≥ Qdiag_m k R m (yTensor k R T)
        - 192 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
            * ((B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)) := by
  have hge := s2Compat_ge_N k R T m hR hD
  have hfull : s2FullFormM k R (W k) m (yTensor k R T) = Qdiag_m k R m (yTensor k R T) := by
    simp only [s2FullFormM, Qdiag_m, s2Summand]
  have hB2 : (0 : ℝ) ≤ 4 * (B1 k R (W k) T) ^ 2 := by positivity
  have hNdiag : Ndiag k R T m ≤ 8 * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1) := by
    rw [Ndiag]
    calc 4 * (B1 k R (W k) T) ^ 2 * Gdiag k R T m
        ≤ 4 * (B1 k R (W k) T) ^ 2 * (2 * (A1 k R (W k) T) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left (Gdiag_le k R T m hR (by omega)) hB2
      _ = 8 * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1) := by ring
  have hcoef : (0 : ℝ) ≤ 24 * (k : ℝ) ^ 2 / (D₀ k : ℝ) := by positivity
  have hmul : 24 * (k : ℝ) ^ 2 / (D₀ k : ℝ) * Ndiag k R T m
      ≤ 192 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
          * ((B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)) := by
    calc 24 * (k : ℝ) ^ 2 / (D₀ k : ℝ) * Ndiag k R T m
        ≤ 24 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
            * (8 * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left hNdiag hcoef
      _ = 192 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
            * ((B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)) := by ring
  linarith [hge, hfull, hmul]

/-- **C4 item 6 (assembled).** Combining the diagonal collision correction
(`s2CompatFormM_ge_Qdiag`), the relative main lower bound `s2main_lower_rel`
(P2), and the Chebyshev tensor lower bound (`hcheb`, discharged in `C5` by
`s2_tensor_lower_cheb`), the compat diagonal exceeds `(1/4)B₁²A₁^{k-1}` minus two
explicit error terms: the P2 relative error (A-type, `∝ B₁A₁^{k-1}`) and the
collision correction (`∝ (k²/D₀)B₁²A₁^{k-1}`).  `C5` bounds both by `(3/16)`
of the main using the sharp `B₁` lower bound and `k ≥ 3072`. -/
theorem s2CompatFormM_ge_cheb (k R : ℕ) (T : ℝ) (m : Fin k)
    (hR : 2 ≤ R) (hk : 1 ≤ k) (hD : 24 * k ^ 2 ≤ D₀ k)
    (hcheb : (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≥ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      s2CompatFormM k R (W k) m (yTensor k R T)
        ≥ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)
          - (4 * C * Real.log R / (D₀ k : ℝ))
              * ((B1 k R (W k) T) * (A1 k R (W k) T) ^ (k - 1))
          - 192 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
              * ((B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)) := by
  obtain ⟨C, hC0, hP2⟩ := s2main_lower_rel k R m T hR hk (by omega)
  refine ⟨C, hC0, ?_⟩
  have h6a := s2CompatFormM_ge_Qdiag k R T m hR hD
  have heq : (2 * C * Real.log R / (D₀ k : ℝ)) * (B1 k R (W k) T)
        * (2 * (A1 k R (W k) T) ^ (k - 1))
      = (4 * C * Real.log R / (D₀ k : ℝ))
          * ((B1 k R (W k) T) * (A1 k R (W k) T) ^ (k - 1)) := by ring
  rw [heq] at hP2
  linarith [h6a, hP2, hcheb]

/-! ## C5 — the counting identity and pigeonhole -/

/-- **The counting identity.** `Σ_m S₂^(m) = Σ_{n∈window} P(n)·w(n)`, where
`P(n) = #{m : (n+hₘ) prime}` and `w = weightSq ≥ 0`.  A sum swap. -/
theorem sum_S2m_eq (k K₀ N R ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ) :
    ∑ m : Fin k, S2m k K₀ N R ν₀ m y
      = ∑ n ∈ windowSet K₀ N (W k) ν₀,
          ((Finset.univ.filter (fun m : Fin k => (n + hSeq k m).Prime)).card : ℝ)
            * weightSq k R (W k) y n := by
  simp only [S2m]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_boole]

/-- **Pigeonhole.** If `Σ_m S₂^(m) > S₁ = Σ_n w(n)`, some window point `n` has
at least two prime shifts `n+hₘ`. -/
theorem exists_window_two_primes (k K₀ N R ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hgt : S1 k K₀ N R (W k) ν₀ y < ∑ m : Fin k, S2m k K₀ N R ν₀ m y) :
    ∃ n ∈ windowSet K₀ N (W k) ν₀,
      2 ≤ (Finset.univ.filter (fun m : Fin k => (n + hSeq k m).Prime)).card := by
  by_contra hcon
  rw [sum_S2m_eq, S1] at hgt
  have hle : ∑ n ∈ windowSet K₀ N (W k) ν₀,
        ((Finset.univ.filter (fun m : Fin k => (n + hSeq k m).Prime)).card : ℝ)
          * weightSq k R (W k) y n
      ≤ ∑ n ∈ windowSet K₀ N (W k) ν₀, weightSq k R (W k) y n := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hcard : (Finset.univ.filter (fun m : Fin k => (n + hSeq k m).Prime)).card ≤ 1 := by
      by_contra hc; exact hcon ⟨n, hn, by omega⟩
    calc ((Finset.univ.filter (fun m : Fin k => (n + hSeq k m).Prime)).card : ℝ)
            * weightSq k R (W k) y n
        ≤ 1 * weightSq k R (W k) y n :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            (by rw [weightSq]; exact sq_nonneg _)
      _ = weightSq k R (W k) y n := one_mul _
  linarith [hgt, hle]

/-- **Bounded gap from the sieve inequality.** If `Σ_m S₂^(m) > S₁`, the window
contains a point with two prime shifts, yielding two primes `p ≠ q` above `N`
with `|q − p| ≤ D₀ k`. -/
theorem bounded_gap_of_S2_gt_S1 (k K₀ N R ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hgt : S1 k K₀ N R (W k) ν₀ y < ∑ m : Fin k, S2m k K₀ N R ν₀ m y) :
    ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-(D₀ k : ℤ)) (D₀ k : ℤ) := by
  obtain ⟨n, hn, hcard⟩ := exists_window_two_primes k K₀ N R ν₀ y hgt
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le one_lt_two hcard)
  rw [Finset.mem_filter] at hi hj
  have hnN : N < n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  refine ⟨n + hSeq k i, n + hSeq k j, by omega, by omega, ?_, hi.2, hj.2, ?_⟩
  · have : hSeq k i ≠ hSeq k j := fun h => hij (hSeq_injective k h)
    omega
  · have hiD : hSeq k i ≤ D₀ k := hSeq_le_D₀ k i
    have hjD : hSeq k j ≤ D₀ k := hSeq_le_D₀ k j
    simp only [Set.mem_Icc]
    constructor <;> push_cast <;> omega

/-! ## C5 — the master inequality reduces to one numerical bound -/

/-- **The sieve inequality, reduced.** Given the per-`m` S₂ lower bound (EH
consumption), a uniform compat-diagonal lower bound `cval`, a uniform `Δπ`
lower bound `δ`, and the numerical inequality `hnum` (S₁ below the `k`-fold main
term), we get `S₁ < Σ_m S₂^(m)`.  Pure combining — the analytic content is all
in `hnum` (the ratio) and the input bounds. -/
theorem S1_lt_sum_S2m (k K₀ N R ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ)
    (δ errEH cval : ℝ)
    (hφ : 0 < (Nat.totient (W k) : ℝ)) (hcval : 0 ≤ cval) (hδ0 : 0 ≤ δ)
    (hDpi : ∀ m : Fin k, δ ≤ deltaPi k K₀ N m)
    (hcompat : ∀ m : Fin k, cval ≤ s2CompatFormM k R (W k) m y)
    (hEHres : ∀ m : Fin k,
      deltaPi k K₀ N m / (Nat.totient (W k) : ℝ) * s2CompatFormM k R (W k) m y - errEH
        ≤ S2m k K₀ N R ν₀ m y)
    (hnum : S1 k K₀ N R (W k) ν₀ y
      < (k : ℝ) * (δ / (Nat.totient (W k) : ℝ) * cval) - (k : ℝ) * errEH) :
    S1 k K₀ N R (W k) ν₀ y < ∑ m : Fin k, S2m k K₀ N R ν₀ m y := by
  have hlow : ∀ m : Fin k,
      δ / (Nat.totient (W k) : ℝ) * cval - errEH ≤ S2m k K₀ N R ν₀ m y := by
    intro m
    refine le_trans ?_ (hEHres m)
    have hDpinn : 0 ≤ deltaPi k K₀ N m := le_trans hδ0 (hDpi m)
    have hdiv : δ / (Nat.totient (W k) : ℝ) ≤ deltaPi k K₀ N m / (Nat.totient (W k) : ℝ) := by
      gcongr
      exact hDpi m
    have hmain : δ / (Nat.totient (W k) : ℝ) * cval
        ≤ deltaPi k K₀ N m / (Nat.totient (W k) : ℝ) * s2CompatFormM k R (W k) m y :=
      mul_le_mul hdiv (hcompat m) hcval (div_nonneg hDpinn hφ.le)
    linarith
  calc S1 k K₀ N R (W k) ν₀ y
      < (k : ℝ) * (δ / (Nat.totient (W k) : ℝ) * cval) - (k : ℝ) * errEH := hnum
    _ = ∑ _m : Fin k, (δ / (Nat.totient (W k) : ℝ) * cval - errEH) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ ∑ m : Fin k, S2m k K₀ N R ν₀ m y := Finset.sum_le_sum (fun m _ => hlow m)

end Salt.Maynard
