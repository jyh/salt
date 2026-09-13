/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE PER-CLASS SET BY PELL PERIODICITY — one seed in a class gives infinitely many in THAT class

`StridePrizePell.lean` reaches the prize's `r`-free set through the one class `n ≡ −1 (mod primorial
z)`. This file reaches EVERY admissible class, from one seed in it.

THE CONSTRUCTION.  Let `P = primorial z`, `r` admissible (`gcd(r(r+2), P) = 1`), and `n₀ ≡ r (mod
P)` with `Ω(n₀(n₀+2))` odd.  Mathlib's Pell sequences at `a = n₀ + 1` solve `x_m² − d·y_m² = 1`, `d
= n₀(n₀+2)`, with `(x_1, y_1) = (n₀ + 1, 1)`.  Both satisfy `u_{m+2} + u_m = 2a·u_{m+1}`, so the
state `(x_m, x_{m+1}, y_m, y_{m+1})` read in `ZMod P` is determined by its successor AND by its
predecessor; a repeat in the finite state space (`Finite.exists_ne_map_eq_of_infinite`) therefore
walks back to index 0, and the state is PURELY periodic with some period `T > 0`
(`pell_state_periodic`).  At `m = 1 + k·T` it reads `x_m ≡ n₀ + 1` and `y_m ≡ 1`
(`pell_class_iter`).  Then `n := x_m − 1` is `≡ r`, `n(n+2) = d·y_m²` has `Ω` odd, `d` and `y_m` are
prime to `P` (so `n(n+2)` is `z`-rough), and `x_m` is strictly increasing
(`zRough_oddOmega_infinite_class_of_seed`).  `StridePrizePell` is the case `n₀ + 1 ≡ 0`, period 4.

HONEST LABEL.  This shows that "infinitely many `z`-rough `n` with `Ω(n(n+2))` odd IN an admissible
class" follows from ONE such `n` in that class, elementarily, for every `z`.  It does not produce
the seed: that every admissible class at every `z` has one is a consequence of Tao's logarithmic
two-point Chowla (arXiv:1509.05422) at fixed modulus, and elementary only where a seed table is
computed (135 classes at `primorial z = 2310`, all witnessed).  What no elementary route reaches is
the QUANTITATIVE per-class statement — the class's `1/k`-weighted logarithmic mass — which the
stride supply carries.  ADDITIVE ONLY: every name is new, no landed declaration moves, no cap or
(B1) statement is touched, and nothing here bears on twin primes.
-/
import Salt.MR.StridePrizePell
import Salt.Entropy.Chowla.AffineFork

namespace Salt.MR
open ArithmeticFunction

/-- **⟦THE PELL STATE IS PURELY PERIODIC MOD `P`⟧ (class B)** — the recurrence runs both ways in
`ZMod P`, so a repeat walks back to index 0. -/
theorem pell_state_periodic {a : ℕ} (a1 : 1 < a) (P : ℕ) [NeZero P] :
    ∃ T : ℕ, 0 < T ∧ ∀ m, (Pell.xn a1 (m + T) : ZMod P) = Pell.xn a1 m
      ∧ (Pell.yn a1 (m + T) : ZMod P) = Pell.yn a1 m := by
  let st : ℕ → (ZMod P × ZMod P) × (ZMod P × ZMod P) := fun m =>
    (((Pell.xn a1 m : ZMod P), (Pell.xn a1 (m + 1) : ZMod P)),
      ((Pell.yn a1 m : ZMod P), (Pell.yn a1 (m + 1) : ZMod P)))
  have hx2 : ∀ m, (Pell.xn a1 (m + 2) : ZMod P) + Pell.xn a1 m = 2 * a * Pell.xn a1 (m + 1) := by
    intro m
    have h := congrArg (Nat.cast : ℕ → ZMod P) (Pell.xn_succ_succ a1 m)
    push_cast at h
    exact h
  have hy2 : ∀ m, (Pell.yn a1 (m + 2) : ZMod P) + Pell.yn a1 m = 2 * a * Pell.yn a1 (m + 1) := by
    intro m
    have h := congrArg (Nat.cast : ℕ → ZMod P) (Pell.yn_succ_succ a1 m)
    push_cast at h
    exact h
  let B : (ZMod P × ZMod P) × (ZMod P × ZMod P) → (ZMod P × ZMod P) × (ZMod P × ZMod P) :=
    fun s => ((2 * a * s.1.1 - s.1.2, s.1.1), (2 * a * s.2.1 - s.2.2, s.2.1))
  let F : (ZMod P × ZMod P) × (ZMod P × ZMod P) → (ZMod P × ZMod P) × (ZMod P × ZMod P) :=
    fun s => ((s.1.2, 2 * a * s.1.2 - s.1.1), (s.2.2, 2 * a * s.2.2 - s.2.1))
  have hB : ∀ m, st m = B (st (m + 1)) := by
    intro m
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> dsimp only [st, B] <;>
      first | rfl | linear_combination hx2 m | linear_combination hy2 m
  have hF : ∀ m, st (m + 1) = F (st m) := by
    intro m
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> dsimp only [st, F] <;>
      first | rfl | linear_combination hx2 m | linear_combination hy2 m
  have hback : ∀ i j, i ≤ j → st i = st j → st 0 = st (j - i) := by
    intro i
    induction i with
    | zero => intro j _ h; simpa using h
    | succ i ih =>
      intro j hij h
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have h' : st i = st j' := by rw [hB i, hB j', h]
      have := ih j' (by omega) h'
      simpa using this
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite st
  have hper0 : ∃ T, 0 < T ∧ st 0 = st T := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨j - i, by omega, hback i j hlt.le hij⟩
    · exact ⟨i - j, by omega, hback j i hlt.le hij.symm⟩
  obtain ⟨T, hT, h0T⟩ := hper0
  have hall : ∀ m, st (m + T) = st m := by
    intro m
    induction m with
    | zero => simpa using h0T.symm
    | succ m ih => rw [show m + 1 + T = (m + T) + 1 by omega, hF, ih, ← hF]
  refine ⟨T, hT, fun m => ?_⟩
  have h := hall m
  simp only [st, Prod.mk.injEq] at h
  exact ⟨h.1.1, h.2.1⟩

/-- **⟦AT `1 + k·T` THE STATE IS THE SEED'S⟧ (class A)** — `x ≡ a`, `y ≡ 1` mod `P`. -/
theorem pell_class_iter {a : ℕ} (a1 : 1 < a) (P : ℕ) [NeZero P] {T : ℕ}
    (hper : ∀ m, (Pell.xn a1 (m + T) : ZMod P) = Pell.xn a1 m
      ∧ (Pell.yn a1 (m + T) : ZMod P) = Pell.yn a1 m) :
    ∀ k, (Pell.xn a1 (1 + k * T) : ZMod P) = (a : ZMod P)
      ∧ (Pell.yn a1 (1 + k * T) : ZMod P) = 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 1 + (k + 1) * T = (1 + k * T) + T by ring]
    exact ⟨(hper _).1.trans ih.1, (hper _).2.trans ih.2⟩

/-- **⟦THE PER-CLASS SET FROM ONE SEED IN THE CLASS⟧ (class B)** — for every `z`, `r`, and `n₀ ≡ r
(mod primorial z)` with `gcd(r(r+2), primorial z) = 1` and `Ω(n₀(n₀+2))` odd, infinitely many `n ≡
r` have `n(n+2)` `z`-rough and `Ω(n(n+2))` odd.  `n₀ ≠ 0` is forced (`Ω 0 = 0`). -/
theorem zRough_oddOmega_infinite_class_of_seed {z r n₀ : ℕ}
    (hn₀ : n₀ % primorial z = r) (hcop : Nat.Coprime (r * (r + 2)) (primorial z))
    (hΩ : Odd (ArithmeticFunction.cardFactors (n₀ * (n₀ + 2)))) :
    {n : ℕ | n % primorial z = r ∧ (∀ p ∈ (n * (n + 2)).primeFactors, z < p)
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))}.Infinite := by
  set P := primorial z with hP
  haveI : NeZero P := ⟨(primorial_pos z).ne'⟩
  have hn₀pos : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · subst h; simp at hΩ
    · exact h
  have hK1 : 1 < n₀ + 1 := by omega
  obtain ⟨T, hT, hper⟩ := pell_state_periodic hK1 P
  have hit := pell_class_iter hK1 P hper
  have hd : (n₀ + 1) ^ 2 - 1 = n₀ * (n₀ + 2) := by
    apply Nat.sub_eq_of_eq_add; ring
  have hd0 : n₀ * (n₀ + 2) ≠ 0 := Nat.mul_ne_zero hn₀pos.ne' (by omega)
  have hcop₀ : Nat.Coprime (n₀ * (n₀ + 2)) P := by
    have h := Salt.Entropy.Chowla.coprime_twinProd_of_affine hcop (n₀ / P)
    have hdecomp : P * (n₀ / P) + r = n₀ := by rw [← hn₀]; exact Nat.div_add_mod n₀ P
    rwa [hdecomp] at h
  refine Set.infinite_of_injective_forall_mem
    (f := fun k => Pell.xn hK1 (1 + k * T) - 1) (fun i j hij => ?_) (fun k => ?_)
  · have hxi := Pell.x_pos hK1 (1 + i * T)
    have hxj := Pell.x_pos hK1 (1 + j * T)
    have h1 : Pell.xn hK1 (1 + i * T) = Pell.xn hK1 (1 + j * T) := by
      simp only at hij; omega
    have h2 := (Pell.strictMono_x hK1).injective h1
    have h3 : i * T = j * T := by omega
    exact Nat.eq_of_mul_eq_mul_right hT h3
  · obtain ⟨hxK, hy1⟩ := hit k
    set m := 1 + k * T with hm
    have hx1 := Pell.x_pos hK1 m
    have hy0 : Pell.yn hK1 m ≠ 0 := by
      have h := (Pell.strictMono_y hK1) (show 0 < m by omega)
      rw [Pell.yn_zero] at h
      omega
    have hid := pell_xn_sub_one_mul hK1 m
    rw [hd] at hid
    simp only [Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · -- the class
      have hmod : Pell.xn hK1 m ≡ n₀ + 1 [MOD P] := by
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hxK
      have hmod' : Pell.xn hK1 m - 1 + 1 ≡ n₀ + 1 [MOD P] := by
        rwa [Nat.sub_add_cancel hx1]
      have hc := Nat.ModEq.add_right_cancel' 1 hmod'
      rw [hc, hn₀]
    · -- roughness
      have hyP : Nat.Coprime (Pell.yn hK1 m) P := by
        have hmod : Pell.yn hK1 m ≡ 1 [MOD P] :=
          (ZMod.natCast_eq_natCast_iff _ _ _).mp (by push_cast; exact hy1)
        have hg := Nat.ModEq.gcd_eq hmod
        rw [Nat.Coprime, hg, Nat.gcd_one_left]
      rw [hid]
      exact Salt.Entropy.Chowla.rough_of_coprime_primorial
        (Nat.Coprime.mul_left hcop₀ (Nat.Coprime.mul_left hyP hyP))
    · rw [hid, cardFactors_mul hd0 (mul_ne_zero hy0 hy0), cardFactors_mul hy0 hy0]
      exact hΩ.add_even ⟨_, rfl⟩

end Salt.MR
