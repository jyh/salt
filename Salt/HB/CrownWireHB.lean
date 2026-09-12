/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.CrownAssembly

/-!
# The crown wire — the N8 collapse record and the HB wire

**§0 (THIS FILE, the crown wire's first cut): THE N8 WIRE'S COLLAPSE, AS A KERNEL RECORD.**
The crown's current sieve wire `hbDataN8` (`Salt/HB/CrownAssembly.lean`) puts
`support := l2cWindow χ z x` — a window ALREADY coprime to `excPrimorial χ z`
(`l2cWindow_excPrimorial_coprime`) — under a sieve whose modulus `hbP` DIVIDES that
primorial (`l2cWindow_coprime_hbP`, whose proof is exactly that divisibility).  So every
prime the sieve is asked to sift by is a prime the window has already removed, and the two
theorems below say at the kernel what that costs: `S d = 0` for every `1 < d ∣ P`
(`hbDataN8_S_eq_zero`), whence the Rosser weight sum keeps only its `d = 1` term and
`lamSum … = S⁽³⁾` (`lamSum_S_eq_S3`) — for EVERY `Λ`, every `side ≤ 2`, every `1 ≤ b`.
Both sides of HB's sandwich (2.2) are `S⁽³⁾` itself at this data: **the dimension-4 sieve
extracts nothing here.**  Neither the sieve interface nor any landed statement is at fault —
the interface is generic in its data, and this is a fact about the DATA.  The record lands
BEFORE the wire is re-cut because it is the kernel's own sentence for why the re-cut is not
optional.

**§1–§3 are RESERVED for the next cuts and are NOT in this file yet:** the HB wire
`hbDataHB` (a modulus that is not already divided out by the support), the bridge from that
wire back to the crown window, and the p.200 lower assembly re-stated at the HB wire.

⛔ **WHAT THIS RECORD DOES NOT SAY.**  It concerns conclusion (1) of `hbSieve_fl_sandwich` —
the Rosser sandwich on the sifted sum — at `hbDataN8`, and nothing else.  It says NOTHING
about that theorem's conclusions (2) and (3), the FL defect and the per-`δ` transfers: those
are stated at other functions, they never read the `λ`-weights, and they are untouched.  No
statement anywhere is edited, weakened or re-graded by this file; it adds theorems and
removes nothing.

Nothing here bears on twin primes.
-/

namespace Salt.HB

open Salt.SW Salt.BrunLower

/-- **W1 — the vanishing.**  `S(d) = 0` for every `1 < d ∣ P` at the N8 wire: the window is
coprime to `hbP` (`l2cWindow_coprime_hbP`), so no `n` in it has `d ∣ n(n+2)`. -/
theorem hbDataN8_S_eq_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z : ℕ} (hz : 2 ≤ z) (x : ℕ) {d : ℕ}
    (hd : d ∣ (hbDataN8 χ hsq hz x).P) (h1 : 1 < d) :
    (hbDataN8 χ hsq hz x).S d = 0 := by
  classical
  rw [hbDataN8_P] at hd
  refine Finset.sum_eq_zero ?_
  intro n hn
  exfalso
  rw [Finset.mem_filter] at hn
  obtain ⟨hnw, hdvd⟩ := hn
  have hcop : Nat.Coprime (n * (n + 2)) (hbP (chiReChar χ hsq) (z : ℝ)) :=
    l2cWindow_coprime_hbP χ hsq z x n hnw
  have hg : d ∣ Nat.gcd (n * (n + 2)) (hbP (chiReChar χ hsq) (z : ℝ)) :=
    Nat.dvd_gcd hdvd hd
  rw [Nat.Coprime] at hcop
  rw [hcop] at hg
  have := Nat.le_of_dvd one_pos hg
  omega


/-- **THE SIEVE IS THE IDENTITY ON THE N8 WIRE.**  Both sides of HB's sandwich (2.2)
collapse to `S⁽³⁾` itself: every `S(d)`, `d > 1`, vanishes, and `λ_1 = 1`.  This is the
kernel's record of why the wire is re-cut: the sieve interface is generic in its data, and
on THIS data both Rosser sides are `S⁽³⁾` itself.  Its hypotheses (`∀ Lam`, `side ≤ 2`,
`1 ≤ b`) cover every crown call site. -/
theorem lamSum_S_eq_S3 {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z : ℕ} (hz : 2 ≤ z) (x : ℕ) {Lam : ℝ} {side b : ℕ}
    (hb : 1 ≤ b) (hside : side ≤ 2) :
    lamSum Lam (hbDataN8 χ hsq hz x).z side b (hbDataN8 χ hsq hz x).P
        (hbDataN8 χ hsq hz x).S
      = (hbDataN8 χ hsq hz x).S3 := by
  classical
  set H := hbDataN8 χ hsq hz x with hH
  have hP0 : H.P ≠ 0 := H.P_squarefree.ne_zero
  have hstep : lamSum Lam H.z side b H.P H.S
      = ∑ d ∈ H.P.divisors, (if d = 1 then H.S 1 else 0) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases h1 : d = 1
    · subst h1
      simp [lamBB, chi_one Lam H.z hb hside]
    · have hdvd : d ∣ H.P := Nat.dvd_of_mem_divisors hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      have hd1 : 1 < d := by omega
      rw [hbDataN8_S_eq_zero χ hsq hz x (hH ▸ hdvd) hd1, if_neg h1, mul_zero]
  rw [hstep, Finset.sum_ite_eq' H.P.divisors 1 (fun _ => H.S 1),
    if_pos (Nat.one_mem_divisors.mpr hP0)]
  -- `S(1)` is the whole window; `S⁽³⁾` is too (the `(l,P)=1` filter is vacuous)
  have hS1 : H.S 1 = ∑ n ∈ l2cWindow χ z x, LamStar χ z n * LamStar χ z (n + 2) := by
    change ∑ n ∈ (l2cWindow χ z x).filter (fun n => 1 ∣ n * (n + 2)), _ = _
    rw [Finset.filter_true_of_mem (fun n _ => one_dvd _)]
    rfl
  have hS3 : H.S3 = ∑ n ∈ l2cWindow χ z x, LamStar χ z n * LamStar χ z (n + 2) := by
    change ∑ n ∈ (l2cWindow χ z x).filter
      (fun n => Nat.Coprime (n * (n + 2)) (hbP (chiReChar χ hsq) (z : ℝ))), _ = _
    rw [Finset.filter_true_of_mem (l2cWindow_coprime_hbP χ hsq z x)]
    rfl
  rw [hS1, hS3]

end Salt.HB
