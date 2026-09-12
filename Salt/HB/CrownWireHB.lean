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

**§1 (THIS CUT): THE HB WIRE.**  `hbDataHB` — Heath-Brown's own Lemma 5 instance, for the
twin pair `(4k+1, 4k+3)` over the k-range `(x, 2x]`, whose modulus is NOT already divided out
by its own support.  **§2 (THIS CUT): THE BRIDGE** from that wire back to the crown window at
`X = 4x+1`, along the index map `k ↦ 4k+1`.  **§3 is RESERVED for the next cut and is NOT in
this file yet:** the p.200 lower assembly re-stated at the HB wire.

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

variable {q : ℕ}

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

/-! ## §1 — THE HB WIRE: HEATH-BROWN'S OWN INSTANCE, FOR THE PAIR `(4k+1, 4k+3)` -/

/-- **W-a.1 — THE HB WIRE.**  The `HBSieveData` at Heath-Brown's own Lemma 5 instance for the
twin pair `(4k+1, 4k+3)` (p. 195; the normalisation (1.3)–(1.9) at `α = (4,4)`, `β = (1,3)`):
character `chiReChar χ hsq`, modulus `hbP`, `support := {k ∈ (x, 2x] : ((4k+1)(4k+3), q) = 1}`,
`val k = (4k+1)(4k+3)`, `a k = Λ*(4k+1)·Λ*(4k+3)` with HB's Lemma 1 (`LamStar_nonneg`, twice)
discharging `ofHbP`'s one obligation `a_nonneg`.  **The contrast with `hbDataN8` (§0) is the
point of the re-cut:** there the support had already removed every prime the sieve sifts by,
so the sieve was the identity on it; here the modulus is not divided out by the support.  The
support's predicate is decidable exactly as `l2cWindow`'s is.  Class **A**, cap 25.  Consumers:
`hbDataHB_S3_le_S3_window`, `hbS1_eq_W_HB`, `hb_p200_lower_HB`. -/
noncomputable def hbDataHB (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 2 ≤ z) (x : ℕ) : HBSieveData :=
  HBSieveData.ofHbP (chiReChar χ hsq) (z := (z : ℝ)) (by exact_mod_cast hz)
    ((Finset.Ioc x (2 * x)).filter (fun k => Nat.Coprime ((4 * k + 1) * (4 * k + 3)) q))
    (fun k => (4 * k + 1) * (4 * k + 3))
    (fun k => LamStar χ z (4 * k + 1) * LamStar χ z (4 * k + 3))
    (fun k _ => mul_nonneg (LamStar_nonneg χ hsq z (4 * k + 1))
      (LamStar_nonneg χ hsq z (4 * k + 3)))

/-- **W-a.2 — the modulus did not move.**  `ofHbP` builds a wire's `P` from the character and
`z` alone, so the HB wire sifts by the same `hbP` the N8 wire does; what moved is the support,
the value and the weight.  Class **A**, cap 15 (with its sibling below).  By `rfl`.  Consumer:
`hb_p200_lower_HB`'s `hPα` binder, and every `.P` read on the crown path. -/
theorem hbDataHB_P (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℕ) : (hbDataHB χ hsq hz x).P = hbP (chiReChar χ hsq) (z : ℝ) := rfl

/-- **W-a.2 — `S⁽³⁾` unfolded at the HB wire.**  The weight sum over the k-range, filtered
twice: by `((4k+1)(4k+3), q) = 1` (the support's own condition) and by
`((4k+1)(4k+3), P) = 1` (the sieve's) — HB's `(l, qP) = 1` read at the pair.  Class **A**,
cap 15 (with its sibling above).  By `rfl`.  Consumer: `hbDataHB_S3_le_S3_window`, which
rewrites the bridge's left-hand side through this equation. -/
theorem hbDataHB_S3_eq (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℕ) :
    (hbDataHB χ hsq hz x).S3
      = ∑ k ∈ ((Finset.Ioc x (2 * x)).filter
            (fun k => Nat.Coprime ((4 * k + 1) * (4 * k + 3)) q)).filter
            (fun k => Nat.Coprime ((4 * k + 1) * (4 * k + 3)) (hbP (chiReChar χ hsq) (z : ℝ))),
          LamStar χ z (4 * k + 1) * LamStar χ z (4 * k + 3) := rfl

/-! ## §2 — THE BRIDGE: FROM THE HB WIRE BACK TO THE CROWN WINDOW AT `X = 4x+1` -/

/-- **W-c₁.1 — the index map lands inside the crown window.**  The image of `(x, 2x]` under
`k ↦ 4k+1` is `[4x+5, 8x+1]`, and the crown window's index range at `X = 4x+1` is
`(4x+1, 8x+2]`: both boundaries clear, so no membership side condition survives into the
bridge.  Class **A**, cap 6.  Red-first: `Finset.mem_Ioc` and `omega`.  Consumer:
`hbDataHB_S3_le_S3_window`. -/
theorem four_mul_add_one_mem_Ioc {x k : ℕ} (hk : k ∈ Finset.Ioc x (2 * x)) :
    4 * k + 1 ∈ Finset.Ioc (4 * x + 1) (2 * (4 * x + 1)) := by
  simp only [Finset.mem_Ioc] at hk ⊢; omega

/-- **W-c₁.2 — an odd `m` coprime to `q` and to the sieve's modulus is coprime to the
primorial.**  `excPrimorial χ z` is the product over the primes `p < z` with `χ_ℝ(p) ≠ −1`, so
the trichotomy leaves two values per factor, and each is discharged from a DIFFERENT
hypothesis: `χ_ℝ(p) = 0` gives `p ∣ q`, closed by `hq`; `χ_ℝ(p) = +1` with `2 < p` puts `p` in
`hbSiftSet`, hence `p ∣ hbP`, closed by `hP`; and `p = 2` is closed by `hodd` alone.  All
three hypotheses are load-bearing.  Class **A**, cap 40 (24 lines bare).  Red-first:
`Nat.Coprime.prod_right`, then the trichotomy and `Nat.lt_or_ge 2 p`.  Consumer:
`hbDataHB_S3_le_S3_window`, at `m = (4k+1)(4k+3)`. -/
theorem coprime_excPrimorial_of_odd (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ)
    {m : ℕ} (hodd : ¬ 2 ∣ m) (hq : Nat.Coprime m q)
    (hP : Nat.Coprime m (hbP (chiReChar χ hsq) (z : ℝ))) :
    Nat.Coprime m (excPrimorial χ z) := by
  classical
  rw [excPrimorial]
  refine Nat.Coprime.prod_right ?_
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpz, hpp, hchi⟩ := hp
  rcases chiRe_eq_one_or_neg_one_or_zero χ hsq p with h1 | hm1 | h0
  · rcases Nat.lt_or_ge 2 p with h2 | h2
    · have hmem : p ∈ hbSiftSet (chiReChar χ hsq) (z : ℝ) := by
        rw [hbSiftSet_chiReChar]
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpz, hpp, h2, h1⟩
      have hdvd : p ∣ hbP (chiReChar χ hsq) (z : ℝ) := by
        rw [hbP]; exact Finset.dvd_prod_of_mem (fun p => p) hmem
      exact Nat.Coprime.coprime_dvd_right hdvd hP
    · have hp2 : p = 2 := le_antisymm h2 hpp.two_le
      subst hp2
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
  · exact absurd hm1 hchi
  · exact Nat.Coprime.coprime_dvd_right
      ((chiRe_prime_eq_zero_iff_dvd χ hsq hpp).mp h0) hq

/-- **W-c₁.3 — THE BRIDGE.**  The HB wire's sifted sum is bounded by the crown window's at
`X = 4x+1`.  The k-indexed sum is carried to the n-indexed one along the injection
`k ↦ 4k+1` (`Finset.sum_image`, whose `Set.InjOn` side condition is `omega`); the image lands
in `l2cWindow χ z (4x+1)` by `four_mul_add_one_mem_Ioc` for the range and by
`Nat.Coprime.mul_right` of the support's own `(·, q) = 1` with `coprime_excPrimorial_of_odd`
for the rest, whose oddness input is `(4k+1)(4k+3) ≡ 1 mod 2`.  `4k+1+2` and `4k+3` are
definitionally equal, so nothing is rewritten there.  Every crown term the image misses is
`≥ 0`.  This is the ONE inequality through which the crown consumes the new wire.  Class
**A**, cap 50 (33 lines bare).  Consumer: the next cut, where the crown's `S⁽³⁾` step becomes
one-sided. -/
theorem hbDataHB_S3_le_S3_window (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 2 ≤ z) (x : ℕ) :
    (hbDataHB χ hsq hz x).S3 ≤ S3 χ z (l2cWindow χ z (4 * x + 1)) := by
  classical
  have key : ∀ T : Finset ℕ, (∀ k ∈ T, 4 * k + 1 ∈ l2cWindow χ z (4 * x + 1)) →
      ∑ k ∈ T, LamStar χ z (4 * k + 1) * LamStar χ z (4 * k + 3)
        ≤ S3 χ z (l2cWindow χ z (4 * x + 1)) := by
    intro T hT
    have hinj : Set.InjOn (fun k : ℕ => 4 * k + 1) (T : Set ℕ) := by
      intro a _ b _ h
      have h' : 4 * a + 1 = 4 * b + 1 := h
      omega
    have himg : ∑ n ∈ T.image (fun k => 4 * k + 1), LamStar χ z n * LamStar χ z (n + 2)
        = ∑ k ∈ T, LamStar χ z (4 * k + 1) * LamStar χ z (4 * k + 3) :=
      Finset.sum_image hinj
    change _ ≤ ∑ n ∈ l2cWindow χ z (4 * x + 1), LamStar χ z n * LamStar χ z (n + 2)
    rw [← himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ =>
      mul_nonneg (LamStar_nonneg χ hsq z n) (LamStar_nonneg χ hsq z (n + 2)))
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    exact hT k hk
  rw [hbDataHB_S3_eq]
  refine key _ (fun k hk => ?_)
  obtain ⟨hk1, hkP⟩ := Finset.mem_filter.mp hk
  obtain ⟨hkIoc, hkq⟩ := Finset.mem_filter.mp hk1
  have hodd : ¬ 2 ∣ (4 * k + 1) * (4 * k + 3) := by
    have hmod : ((4 * k + 1) * (4 * k + 3)) % 2 = 1 := by
      rw [Nat.mul_mod, show (4 * k + 1) % 2 = 1 from by omega,
        show (4 * k + 3) % 2 = 1 from by omega]
    omega
  exact Finset.mem_filter.mpr ⟨four_mul_add_one_mem_Ioc hkIoc,
    Nat.Coprime.mul_right hkq (coprime_excPrimorial_of_odd χ hsq z hodd hkq hkP)⟩

end Salt.HB
