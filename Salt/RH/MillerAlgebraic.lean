/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.Targets

/-!
# O106 row R5a — Miller's algebraic half (unconditional)

For an odd composite `n`, every unit that passes the strong probable-prime test lies in ONE
proper subgroup of `(ZMod n)ˣ` (`MillerAlgebraic`, stated in `Salt.RH.Targets`). This is the
half of Miller's theorem that needs no hypothesis: GRH enters only through `SmallNonMember`,
which supplies a small unit outside any such subgroup.

## Route

Write `n − 1 = 2^s · d` with `d` odd.
* **`n = p^e` with `e ≥ 2`.** The subgroup is the Fermat-liar group `{u | u^(n−1) = 1}`. Every
  strong liar is a Fermat liar. It is proper: `(ZMod p^e)ˣ` is cyclic (`p` odd) of order
  `p^(e−1)(p − 1)`, so if every unit had `u^(n−1) = 1` then `p ∣ n − 1`, while `p ∣ n`.
* **`n` not a prime power.** Split `n = m₁ m₂` with `m₁ = p^k` the full power of `p = minFac n`,
  so the two factors are coprime and both are `> 1`. Let `k` be the LARGEST `r < s` at which some
  unit has `u^(2^r d) = −1` (`r = 0` qualifies through `u = −1`, since `d` is odd). The subgroup
  is `{u | u^(2^k d) = ±1}`. A strong liar lands in it by the maximality of `k`. It is proper:
  take `b` with `b^(2^k d) = −1` and, by the Chinese remainder theorem, the unit `x ≡ b (m₁)`,
  `x ≡ 1 (m₂)`. Then `x^(2^k d) ≡ −1 (m₁)` and `≡ 1 (m₂)`, which is neither `1` nor `−1`.
-/

namespace Salt.RH

/-- The 2-adic exponent `s` of `n − 1`. -/
abbrev sprS (n : ℕ) : ℕ := (n - 1).factorization 2

/-- The odd part `d` of `n − 1`. -/
abbrev sprD (n : ℕ) : ℕ := (n - 1) / 2 ^ sprS n

theorem two_pow_mul_sprD (n : ℕ) : 2 ^ sprS n * sprD n = n - 1 :=
  Nat.ordProj_mul_ordCompl_eq_self (n - 1) 2

theorem sprD_odd {n : ℕ} (h3 : 3 ≤ n) : Odd (sprD n) :=
  Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (by omega))

theorem sprS_pos {n : ℕ} (h3 : 3 ≤ n) (hodd : Odd n) : 0 < sprS n := by
  have h2 : 2 ∣ n - 1 := by
    obtain ⟨k, rfl⟩ := hodd
    exact ⟨k, by omega⟩
  exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two (by omega)).mp h2

/-- A strong liar is a Fermat liar. -/
theorem pow_sub_one_eq_one_of_spp {n : ℕ} {x : ZMod n}
    (h : x ^ sprD n = 1 ∨ ∃ r < sprS n, x ^ (2 ^ r * sprD n) = -1) :
    x ^ (n - 1) = 1 := by
  rw [← two_pow_mul_sprD n]
  rcases h with h | ⟨r, hr, h⟩
  · rw [mul_comm, pow_mul, h, one_pow]
  · obtain ⟨t, ht⟩ : ∃ t, sprS n = r + 1 + t := ⟨sprS n - r - 1, by omega⟩
    have he : 2 ^ sprS n * sprD n = (2 ^ r * sprD n) * 2 * 2 ^ t := by
      rw [ht, pow_add, pow_add, pow_one]; ring
    rw [he, pow_mul, pow_mul, h, neg_one_sq, one_pow]

/-- The test at the natural number `u.val` is the test at the unit `u`. -/
theorem spp_val_iff {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) :
    StrongProbablePrime n (u : ZMod n).val ↔
      ((u : ZMod n) ^ sprD n = 1 ∨ ∃ r < sprS n, (u : ZMod n) ^ (2 ^ r * sprD n) = -1) := by
  unfold StrongProbablePrime
  rw [ZMod.natCast_zmod_val]

/-! ## Case 1 — `n = p^e`, `e ≥ 2` -/

theorem millerAlgebraic_primePow {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 2 ≤ e) :
    ∃ H : Subgroup (ZMod (p ^ e))ˣ, H ≠ ⊤ ∧
      ∀ u : (ZMod (p ^ e))ˣ, StrongProbablePrime (p ^ e) (u : ZMod (p ^ e)).val → u ∈ H := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  set n := p ^ e with hn
  refine ⟨(powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker, ?_, ?_⟩
  · intro htop
    have hall : ∀ u : (ZMod n)ˣ, u ^ (n - 1) = 1 := by
      intro u
      have : u ∈ (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker := by
        rw [htop]; exact Subgroup.mem_top u
      simpa using this
    haveI : IsCyclic (ZMod n)ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
    have hexp : Monoid.exponent (ZMod n)ˣ ∣ n - 1 := Monoid.exponent_dvd_of_forall_pow_eq_one hall
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      hn, Nat.totient_prime_pow hp (by omega)] at hexp
    have hpd : p ∣ p ^ e - 1 :=
      (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) (p - 1)).trans hexp
    have hpn : p ∣ p ^ e := dvd_pow_self p (by omega)
    have h1 : p ∣ 1 := by
      have := Nat.dvd_sub hpn hpd
      have hpos : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
      rwa [show p ^ e - (p ^ e - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  · intro u hu
    rw [spp_val_iff] at hu
    have h := pow_sub_one_eq_one_of_spp hu
    simp only [MonoidHom.mem_ker, powMonoidHom_apply]
    ext
    simpa using h

/-! ## Case 2 — `n` is not a prime power -/

/-- The subgroup `{1, −1}` of the units. -/
def pmOne (R : Type*) [CommRing R] : Subgroup Rˣ where
  carrier := {x | x = 1 ∨ x = -1}
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro a (rfl | rfl) <;> simp

theorem mem_pmOne {R : Type*} [CommRing R] (x : Rˣ) : x ∈ pmOne R ↔ x = 1 ∨ x = -1 := Iff.rfl

theorem millerAlgebraic_coprime {m₁ m₂ : ℕ} (hco : m₁.Coprime m₂) (h1 : 3 ≤ m₁) (h2 : 3 ≤ m₂)
    (hodd : Odd (m₁ * m₂)) :
    ∃ H : Subgroup (ZMod (m₁ * m₂))ˣ, H ≠ ⊤ ∧
      ∀ u : (ZMod (m₁ * m₂))ˣ,
        StrongProbablePrime (m₁ * m₂) (u : ZMod (m₁ * m₂)).val → u ∈ H := by
  set n := m₁ * m₂ with hn
  have h3 : 3 ≤ n := by rw [hn]; nlinarith
  haveI : NeZero n := ⟨by omega⟩
  set S := sprS n
  set d := sprD n
  have hd : Odd d := sprD_odd h3
  have hS : 0 < S := sprS_pos h3 hodd
  classical
  -- the largest `r < S` at which some unit reaches `−1`
  let P : ℕ → Prop := fun r => r < S ∧ ∃ u : (ZMod n)ˣ, (u : ZMod n) ^ (2 ^ r * d) = -1
  have hP0 : P 0 := ⟨hS, -1, by simp [hd.neg_one_pow]⟩
  set k := Nat.findGreatest P (S - 1) with hk
  have hPk : P k := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hmax : ∀ r, P r → r ≤ k := fun r hr => Nat.le_findGreatest (by have := hr.1; omega) hr
  obtain ⟨_, b, hb⟩ := hPk
  let H : Subgroup (ZMod n)ˣ := (pmOne (ZMod n)).comap (powMonoidHom (2 ^ k * d))
  refine ⟨H, ?_, ?_⟩
  · -- proper: the CRT unit `x ≡ b (m₁)`, `x ≡ 1 (m₂)`
    intro htop
    let e : ZMod n ≃+* ZMod m₁ × ZMod m₂ := ZMod.chineseRemainder hco
    let bp : (ZMod m₁)ˣ × (ZMod m₂)ˣ := MulEquiv.prodUnits (Units.map e.toMonoidHom b)
    let x : (ZMod n)ˣ :=
      Units.map e.symm.toMonoidHom (MulEquiv.prodUnits.symm (bp.1, 1))
    have hx : e ((x : ZMod n) ^ (2 ^ k * d)) = (-1, 1) := by
      have hb' : e ((b : ZMod n) ^ (2 ^ k * d)) = (-1, -1) := by
        rw [hb, map_neg, map_one]; rfl
      have hex : e (x : ZMod n) = ((e (b : ZMod n)).1, 1) := by
        simp [x, bp, MulEquiv.prodUnits]
      have h1 : (e (b : ZMod n)).1 ^ (2 ^ k * d) = -1 := by
        rw [map_pow] at hb'
        have := congrArg Prod.fst hb'
        simpa using this
      rw [map_pow, hex, Prod.pow_mk, one_pow, h1]
    have hxH : x ∈ H := by rw [htop]; exact Subgroup.mem_top x
    have hxH' : x ^ (2 ^ k * d) = 1 ∨ x ^ (2 ^ k * d) = -1 := hxH
    haveI : Fact (2 < m₁) := ⟨by omega⟩
    haveI : Fact (2 < m₂) := ⟨by omega⟩
    rcases hxH' with h | h
    · have hv : (x : ZMod n) ^ (2 ^ k * d) = 1 := by
        have := congrArg Units.val h; simpa using this
      rw [hv, map_one] at hx
      have := congrArg Prod.fst hx
      exact ZMod.neg_one_ne_one this.symm
    · have hv : (x : ZMod n) ^ (2 ^ k * d) = -1 := by
        have := congrArg Units.val h; simpa using this
      rw [hv, map_neg, map_one] at hx
      have := congrArg Prod.snd hx
      exact ZMod.neg_one_ne_one (by simpa using this)
  · -- every strong liar is in `H`, by the maximality of `k`
    intro u hu
    rw [spp_val_iff] at hu
    change u ^ (2 ^ k * d) ∈ pmOne (ZMod n)
    rw [mem_pmOne]
    rcases hu with h | ⟨r, hr, h⟩
    · left
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one]
      rw [mul_comm, pow_mul, h, one_pow]
    · have hrk : r ≤ k := hmax r ⟨hr, u, h⟩
      rcases Nat.eq_or_lt_of_le hrk with rfl | hlt
      · right
        ext
        simpa using h
      · left
        ext
        obtain ⟨t, ht⟩ : ∃ t, k = r + 1 + t := ⟨k - r - 1, by omega⟩
        have he : 2 ^ k * d = (2 ^ r * d) * 2 * 2 ^ t := by
          rw [ht, pow_add, pow_add, pow_one]; ring
        simp only [Units.val_pow_eq_pow_val, Units.val_one]
        rw [he, pow_mul, pow_mul, h, neg_one_sq, one_pow]

/-! ## The theorem -/

/-- **R5a: Miller's algebraic half.** For odd composite `n ≥ 3`, the strong liars lie in a proper
subgroup of `(ZMod n)ˣ`. -/
theorem millerAlgebraic : MillerAlgebraic := by
  intro n h3 hodd hnp
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, e, hp, he0, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have he : 2 ≤ e := by
      by_contra h
      have : e = 1 := by omega
      subst this
      exact hnp (by simpa using hp)
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (by
        exact (Nat.even_pow.mpr ⟨even_two, by omega⟩))
    exact millerAlgebraic_primePow hp hp2 he
  · set p := n.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    set m₁ := p ^ n.factorization p with hm₁
    set m₂ := n / m₁ with hm₂
    have hmul : m₁ * m₂ = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hco : m₁.Coprime m₂ :=
      Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp (by omega))
    have hk : 1 ≤ n.factorization p :=
      (hp.dvd_iff_one_le_factorization (by omega)).mp (Nat.minFac_dvd n)
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      rcases Nat.eq_or_lt_of_le h2 with h | h
      · exfalso
        have : 2 ∣ n := by rw [h]; exact Nat.minFac_dvd n
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
      · omega
    have hm₁3 : 3 ≤ m₁ := le_trans hp3 (by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ m₁ := Nat.pow_le_pow_right hp.pos hk)
    have hm₂pos : 0 < m₂ := by
      rcases Nat.eq_zero_or_pos m₂ with h | h
      · rw [h, mul_zero] at hmul; omega
      · exact h
    have hm₂1 : m₂ ≠ 1 := by
      intro h
      apply hpp
      rw [← hmul, h, mul_one]
      exact (isPrimePow_nat_iff _).mpr ⟨p, _, hp, hk, rfl⟩
    have hm₂odd : Odd m₂ := by
      rw [← hmul] at hodd
      exact (Nat.odd_mul.mp hodd).2
    have hm₂3 : 3 ≤ m₂ := by
      obtain ⟨j, hj⟩ := hm₂odd
      omega
    have := millerAlgebraic_coprime hco hm₁3 hm₂3 (by rw [hmul]; exact hodd)
    rw [hmul] at this
    exact this

end Salt.RH
