/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.EstermannGlobal
import Salt.Weil.RoadModulus

/-!
# The Estermann 2-adic discharge — (7.1) with NO 2-adic factor, for `v₂(k) ≤ 8`

`Salt.Weil.EstermannGlobal` lands the composite Estermann bound

`‖S(a,b;k)‖ ≤ 2^{v₂(k)/2} · d(k) · √k · √(k,a,b)`

with the 2-adic factor `2^{v₂(k)/2}` carried **explicitly**.  Heath-Brown's (7.1)
(`docs/sources/hb1983-notes.md`) has **no such factor**.  `Salt/Certs/Kloosterman.lean:48`
records the residue in as many words: *"The 2-adic factor is stated, never discharged."*

This module discharges it, on a hypothesis that is a plain valuation bound.

## 🔑 The finding: the 2-part needs no square-root saving at all

At the 2-part the trivial bound `‖S(a,b;2^e)‖ ≤ #(ZMod 2^e)ˣ = φ(2^e) = 2^{e-1}` already
beats `d(2^e)·√(2^e) = (e+1)·2^{e/2}` — but **only while `e ≤ 8`**, because `2^{e-1}` grows
geometrically and `(e+1)·2^{e/2}` does not.  `two_pow_totient_le_estermann` is that
comparison and `norm_kloosterman_two_pow_estermann` is the bound it buys; the odd part is
already factor-free in `norm_kloosterman_estermann_nat` (its 2-adic exponent is `0`), so the
CRT glue of the two is (7.1) verbatim, constant `1`.

⚠️ **The hypothesis `e ≤ 8` is not slack that could be removed by working harder** — the
method is exhausted at `e = 9`.  The witness is `Salt.HB.two_pow_totient_exceeds_estermann_at_nine`
in `Salt/HB/EstermannRoad.lean`, which is a **NEGATIVE control** and is fenced there.

## The rows

* `two_pow_totient_le_estermann` (D1′) — `φ(2^e) ≤ d(2^e)·√(2^e)` for `e ≤ 8`.
* `norm_kloosterman_two_pow_estermann` (D1) — the 2-part row, factor-free.
* `norm_kloosterman_estermann_nat_of_v2_le` (D2) — the global bound, nat arguments.
* `norm_kloosterman_estermann_of_v2_le` (D3) — the same, `ZMod` arguments.  **HB (7.1)
  verbatim.**
* `norm_kloosterman_estermann_road_clean` (D4) — the close on the §5 road modulus
  `k = D·δ₁·w₁`, `D = roadModulus α₂ q`, whose 2-part is `max (v₂ α₂) (v₂ q)`.

📌 **The hypothesis set here is STRICTLY LARGER than the one the road consumes.**  The road
supplies `v₂(q) ≤ 3` (`Salt.HB.factorization_two_le_three_of_isPrimitive`); these rows are
stated at `≤ 8` because that is where the *method* stops, not where the *consumer* stops.
The two numbers are deliberately not collapsed: `8` is a fact about this proof, `3` is a fact
about primitive real characters, and a reader who sees only one of them cannot tell how much
room the discharge has.
-/

namespace Salt.Weil

/-- **D1′.**  For `e ≤ 8`, Euler's totient of `2 ^ e` is at most the Estermann shape
`d(2^e) · √(2^e)`.  This is the whole 2-adic content: past `e = 8` it is FALSE. -/
theorem two_pow_totient_le_estermann {e : ℕ} (he : e ≤ 8) :
    (((2 ^ e : ℕ).totient : ℕ) : ℝ)
      ≤ (((2 ^ e : ℕ).divisors.card : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ e) := by
  have hdiv : ((2 ^ e : ℕ).divisors.card) = e + 1 := by
    first
      | simp [Nat.card_divisors_prime_pow Nat.prime_two]
      | (rw [Nat.divisors_prime_pow Nat.prime_two]; simp)
  rw [hdiv]
  set s := Real.sqrt ((2 : ℝ) ^ e) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hss : s * s = (2 : ℝ) ^ e := Real.mul_self_sqrt (by positivity)
  have key : ∀ x c : ℝ, 0 ≤ x → 0 ≤ c → x * x ≤ (c * c) * (2 : ℝ) ^ e → x ≤ c * s := by
    intro x c hx hc hxc
    by_contra hcon0
    -- `push_neg` is deprecated in this mathlib; the same step, warning-free
    have hcon : c * s < x := not_le.mp hcon0
    have h1 : (c * s) * (c * s) < x * x := mul_self_lt_mul_self (by positivity) hcon
    have h2 : (c * s) * (c * s) = (c * c) * (2 : ℝ) ^ e := by rw [← hss]; ring
    rw [h2] at h1
    linarith
  rcases Nat.eq_zero_or_pos e with rfl | he1
  · norm_num [hsdef]
  · have htot : ((2 ^ e : ℕ).totient) = 2 ^ (e - 1) := by
      rw [Nat.totient_prime_pow Nat.prime_two he1]; simp
    rw [htot]
    refine key _ _ (by positivity) (by positivity) ?_
    have hcast : (((2 ^ (e - 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (e - 1) := by push_cast; ring
    rw [hcast]
    have hnum : (2 : ℝ) ^ (e - 1) * (2 : ℝ) ^ (e - 1)
        ≤ ((((e + 1 : ℕ)) : ℝ) * (((e + 1 : ℕ)) : ℝ)) * (2 : ℝ) ^ e := by
      interval_cases e <;> norm_num
    exact hnum

/-- **D1 — the 2-part row, factor-free, for `e ≤ 8`.**  The trivial bound
`‖S(a,b;2^e)‖ ≤ φ(2^e)` composed with D1′; the gcd factor is carried as slack (`≥ 1`). -/
theorem norm_kloosterman_two_pow_estermann {e : ℕ} [NeZero (2 ^ e)] (he : e ≤ 8) (A B : ℕ) :
    ‖kloosterman ((A : ℕ) : ZMod (2 ^ e)) ((B : ℕ) : ZMod (2 ^ e))‖
      ≤ (((2 ^ e : ℕ).divisors.card : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ e)
          * Real.sqrt ((Nat.gcd (2 ^ e) (Nat.gcd A B) : ℕ) : ℝ) := by
  have h1 := norm_kloosterman_le ((A : ℕ) : ZMod (2 ^ e)) ((B : ℕ) : ZMod (2 ^ e))
  rw [ZMod.card_units_eq_totient] at h1
  refine h1.trans ?_
  have h2 := two_pow_totient_le_estermann (e := e) he
  have hgpos : 0 < Nat.gcd (2 ^ e) (Nat.gcd A B) :=
    Nat.pos_of_ne_zero fun hz => (pow_ne_zero e (two_ne_zero)) (Nat.gcd_eq_zero_iff.mp hz).1
  have hg : (1 : ℝ) ≤ Real.sqrt ((Nat.gcd (2 ^ e) (Nat.gcd A B) : ℕ) : ℝ) := by
    have h := Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ ((Nat.gcd (2 ^ e) (Nat.gcd A B) : ℕ) : ℝ) by exact_mod_cast hgpos)
    simpa using h
  have hprod0 : (0 : ℝ) ≤ (((2 ^ e : ℕ).divisors.card : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ e) := by
    positivity
  nlinarith [h2, hg, hprod0]

/-- **D2 — the factor-free global bound under `v₂(k) ≤ 8` (nat form).**  Splits `k = 2^κ·m`
with `m` odd, applies D1 to the 2-part and the LANDED global bound to the odd part (where the
2-adic factor is already `1`), then glues by twisted multiplicativity.  The constant is
exactly multiplicative — `d`, `√·` and the gcd datum all factor across the coprime split. -/
theorem norm_kloosterman_estermann_nat_of_v2_le (k : ℕ) [NeZero k]
    (hk : k.factorization 2 ≤ 8) (A B : ℕ) :
    ‖kloosterman ((A : ℕ) : ZMod k) ((B : ℕ) : ZMod k)‖
      ≤ (k.divisors.card : ℝ) * Real.sqrt (k : ℝ)
          * Real.sqrt ((Nat.gcd k (Nat.gcd A B) : ℕ) : ℝ) := by
  obtain ⟨κ, m, hodd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne k) 2 (by norm_num)
  haveI : NeZero m := ⟨by rintro rfl; exact hodd (dvd_zero 2)⟩
  haveI : NeZero (2 ^ κ) := ⟨pow_ne_zero κ two_ne_zero⟩
  have hm0 : m ≠ 0 := NeZero.ne m
  have hcop : Nat.Coprime (2 ^ κ) m :=
    Nat.Coprime.pow_left κ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  -- the hypothesis reads `κ ≤ 8`
  have hfac : ((2 ^ κ * m : ℕ).factorization) 2 = κ := by
    rw [Nat.factorization_mul (by positivity) hm0]
    simp [Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hodd]
  rw [hfac] at hk
  -- the coprime glue, done ONCE
  obtain ⟨l₁, l₂, hu₁, hu₂, hmul⟩ :=
    kloosterman_mul_of_coprime_unit_twist hcop ((A : ℕ) : ZMod (2 ^ κ * m))
      ((B : ℕ) : ZMod (2 ^ κ * m))
  obtain ⟨A₁, B₁, hA₁, hB₁, hg₁⟩ := gcd_unit_twist_nat hu₁ A B
  obtain ⟨A₂, B₂, hA₂, hB₂, hg₂⟩ := gcd_unit_twist_nat hu₂ A B
  rw [hmul, natCast_chineseRemainder_fst, natCast_chineseRemainder_fst,
    natCast_chineseRemainder_snd, natCast_chineseRemainder_snd, hA₁, hB₁, hA₂, hB₂, norm_mul]
  set g := Nat.gcd A B with hgdef
  -- factor 1: the 2-part, by D1
  have hb₁ : ‖kloosterman ((A₁ : ℕ) : ZMod (2 ^ κ)) ((B₁ : ℕ) : ZMod (2 ^ κ))‖
      ≤ (((2 ^ κ : ℕ).divisors.card : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ κ)
          * Real.sqrt ((Nat.gcd (2 ^ κ) g : ℕ) : ℝ) := by
    refine (norm_kloosterman_two_pow_estermann hk A₁ B₁).trans ?_
    have hle : ((Nat.gcd (2 ^ κ) (Nat.gcd A₁ B₁) : ℕ) : ℝ) ≤ ((Nat.gcd (2 ^ κ) g : ℕ) : ℝ) := by
      have : Nat.gcd (2 ^ κ) (Nat.gcd A₁ B₁) ≤ Nat.gcd (2 ^ κ) g :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero fun hz =>
          (NeZero.ne (2 ^ κ)) (Nat.gcd_eq_zero_iff.mp hz).1) hg₁
      exact_mod_cast this
    have hsq := Real.sqrt_le_sqrt hle
    have h0 : (0 : ℝ) ≤ (((2 ^ κ : ℕ).divisors.card : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ κ) := by
      positivity
    exact mul_le_mul_of_nonneg_left hsq h0
  -- factor 2: the odd part, by the LANDED global bound (its 2-adic factor is `1`)
  have hb₂ : ‖kloosterman ((A₂ : ℕ) : ZMod m) ((B₂ : ℕ) : ZMod m)‖
      ≤ (m.divisors.card : ℝ) * Real.sqrt (m : ℝ) * Real.sqrt ((Nat.gcd m g : ℕ) : ℝ) := by
    have h := norm_kloosterman_estermann_nat m A₂ B₂
    have hm2 : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hodd
    rw [hm2] at h
    simp only [pow_zero, Real.sqrt_one, one_mul] at h
    refine h.trans ?_
    have hle : ((Nat.gcd m (Nat.gcd A₂ B₂) : ℕ) : ℝ) ≤ ((Nat.gcd m g : ℕ) : ℝ) := by
      have : Nat.gcd m (Nat.gcd A₂ B₂) ≤ Nat.gcd m g :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero fun hz =>
          hm0 (Nat.gcd_eq_zero_iff.mp hz).1) hg₂
      exact_mod_cast this
    have hsq := Real.sqrt_le_sqrt hle
    have h0 : (0 : ℝ) ≤ (m.divisors.card : ℝ) * Real.sqrt (m : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hsq h0
  -- multiply
  have hstep := mul_le_mul hb₁ hb₂ (norm_nonneg _) (by positivity)
  refine hstep.trans ?_
  -- the constant is exactly multiplicative
  have hcard : ((2 ^ κ * m : ℕ).divisors.card) = (2 ^ κ : ℕ).divisors.card * m.divisors.card :=
    Nat.Coprime.card_divisors_mul hcop
  have hsqrtk : Real.sqrt ((2 ^ κ * m : ℕ) : ℝ)
      = Real.sqrt ((2 : ℝ) ^ κ) * Real.sqrt (m : ℝ) := by
    rw [show (((2 ^ κ * m : ℕ)) : ℝ) = (2 : ℝ) ^ κ * (m : ℝ) by push_cast; ring,
      Real.sqrt_mul (by positivity)]
  have hgd : Nat.gcd (2 ^ κ) g * Nat.gcd m g ∣ Nat.gcd (2 ^ κ * m) g := by
    refine Nat.dvd_gcd (Nat.mul_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)) ?_
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _)
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) hcop)
  have hgle : ((Nat.gcd (2 ^ κ) g : ℕ) : ℝ) * ((Nat.gcd m g : ℕ) : ℝ)
      ≤ ((Nat.gcd (2 ^ κ * m) g : ℕ) : ℝ) := by
    have : Nat.gcd (2 ^ κ) g * Nat.gcd m g ≤ Nat.gcd (2 ^ κ * m) g :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero fun hz => by
        have := (Nat.gcd_eq_zero_iff.mp hz).1
        simp only [Nat.mul_eq_zero] at this
        rcases this with h | h
        · exact (pow_ne_zero κ two_ne_zero) h
        · exact hm0 h) hgd
    exact_mod_cast this
  have hsqrtprod : Real.sqrt ((Nat.gcd (2 ^ κ) g : ℕ) : ℝ) * Real.sqrt ((Nat.gcd m g : ℕ) : ℝ)
      ≤ Real.sqrt ((Nat.gcd (2 ^ κ * m) g : ℕ) : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hgle
  have hrewrite : ((2 ^ κ * m : ℕ).divisors.card : ℝ) * Real.sqrt ((2 ^ κ * m : ℕ) : ℝ)
      = ((((2 ^ κ : ℕ).divisors.card : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ κ))
        * ((m.divisors.card : ℝ) * Real.sqrt (m : ℝ)) := by
    rw [hcard, hsqrtk]
    push_cast
    ring
  calc ((((2 ^ κ : ℕ).divisors.card : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ κ)
          * Real.sqrt ((Nat.gcd (2 ^ κ) g : ℕ) : ℝ))
        * ((m.divisors.card : ℝ) * Real.sqrt (m : ℝ) * Real.sqrt ((Nat.gcd m g : ℕ) : ℝ))
      = ((((2 ^ κ : ℕ).divisors.card : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ κ))
          * ((m.divisors.card : ℝ) * Real.sqrt (m : ℝ))
          * (Real.sqrt ((Nat.gcd (2 ^ κ) g : ℕ) : ℝ)
              * Real.sqrt ((Nat.gcd m g : ℕ) : ℝ)) := by ring
    _ ≤ ((((2 ^ κ : ℕ).divisors.card : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ κ))
          * ((m.divisors.card : ℝ) * Real.sqrt (m : ℝ))
          * Real.sqrt ((Nat.gcd (2 ^ κ * m) g : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrtprod (by positivity)
    _ = ((2 ^ κ * m : ℕ).divisors.card : ℝ) * Real.sqrt ((2 ^ κ * m : ℕ) : ℝ)
          * Real.sqrt ((Nat.gcd (2 ^ κ * m) g : ℕ) : ℝ) := by rw [hrewrite]

/-- **D3 — the factor-free global bound, `ZMod` form.** HB (7.1) VERBATIM, constant `1`,
on every modulus whose 2-part is at most `2^8`. -/
theorem norm_kloosterman_estermann_of_v2_le {k : ℕ} [NeZero k]
    (hk : k.factorization 2 ≤ 8) (a b : ZMod k) :
    ‖kloosterman a b‖
      ≤ (k.divisors.card : ℝ) * Real.sqrt (k : ℝ)
          * Real.sqrt ((Nat.gcd k (Nat.gcd a.val b.val) : ℕ) : ℝ) := by
  have ha : ((a.val : ℕ) : ZMod k) = a := by rw [ZMod.natCast_val, ZMod.cast_id]
  have hb : ((b.val : ℕ) : ZMod k) = b := by rw [ZMod.natCast_val, ZMod.cast_id]
  have := norm_kloosterman_estermann_nat_of_v2_le k hk a.val b.val
  rwa [ha, hb] at this

/-- **D4 — THE CLOSE ON ROAD MODULI: Estermann (7.1) verbatim, no 2-adic factor.**
At `k = D·δ₁·w₁` with `D = roadModulus α₂ q`, the support conditions force `δ₁, w₁` odd,
so `v₂(k) = v₂(D) = max (v₂ α₂) (v₂ q)` and the hypothesis is two valuation bounds. -/
theorem norm_kloosterman_estermann_road_clean {α₂ q δ₁ w₁ α : ℕ}
    (hα₂ : α₂ ≠ 0) (hq : q ≠ 0)
    (hv2α : α₂.factorization 2 ≤ 8) (hw4a : q.factorization 2 ≤ 8)
    (hα : 2 ∣ α) (hδ : Nat.Coprime δ₁ α) (hw : Nat.Coprime w₁ α)
    [NeZero (roadModulus α₂ q * δ₁ * w₁)] (a b : ZMod (roadModulus α₂ q * δ₁ * w₁)) :
    ‖kloosterman a b‖
      ≤ ((roadModulus α₂ q * δ₁ * w₁).divisors.card : ℝ)
          * Real.sqrt ((roadModulus α₂ q * δ₁ * w₁ : ℕ) : ℝ)
          * Real.sqrt
              ((Nat.gcd (roadModulus α₂ q * δ₁ * w₁) (Nat.gcd a.val b.val) : ℕ) : ℝ) := by
  have hD : roadModulus α₂ q ≠ 0 := by
    intro h
    exact (NeZero.ne (roadModulus α₂ q * δ₁ * w₁)) (by simp [h])
  have hk : (roadModulus α₂ q * δ₁ * w₁).factorization 2 ≤ 8 := by
    rw [factorization_two_kloosterman_modulus hD hα hδ hw,
      factorization_two_roadModulus hα₂ hq]
    exact max_le hv2α hw4a
  exact norm_kloosterman_estermann_of_v2_le hk a b

end Salt.Weil
