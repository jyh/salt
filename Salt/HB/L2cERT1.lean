/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cER

/-!
# HB-L2c — the `E_R` T1′ family (node HB-L2c, the all-plus subclass of `ER_prime_cover`)

This file prices the **all-plus** subclass of the `E_R` prime part: window elements `n`
with `n = p` prime and `(n+2)₋ = 1` (every prime block of `n+2` has `χ = +1`) — the first
summand of `L2cER.ER_prime_cover`.

## STOP RECORD (iron rule 1) — the frozen `ER_T1'_bound` shape is NOT stated here

The freeze (`docs/exploration/l2c-freeze.md` §S4; `L2cER` §5 NOTES) assigns this subclass
the `J1` budget `≤ Cmain·(x / z₀)` with `Cmain` absolute.  That statement is
**unprovable as stated** under the master packet `(hz100, hz8, hzx)` alone:

* For all-plus `M`, `Λ̃(M) = 2^{ω(M)}(log M − log rad M) + 2^{ω(M)−1}·log rad M` — the
  weight is exponential in `ω(M)`, and `ω(M)` is unbounded on the subclass (no
  single-block structure caps it).  The `E_L` side never priced this shape in a `J1` row:
  there the all-plus class (`v = 1`, `n₊` composite) lives inside `EL_T2_bound`, a `J2`
  row whose `e^{5z₀}·PretenseSum` allowance absorbs the `2^{ω}` weight.
* At `χ` principal (`q = 1`, `hsq` holds, `χ_ℝ ≡ 1`) the subclass contains every prime
  `p ∈ (x,2x]` with `p+2 = QR`, `Q,R ≥ z` prime, each term `≈ 2L'²`; quantitative
  Hardy–Littlewood counts put this slice at `≍ x·log z₀`.  The packet corner
  `z ≍ L'⁸` (allowed by `hz8`) drives `z₀ = L'/log z → ∞`, so `x·log z₀ ≫ Cmain·(x/z₀)`
  for every fixed `Cmain`.  The roles-swap restatement routed the `w = 1` composite
  plus-part class into `T1'`/`J1`, where `E_L` routes it into `T2`/`J2` — an R6-cover
  statement-layer gap (the freeze's own open risk), for Fable/human re-ratification.

## What lands instead (the Zeno partial, sorry-free)

Splitting the subclass by `IsPrimePow (n+2)`:

* `ER_T1'_pp_bound` — the prime-power slice: primes vanish exactly, proper prime powers
  number `≤ √(2x+2)`, each term `≤ 2L'²` (sharp all-plus cap `Λ̃ ≤ 2·log`, no `e^{z₀}`):
  `≤ 4·(x / z₀)` — the true `J1` shape.
* `ER_T1'_comp_bound` — the composite slice: fiber by `p'' := minFac(n+2)`, a `χ=+1`
  prime in `[z, √(2x+2)]`; count fibers with `L2cCore.l2c_pair_count_clean` at
  `(d₁,d₂) = (1, p'')`, sifted at `Z := Zz z` (the cofactor `(n+2)/p''` is only
  `z`-rough — house amendment #3 makes a `Zf`-sift unsound here; the `n`-side cofactor
  is the prime `n > x` itself); sum `Σ 1/p''` by the `PretenseSum` conversion:
  `≤ 524288·(x/L')·e^{5z₀}·PS(2x+2)` — exactly the frozen `J2` row shape.
* `ER_T1'_split` / `ER_T1'_bound_mixed` — the exact cover and the combined budget
  `≤ 4·(x/z₀) + 524288·(x/L')·e^{5z₀}·PS(2x+2)`.
* `ER_T1'_odd_guard` / `erT1_mem_odd` — house amendment #2 (catch #246): the parity
  guard `Odd n` is implied on this family and made explicit (filter equivalence).

At the Horn-A consumption site (`χ` exceptional, `PS` small, `z₀` bounded by the G2
window discipline) the mixed bound recovers the intended `J1` grade; the general-packet
`J1` claim is the refuted part.  No junk-guard predicate is needed: the only routed
modulus is a genuine prime `p'' ≥ z`, never a small-base squarefull block.

Single-writer file (`L2cERT1.lean`); imports the frozen surfaces `L2cER`/`L2cCore`
only and touches no other file.  Helper names carry the `erT1_` prefix (house
amendment #1: the single-writer law extends to names).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — window and structure helpers -/

/-- A number all of whose prime factors exceed `Z` is coprime to `primorial Z`. -/
lemma erT1_coprime_primorial_of_rough {Z m : ℕ}
    (h : ∀ r : ℕ, r.Prime → r ∣ m → Z < r) : Nat.Coprime (primorial Z) m := by
  rw [primorial]
  refine Nat.Coprime.prod_left fun p hp => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hp
  rw [(hp.2).coprime_iff_not_dvd]
  intro hdvd
  have := h p hp.2 hdvd
  omega

/-- On the all-plus subclass, `n+2` **is** its own plus part. -/
lemma erT1_np2_eq_nPlus (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (h1 : nMinus χ (n + 2) = 1) :
    n + 2 = nPlus χ (n + 2) := by
  have h := eq_nPlus_mul_nMinus χ hsq (n := n + 2) (by omega) (l2cWindow_np2_coprime_q χ hn)
  rw [h1, mul_one] at h
  exact h

/-- Every prime of an all-plus `n+2` has `χ = +1`. -/
lemma erT1_np2_prime_sign (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (h1 : nMinus χ (n + 2) = 1) {r : ℕ} (hr : r.Prime)
    (hrd : r ∣ n + 2) : chiRe χ r = 1 := by
  have h2 : r ∣ nPlus χ (n + 2) := by
    rw [← erT1_np2_eq_nPlus χ hsq hn h1]
    exact hrd
  exact nPlus_dvd_sign hr h2

/-- Every prime of an all-plus `n+2` is `≥ z` (window roughness through the `+1` sign). -/
lemma erT1_np2_prime_ge (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hn : n ∈ l2cWindow χ z x) (h1 : nMinus χ (n + 2) = 1) {r : ℕ} (hr : r.Prime)
    (hrd : r ∣ n + 2) : z ≤ r := by
  have hsign := erT1_np2_prime_sign χ hsq hn h1 hr hrd
  refine l2cWindow_roughness χ z x hn hr (hrd.mul_left n) ?_
  rw [hsign]
  norm_num

/-- **Shifted proper-prime-power count.**  `#{n ∈ (x,2x] : n+2 = p^k, k ≥ 2} ≤ √(2x+2)`
    (the `n ↦ minFac (n+2)` map is injective — a width-`x` window holds one power of
    each `p` — into `[1, √(2x+2)]`).  The `n+2`-shifted mirror of
    `L2cER.properPrimePow_count`. -/
lemma erT1_shifted_properPrimePow_count (x : ℕ) :
    (((Finset.Ioc x (2 * x)).filter
        (fun n => IsPrimePow (n + 2) ∧ ¬ (n + 2).Prime)).card : ℕ)
      ≤ Nat.sqrt (2 * x + 2) := by
  classical
  have hdes : ∀ n ∈ (Finset.Ioc x (2 * x)).filter
      (fun n => IsPrimePow (n + 2) ∧ ¬ (n + 2).Prime),
      ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ p ^ k = n + 2 ∧ (n + 2).minFac = p := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨p, k, hp, hk, hpk⟩ := hn.2.1
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hn.2.2 (by rw [← hpk, pow_one]; exact hp')
    exact ⟨p, k, hp', by omega, hpk, by rw [← hpk]; exact hp'.pow_minFac (by omega)⟩
  have hle : ((Finset.Ioc x (2 * x)).filter
        (fun n => IsPrimePow (n + 2) ∧ ¬ (n + 2).Prime)).card
      ≤ (Finset.Icc 1 (Nat.sqrt (2 * x + 2))).card := by
    refine Finset.card_le_card_of_injOn (fun n => (n + 2).minFac) ?_ ?_
    · intro n hn
      have hnf := Finset.mem_coe.mp hn
      obtain ⟨p, k, hp, hk, hpk, hmf⟩ := hdes n hnf
      rw [Finset.mem_filter, Finset.mem_Ioc] at hnf
      have h1 : 1 ≤ (n + 2).minFac := by rw [hmf]; exact hp.pos
      have h2 : (n + 2).minFac ≤ Nat.sqrt (2 * x + 2) := by
        rw [hmf, Nat.le_sqrt']
        have hp2n : p ^ 2 ≤ n + 2 := by
          rw [← hpk]
          exact Nat.pow_le_pow_right hp.pos hk
        omega
      exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    · intro n hn n' hn' heq
      obtain ⟨p, k, hp, hk, hpk, hmf⟩ := hdes n (Finset.mem_coe.mp hn)
      obtain ⟨p', k', hp', hk', hpk', hmf'⟩ := hdes n' (Finset.mem_coe.mp hn')
      have hpp' : p = p' := by rw [← hmf, ← hmf']; exact heq
      subst hpp'
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ioc] at hn hn'
      obtain ⟨⟨hxn, hn2x⟩, -⟩ := hn
      obtain ⟨⟨hxn', hn2x'⟩, -⟩ := hn'
      -- both `p^k, p^{k'} ∈ (x+2, 2x+2]`; the width-`x` range forces `k = k'`
      have hkey : ∀ a b : ℕ, a ≤ b → p ^ b ≤ 2 * x + 2 → x + 2 < p ^ a → a = b := by
        intro a b hab hb ha
        by_contra hne
        have hab' : a + 1 ≤ b := by omega
        have hpow : p ^ (a + 1) ≤ p ^ b := Nat.pow_le_pow_right hp.pos hab'
        rw [pow_succ] at hpow
        have h2 : 2 * p ^ a ≤ p ^ a * p := by
          have hp2 := hp.two_le
          calc 2 * p ^ a = p ^ a * 2 := by ring
            _ ≤ p ^ a * p := by gcongr
        omega
      have hkk : k = k' := by
        rcases le_total k k' with h | h
        · exact hkey k k' h (by rw [hpk']; omega) (by rw [hpk]; omega)
        · exact (hkey k' k h (by rw [hpk]; omega) (by rw [hpk']; omega)).symm
      rw [hkk] at hpk
      omega
  refine hle.trans ?_
  rw [Nat.card_Icc]
  omega

/-! ## §1 — the in-regime scale facts -/

/-- In-regime floor `x ≥ 100⁴⁸` (from `z ≥ 100¹⁶`, `z³ ≤ x`). -/
lemma erT1_x_ge_100 {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ (x : ℝ)) :
    (100 : ℝ) ^ 48 ≤ (x : ℝ) := by
  have hzr : (100 : ℝ) ^ 16 ≤ (z : ℝ) := by exact_mod_cast hz100
  calc (100 : ℝ) ^ 48 = ((100 : ℝ) ^ 16) ^ 3 := by
        rw [show (48 : ℕ) = 16 * 3 from rfl, pow_mul]
    _ ≤ (z : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hzr 3
    _ ≤ (x : ℝ) := hzx

/-- `z ≤ x` (real form). -/
lemma erT1_z_le_x {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ (x : ℝ)) :
    (z : ℝ) ≤ (x : ℝ) := by
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast le_trans (by norm_num) hz100
  calc (z : ℝ) ≤ (z : ℝ) ^ 3 := le_self_pow₀ hz1 (by norm_num)
    _ ≤ (x : ℝ) := hzx

/-- `L' ≥ 1` once `x ≥ 1`. -/
lemma erT1_Lwin_ge_one {x : ℕ} (hx1 : (1 : ℝ) ≤ (x : ℝ)) : 1 ≤ Lwin x := by
  rw [Lwin]
  have h4 : (4 : ℝ) ≤ 2 * (x : ℝ) + 2 := by linarith
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact (Real.exp_one_lt_d9.trans (by norm_num)).le
  calc (1 : ℝ) ≤ Real.log 4 := hlog4
    _ ≤ Real.log (2 * (x : ℝ) + 2) := Real.log_le_log (by norm_num) h4

/-- `log z ≥ 1` (from `z ≥ 100¹⁶ ≥ e`). -/
lemma erT1_logz_ge_one {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : 1 ≤ Real.log z := by
  have h3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast le_trans (by norm_num) hz100
  rw [Real.le_log_iff_exp_le (by linarith)]
  exact le_trans (Real.exp_one_lt_d9.trans (by norm_num)).le h3

/-- `z₀ > 0` in-regime. -/
lemma erT1_z0_pos {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hx1 : (1 : ℝ) ≤ (x : ℝ)) :
    0 < z0 z x := by
  rw [z0]
  refine div_pos ?_ (lt_of_lt_of_le one_pos (erT1_logz_ge_one hz100))
  exact lt_of_lt_of_le one_pos (erT1_Lwin_ge_one hx1)

/-- `z₀ ≤ L'` (since `log z ≥ 1`). -/
lemma erT1_z0_le_Lwin {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) : z0 z x ≤ Lwin x := by
  rw [z0]
  exact div_le_self (Lwin_nonneg x) (erT1_logz_ge_one hz100)

/-- `L'³ ≤ √x` (from `L'⁸ ≤ z ≤ x`; the pp-slice absorption scale). -/
lemma erT1_Lwin_cube_le_sqrt {z x : ℕ} (hz100 : 100 ^ 16 ≤ z)
    (hz8 : Lwin x ^ 8 ≤ (z : ℝ)) (hzx : (z : ℝ) ^ 3 ≤ (x : ℝ)) :
    Lwin x ^ 3 ≤ Real.sqrt x := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) (erT1_x_ge_100 hz100 hzx)
  have hL1 : 1 ≤ Lwin x := erT1_Lwin_ge_one hx1
  have hL6 : Lwin x ^ 6 ≤ (x : ℝ) := by
    calc Lwin x ^ 6 ≤ Lwin x ^ 8 := pow_le_pow_right₀ hL1 (by omega)
      _ ≤ (z : ℝ) := hz8
      _ ≤ (x : ℝ) := erT1_z_le_x hz100 hzx
  calc Lwin x ^ 3 = Real.sqrt ((Lwin x ^ 3) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt x := by
        refine Real.sqrt_le_sqrt ?_
        calc (Lwin x ^ 3) ^ 2 = Lwin x ^ 6 := by ring
          _ ≤ (x : ℝ) := hL6

/-- The natural square-root count, real-cast: `(⌊√m⌋ : ℝ) ≤ √m`. -/
lemma erT1_natSqrt_le (m : ℕ) : ((Nat.sqrt m : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) := by
  have h1 : ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ ((m : ℕ) : ℝ) := by
    calc ((Nat.sqrt m : ℕ) : ℝ) ^ 2 = ((Nat.sqrt m ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((m : ℕ) : ℝ) := by exact_mod_cast Nat.sqrt_le' m
  calc ((Nat.sqrt m : ℕ) : ℝ) = Real.sqrt (((Nat.sqrt m : ℕ) : ℝ) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt h1

/-- `√(2x+2) ≤ 2√x` once `x ≥ 1`. -/
lemma erT1_sqrt_shift_le {x : ℕ} (hx1 : (1 : ℝ) ≤ (x : ℝ)) :
    Real.sqrt ((2 * x + 2 : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
  have h4 : ((2 * x + 2 : ℕ) : ℝ) ≤ 4 * (x : ℝ) := by push_cast; linarith
  have hsq4 : Real.sqrt (4 * (x : ℝ)) = 2 * Real.sqrt x := by
    rw [show (4 : ℝ) * (x : ℝ) = 2 ^ 2 * (x : ℝ) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  calc Real.sqrt ((2 * x + 2 : ℕ) : ℝ) ≤ Real.sqrt (4 * (x : ℝ)) := Real.sqrt_le_sqrt h4
    _ = 2 * Real.sqrt x := hsq4

/-! ## §2 — the prime-power slice (the true `J1` row) -/

/-- **The sharp all-plus prime-power cap.**  On the window with `(n+2)₋ = 1` and `n+2` a
    prime power, `Λ̃(n+2) ≤ 2·L'` — `f(n+2) = 2^{ω} = 2`, no `e^{z₀}` inflation. -/
lemma erT1_lamTilde_all_plus_pp_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {z x n : ℕ} (hn : n ∈ l2cWindow χ z x) (h1 : nMinus χ (n + 2) = 1)
    (hpp : IsPrimePow (n + 2)) : LamTilde χ (n + 2) ≤ 2 * Lwin x := by
  have h0 : n + 2 ≠ 0 := by omega
  have hcop := l2cWindow_np2_coprime_q χ hn
  have hcard : (n + 2).primeFactors.card = 1 :=
    isPrimePow_iff_card_primeFactors_eq_one.mp hpp
  have hsign : ∀ p ∈ (n + 2).primeFactors, chiRe χ p = 1 := fun p hp =>
    erT1_np2_prime_sign χ hsq hn h1 (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  have hf : fChiSum χ (n + 2) = 2 := by
    rw [← fChiArith_eq_fChiSum, fChiArith_eq_two_pow χ hsq h0 hsign, hcard, pow_one]
  have hb := (l2cWindow_mem_iff χ z x n).mp hn
  have hlog : Real.log ((n : ℝ) + 2) ≤ Lwin x := by
    rw [Lwin]
    have h2x : (n : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hb.1.2
    exact Real.log_le_log (by positivity) (by linarith)
  calc LamTilde χ (n + 2) ≤ fChiSum χ (n + 2) * Real.log (((n + 2 : ℕ)) : ℝ) :=
        LamTilde_le_of_nMinus_one χ hsq h0 hcop h1
    _ = 2 * Real.log ((n : ℝ) + 2) := by rw [hf]; push_cast; ring_nf
    _ ≤ 2 * Lwin x := by linarith [hlog]

/-- **The `T1'` prime-power slice, `J1`-priced.**  Primes `n+2` vanish exactly; proper
    prime powers number `≤ √(2x+2)`, each term `≤ 2L'²`, and `√x·L'²·z₀ ≤ x`. -/
theorem ER_T1'_pp_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ (z : ℝ)) (hzx : (z : ℝ) ^ 3 ≤ (x : ℝ)) :
    ∑ n ∈ (l2cWindow χ z x).filter
        (fun n => n.Prime ∧ nMinus χ (n + 2) = 1 ∧ IsPrimePow (n + 2)),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ 4 * ((x : ℝ) / z0 z x) := by
  classical
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) (erT1_x_ge_100 hz100 hzx)
  set S := (l2cWindow χ z x).filter
      (fun n => n.Prime ∧ nMinus χ (n + 2) = 1 ∧ IsPrimePow (n + 2)) with hS
  -- the `(n+2)`-prime terms vanish
  have hsplit : ∑ n ∈ S, Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      = ∑ n ∈ S.filter (fun n => ¬ (n + 2).Prime),
          Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) := by
    refine (Finset.sum_filter_of_ne fun n _ hne hprime => ?_).symm
    exact hne (by rw [lamTilde_sub_vonMangoldt_eq_zero_of_prime χ hsq hprime, mul_zero])
  -- per-term cap `2L'²`
  have hterm : ∀ n ∈ S.filter (fun n => ¬ (n + 2).Prime),
      Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) ≤ 2 * Lwin x ^ 2 := by
    intro n hn
    have hnS := Finset.mem_of_mem_filter n hn
    rw [hS, Finset.mem_filter] at hnS
    obtain ⟨hnw, -, h1, hpp⟩ := hnS
    have hΛ := l2cWindow_vonMangoldt_cap χ hnw
    have hLt := erT1_lamTilde_all_plus_pp_le χ hsq hnw h1 hpp
    have hsub0 : 0 ≤ LamTilde χ (n + 2) - Λ (n + 2) := by
      have := vonMangoldt_le_LamTilde χ hsq (n + 2)
      linarith
    have hsub2 : LamTilde χ (n + 2) - Λ (n + 2) ≤ 2 * Lwin x := by
      have h0 : (0 : ℝ) ≤ Λ (n + 2) := vonMangoldt_nonneg
      linarith
    calc Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) ≤ Lwin x * (2 * Lwin x) :=
          mul_le_mul hΛ hsub2 hsub0 (Lwin_nonneg x)
      _ = 2 * Lwin x ^ 2 := by ring
  -- the count
  have hcount : (S.filter (fun n => ¬ (n + 2).Prime)).card ≤ Nat.sqrt (2 * x + 2) := by
    refine le_trans (Finset.card_le_card ?_) (erT1_shifted_properPrimePow_count x)
    intro n hn
    rw [Finset.mem_filter] at hn
    have hnS := hn.1
    rw [hS, Finset.mem_filter] at hnS
    rw [Finset.mem_filter]
    exact ⟨l2cWindow_subset χ z x hnS.1, hnS.2.2.2, hn.2⟩
  -- assemble
  have hz0pos : 0 < z0 z x := erT1_z0_pos hz100 hx1
  rw [hsplit, show (4 : ℝ) * ((x : ℝ) / z0 z x) = 4 * (x : ℝ) / z0 z x by ring,
    le_div_iff₀ hz0pos]
  have hcR : ((S.filter (fun n => ¬ (n + 2).Prime)).card : ℝ)
      ≤ Real.sqrt ((2 * x + 2 : ℕ) : ℝ) := by
    refine le_trans ?_ (erT1_natSqrt_le (2 * x + 2))
    exact_mod_cast hcount
  have hsq2 := erT1_sqrt_shift_le hx1
  have hL3 := erT1_Lwin_cube_le_sqrt hz100 hz8 hzx
  have hz0L := erT1_z0_le_Lwin (x := x) hz100
  calc (∑ n ∈ S.filter (fun n => ¬ (n + 2).Prime),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2))) * z0 z x
      ≤ (((S.filter (fun n => ¬ (n + 2).Prime)).card : ℝ) * (2 * Lwin x ^ 2)) * z0 z x := by
        refine mul_le_mul_of_nonneg_right ?_ hz0pos.le
        calc ∑ n ∈ S.filter (fun n => ¬ (n + 2).Prime),
              Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
            ≤ ∑ _n ∈ S.filter (fun n => ¬ (n + 2).Prime), 2 * Lwin x ^ 2 :=
              Finset.sum_le_sum hterm
          _ = ((S.filter (fun n => ¬ (n + 2).Prime)).card : ℝ) * (2 * Lwin x ^ 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * Real.sqrt x * (2 * Lwin x ^ 2)) * Lwin x := by
        have hc2 : ((S.filter (fun n => ¬ (n + 2).Prime)).card : ℝ) ≤ 2 * Real.sqrt x :=
          hcR.trans hsq2
        have hz00 : 0 ≤ z0 z x := hz0pos.le
        have hL2 : (0 : ℝ) ≤ 2 * Lwin x ^ 2 := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_right hc2 hL2) hz0L hz00 (by positivity)
    _ = 4 * (Real.sqrt x * Lwin x ^ 3) := by ring
    _ ≤ 4 * (Real.sqrt x * Real.sqrt x) := by
        have h0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg _
        have := mul_le_mul_of_nonneg_left hL3 h0
        linarith
    _ = 4 * (x : ℝ) := by rw [Real.mul_self_sqrt (by positivity)]

/-! ## §3 — the composite slice: the `minFac` fibration at `Zz` (the `J2` row)

House amendment #3: the fiber cofactor `(n+2)/p''` is only `z`-rough, so the pair count
is sifted at `Zz z = ⌊z^{1/16}⌋` (a `Zf`-sift would be unsound in-regime); the `n`-side
cofactor is the prime `n > x` itself, trivially `Zz`-rough. -/

/-- `Zz z < z` in-regime. -/
lemma erT1_Zz_lt_z {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : Zz z < z := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by
    have h2 : (2 : ℕ) ≤ z := le_trans (by norm_num) hz100
    exact_mod_cast lt_of_lt_of_le one_lt_two h2
  have h1 : ((Zz z : ℕ) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := by
    rw [Zz]
    exact Nat.floor_le (by positivity)
  have h2 : (z : ℝ) ^ ((1 : ℝ) / 16) < (z : ℝ) := by
    calc (z : ℝ) ^ ((1 : ℝ) / 16) < (z : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt hz1 (by norm_num)
      _ = (z : ℝ) := Real.rpow_one _
  exact_mod_cast h1.trans_lt h2

/-- The `Zz` log floor: `log z ≤ 32·log (Zz z)` (from `z^{1/16} < 2·Zz` and
    `log 2 ≤ log Zz`). -/
lemma erT1_log_Zz_ge {z : ℕ} (hz100 : 100 ^ 16 ≤ z) :
    Real.log z ≤ 32 * Real.log (Zz z) := by
  have hZ100 : 100 ≤ Zz z := Zz_ge_100 hz100
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    have : (1 : ℕ) ≤ z := le_trans (by norm_num) hz100
    exact_mod_cast lt_of_lt_of_le one_pos this
  have h1 : (z : ℝ) ^ ((1 : ℝ) / 16) < ((Zz z : ℕ) : ℝ) + 1 := by
    rw [Zz]
    exact Nat.lt_floor_add_one _
  have h2 : ((Zz z : ℕ) : ℝ) + 1 ≤ 2 * ((Zz z : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((Zz z : ℕ) : ℝ) := by exact_mod_cast le_trans (by norm_num) hZ100
    linarith
  have h3 : Real.log ((z : ℝ) ^ ((1 : ℝ) / 16))
      ≤ Real.log (2 * ((Zz z : ℕ) : ℝ)) :=
    Real.log_le_log (by positivity) (h1.le.trans h2)
  rw [Real.log_rpow hzpos, Real.log_mul (by norm_num) (by positivity)] at h3
  have h4 : Real.log 2 ≤ Real.log (Zz z) := by
    refine Real.log_le_log (by norm_num) ?_
    exact_mod_cast le_trans (by norm_num : (2 : ℕ) ≤ 100) hZ100
  linarith

/-- `0 < log (Zz z)` in-regime. -/
lemma erT1_log_Zz_pos {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : 0 < Real.log (Zz z) := by
  refine Real.log_pos ?_
  exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 100) (Zz_ge_100 hz100)

/-- **The `T1'` legality at `Zz`.**  For a fiber modulus `p ≤ √(2x+2)`:
    `p·Zz⁸·(log Zz)² ≤ 2√x·√z·√z = 2√x·z ≤ 2x ≤ 32x`. -/
lemma erT1_legality {z x p : ℕ} (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ (z : ℝ))
    (hzx : (z : ℝ) ^ 3 ≤ (x : ℝ)) (hple : p ≤ Nat.sqrt (2 * x + 2)) :
    (p : ℝ) * ((Zz z : ℕ) : ℝ) ^ 8 * Real.log (Zz z) ^ 2 ≤ 32 * (x : ℝ) := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) (erT1_x_ge_100 hz100 hzx)
  have hz1R : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast le_trans (by norm_num) hz100
  have hzpos : (0 : ℝ) < (z : ℝ) := lt_of_lt_of_le one_pos hz1R
  have hL1 : 1 ≤ Lwin x := erT1_Lwin_ge_one hx1
  -- `p ≤ 2√x`
  have hp2sx : (p : ℝ) ≤ 2 * Real.sqrt x := by
    have h1 : (p : ℝ) ≤ ((Nat.sqrt (2 * x + 2) : ℕ) : ℝ) := by exact_mod_cast hple
    exact h1.trans ((erT1_natSqrt_le (2 * x + 2)).trans (erT1_sqrt_shift_le hx1))
  -- `Zz⁸ ≤ √z`
  have hZz8 : ((Zz z : ℕ) : ℝ) ^ 8 ≤ Real.sqrt z := by
    have h1 : ((Zz z : ℕ) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := by
      rw [Zz]
      exact Nat.floor_le (by positivity)
    have h2 : ((Zz z : ℕ) : ℝ) ^ 8 ≤ ((z : ℝ) ^ ((1 : ℝ) / 16)) ^ (8 : ℕ) :=
      pow_le_pow_left₀ (by positivity) h1 8
    rwa [show ((z : ℝ) ^ ((1 : ℝ) / 16)) ^ (8 : ℕ) = Real.sqrt z by
      rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 16)) 8,
        ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]
      norm_num] at h2
  -- `(log Zz)² ≤ L'² ≤ √z`
  have hlogZz2 : Real.log (Zz z) ^ 2 ≤ Real.sqrt z := by
    have hlogZznn : 0 ≤ Real.log ((Zz z : ℕ) : ℝ) := (erT1_log_Zz_pos hz100).le
    have h1 : Real.log ((Zz z : ℕ) : ℝ) ≤ Real.log z := by
      have hZ1 : (1 : ℕ) ≤ Zz z := le_trans (by norm_num) (Zz_ge_100 hz100)
      have hZpos : (0 : ℝ) < ((Zz z : ℕ) : ℝ) := by
        exact_mod_cast lt_of_lt_of_le one_pos hZ1
      exact Real.log_le_log hZpos (by exact_mod_cast (erT1_Zz_lt_z hz100).le)
    have h2 : Real.log z ≤ Lwin x := by
      rw [Lwin]
      refine Real.log_le_log hzpos ?_
      have := erT1_z_le_x hz100 hzx
      linarith
    have h3 : Real.log (Zz z) ^ 2 ≤ Lwin x ^ 2 := by nlinarith [h1, h2, hlogZznn]
    have h4 : Lwin x ^ 2 ≤ Real.sqrt z := by
      have h6 : (Lwin x ^ 2) ^ 2 ≤ (z : ℝ) := by
        calc (Lwin x ^ 2) ^ 2 = Lwin x ^ 4 := by ring
          _ ≤ Lwin x ^ 8 := pow_le_pow_right₀ hL1 (by omega)
          _ ≤ (z : ℝ) := hz8
      calc Lwin x ^ 2 = Real.sqrt ((Lwin x ^ 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt z := Real.sqrt_le_sqrt h6
    linarith
  -- assemble: `≤ 2√x·√z·√z = 2√x·z ≤ 2√x·√x = 2x`
  have hsznn : 0 ≤ Real.sqrt (z : ℝ) := Real.sqrt_nonneg _
  have hsxnn : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
  have hzsx : (z : ℝ) ≤ Real.sqrt x := by
    have h2 : (z : ℝ) ^ 2 ≤ (x : ℝ) := by nlinarith [hzx, hz1R]
    calc (z : ℝ) = Real.sqrt ((z : ℝ) ^ 2) := (Real.sqrt_sq hzpos.le).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt h2
  have hstep : (p : ℝ) * ((Zz z : ℕ) : ℝ) ^ 8 * Real.log (Zz z) ^ 2
      ≤ 2 * Real.sqrt x * Real.sqrt z * Real.sqrt z := by
    have hZnn : (0 : ℝ) ≤ ((Zz z : ℕ) : ℝ) ^ 8 := by positivity
    have hlnn : (0 : ℝ) ≤ Real.log (Zz z) ^ 2 := by positivity
    have h1 : (p : ℝ) * ((Zz z : ℕ) : ℝ) ^ 8 ≤ 2 * Real.sqrt x * Real.sqrt z :=
      mul_le_mul hp2sx hZz8 hZnn (by positivity)
    exact mul_le_mul h1 hlogZz2 hlnn (by positivity)
  calc (p : ℝ) * ((Zz z : ℕ) : ℝ) ^ 8 * Real.log (Zz z) ^ 2
      ≤ 2 * Real.sqrt x * Real.sqrt z * Real.sqrt z := hstep
    _ = 2 * Real.sqrt x * (z : ℝ) := by
        rw [mul_assoc, Real.mul_self_sqrt hzpos.le]
    _ ≤ 2 * Real.sqrt x * Real.sqrt x := by
        exact mul_le_mul_of_nonneg_left hzsx (by positivity)
    _ = 2 * (x : ℝ) := by rw [mul_assoc, Real.mul_self_sqrt (by positivity)]
    _ ≤ 32 * (x : ℝ) := by linarith

/-- `PretenseSum ≥ 0`. -/
lemma erT1_pretense_nonneg (χ : DirichletCharacter ℂ q) (N : ℕ) :
    0 ≤ PretenseSum χ N := by
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (by positivity)

/-- `z₀³·e^{(log 2)·z₀} ≤ e^{5z₀}` (the `J2` exponent absorption). -/
lemma erT1_z0_cube_absorb {z x : ℕ} (hz100 : 100 ^ 16 ≤ z) (hx1 : (1 : ℝ) ≤ (x : ℝ)) :
    z0 z x ^ 3 * Real.exp (Real.log 2 * z0 z x) ≤ Real.exp (5 * z0 z x) := by
  have hz00 : 0 ≤ z0 z x := (erT1_z0_pos hz100 hx1).le
  have h1 : z0 z x ^ 3 ≤ Real.exp (3 * z0 z x) := by
    have ht : z0 z x ≤ Real.exp (z0 z x) := by
      have := Real.add_one_le_exp (z0 z x)
      linarith
    calc z0 z x ^ 3 ≤ Real.exp (z0 z x) ^ 3 := pow_le_pow_left₀ hz00 ht 3
      _ = Real.exp (3 * z0 z x) := by
          rw [← Real.exp_nat_mul]
          norm_num
  have h2 : Real.exp (Real.log 2 * z0 z x) ≤ Real.exp (z0 z x) := by
    refine Real.exp_le_exp.mpr ?_
    have hl2 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith [hz00]
  calc z0 z x ^ 3 * Real.exp (Real.log 2 * z0 z x)
      ≤ Real.exp (3 * z0 z x) * Real.exp (z0 z x) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (4 * z0 z x) := by
        rw [← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (5 * z0 z x) := Real.exp_le_exp.mpr (by nlinarith [hz00])

/-- **The `T1'` composite slice, `J2`-priced.**  Fiber by `p'' := minFac (n+2)` (a `χ=+1`
    prime in `[z, √(2x+2)]`), count each fiber by `l2c_pair_count_clean` at
    `(d₁,d₂) = (1, p'')`, `Z := Zz z`, and convert `Σ 1/p''` by the `PretenseSum` law:
    the frozen `J2` row shape, where `E_L` routes this same all-plus-composite class. -/
theorem ER_T1'_comp_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ (z : ℝ)) (hzx : (z : ℝ) ^ 3 ≤ (x : ℝ)) :
    ∑ n ∈ (l2cWindow χ z x).filter
        (fun n => n.Prime ∧ nMinus χ (n + 2) = 1 ∧ ¬ IsPrimePow (n + 2)),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ 524288 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by
  classical
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz1 : 1 < z := by omega
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) (erT1_x_ge_100 hz100 hzx)
  have hzxN : z ≤ x := by exact_mod_cast erT1_z_le_x hz100 hzx
  have hZzlt := erT1_Zz_lt_z hz100
  have hlogzpos : (0 : ℝ) < Real.log z := lt_of_lt_of_le one_pos (erT1_logz_ge_one hz100)
  set S := (l2cWindow χ z x).filter
      (fun n => n.Prime ∧ nMinus χ (n + 2) = 1 ∧ ¬ IsPrimePow (n + 2)) with hS
  set Q := (Finset.range (2 * x + 2 + 1)).filter
      (fun p => p.Prime ∧ chiRe χ p = 1 ∧ z ≤ p ∧ p ≤ Nat.sqrt (2 * x + 2)) with hQ
  -- the fiberwise map: `minFac (n+2)` lands in the modulus index `Q`
  have hmap : ∀ n ∈ S, (n + 2).minFac ∈ Q := by
    intro n hn
    rw [hS, Finset.mem_filter] at hn
    obtain ⟨hnw, hnp, h1, hnpp⟩ := hn
    have hmfp : (n + 2).minFac.Prime := Nat.minFac_prime (by omega)
    have hmfd : (n + 2).minFac ∣ n + 2 := Nat.minFac_dvd _
    have hnprime : ¬ (n + 2).Prime := fun h => hnpp h.isPrimePow
    have hb := (l2cWindow_mem_iff χ z x n).mp hnw
    have hn2x : n ≤ 2 * x := hb.1.2
    have hsq2 : (n + 2).minFac ^ 2 ≤ n + 2 := Nat.minFac_sq_le_self (by omega) hnprime
    have hle : (n + 2).minFac ≤ Nat.sqrt (2 * x + 2) := by
      rw [Nat.le_sqrt']
      omega
    have hmfle : (n + 2).minFac ≤ n + 2 := Nat.minFac_le (by omega)
    rw [hQ]
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hmfp, erT1_np2_prime_sign χ hsq hnw h1 hmfp hmfd,
      erT1_np2_prime_ge χ hsq hnw h1 hmfp hmfd, hle⟩
  -- the per-term weight cap
  have hW : ∀ n ∈ S, Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2 := by
    intro n hn
    have hnw : n ∈ l2cWindow χ z x := Finset.mem_of_mem_filter n hn
    have hΛn_le : Λ n ≤ Lwin x := l2cWindow_vonMangoldt_cap χ hnw
    have hcap := l2cWindow_lamTilde_np2_cap χ hsq hz2 hnw
    calc Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
        ≤ Λ n * LamTilde χ (n + 2) :=
          mul_le_mul_of_nonneg_left (sub_le_self _ vonMangoldt_nonneg) vonMangoldt_nonneg
      _ ≤ Lwin x * (Real.exp (Real.log 2 * z0 z x) * Lwin x) :=
          mul_le_mul hΛn_le hcap (LamTilde_nonneg χ hsq (n + 2)) (Lwin_nonneg x)
      _ = Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2 := by ring
  -- the fibered cardinality
  have hcard : S.card = ∑ p ∈ Q, (S.filter (fun n => (n + 2).minFac = p)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  -- the per-fiber pair count at `Zz`
  have hfiber : ∀ p ∈ Q, ((S.filter (fun n => (n + 2).minFac = p)).card : ℝ)
      ≤ 524288 * ((x : ℝ) / p) / Real.log z ^ 2 := by
    intro p hpQ
    rw [hQ] at hpQ
    simp only [Finset.mem_filter, Finset.mem_range] at hpQ
    obtain ⟨hplt, hpp, hpchi, hpz, hple⟩ := hpQ
    have hz3 : (3 : ℕ) ≤ z := le_trans (by norm_num) hz100
    have hodd : Odd p := hpp.odd_of_ne_two (by omega)
    have hsub : S.filter (fun n => (n + 2).minFac = p)
        ⊆ (baseSet x 1 p).filter
          (fun n => Nat.Coprime (primorial (Zz z)) ((n / 1) * ((n + 2) / p))) := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      obtain ⟨hnS, hmf⟩ := hn
      rw [hS, Finset.mem_filter] at hnS
      obtain ⟨hnw, hnp, h1, hnpp⟩ := hnS
      have hpd : p ∣ n + 2 := by rw [← hmf]; exact Nat.minFac_dvd _
      simp only [Finset.mem_filter]
      constructor
      · rw [baseSet, Finset.mem_filter]
        exact ⟨l2cWindow_subset χ z x hnw, one_dvd n, hpd⟩
      · rw [Nat.div_one]
        refine erT1_coprime_primorial_of_rough fun r hr hrd => ?_
        rcases (Nat.Prime.dvd_mul hr).mp hrd with hrn | hrc
        · have hrn' : r = n := (Nat.prime_dvd_prime_iff_eq hr hnp).mp hrn
          have hxr : x < n := (Finset.mem_Ioc.mp (l2cWindow_subset χ z x hnw)).1
          omega
        · have hrd2 : r ∣ n + 2 := hrc.trans (Nat.div_dvd_of_dvd hpd)
          have hge := erT1_np2_prime_ge χ hsq hnw h1 hr hrd2
          omega
    have hleg : ((1 : ℕ) : ℝ) * (p : ℝ) * ((Zz z : ℕ) : ℝ) ^ 8 * Real.log (Zz z) ^ 2
        ≤ 32 * (x : ℝ) := by
      rw [Nat.cast_one, one_mul]
      exact erT1_legality hz100 hz8 hzx hple
    have hcount := l2c_pair_count_clean (x := x) (d₁ := 1) (d₂ := p) (Z := Zz z)
      (Zz_ge_100 hz100) one_pos hpp.pos odd_one hodd (Nat.coprime_one_left p) hleg
    simp only [Nat.cast_one, one_mul] at hcount
    have hratio : ((p : ℝ) / (Nat.totient p : ℝ)) ^ 2 ≤ 4 := by
      rw [Nat.totient_prime hpp, Nat.cast_sub hpp.one_le, Nat.cast_one]
      have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hle2 : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      have hnn : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) := div_nonneg (by positivity) (by linarith)
      nlinarith [hle2, hnn]
    have hlogZzpos := erT1_log_Zz_pos hz100
    have hinv2 : Real.log z ^ 2 ≤ 1024 * Real.log (Zz z) ^ 2 := by
      calc Real.log z ^ 2 ≤ (32 * Real.log (Zz z)) ^ 2 :=
            pow_le_pow_left₀ hlogzpos.le (erT1_log_Zz_ge hz100) 2
        _ = 1024 * Real.log (Zz z) ^ 2 := by ring
    calc ((S.filter (fun n => (n + 2).minFac = p)).card : ℝ)
        ≤ (((baseSet x 1 p).filter
            (fun n => Nat.Coprime (primorial (Zz z)) ((n / 1) * ((n + 2) / p)))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 128 * ((p : ℝ) / (Nat.totient p : ℝ)) ^ 2 * ((x : ℝ) / p)
            / Real.log (Zz z) ^ 2 := hcount
      _ ≤ 128 * 4 * ((x : ℝ) / p) / Real.log (Zz z) ^ 2 := by gcongr
      _ = 128 * 4 * ((x : ℝ) / p) * (1 / Real.log (Zz z) ^ 2) := by ring
      _ ≤ 128 * 4 * ((x : ℝ) / p) * (1024 / Real.log z ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.log z ^ 2),
            div_mul_eq_mul_div, one_mul,
            div_le_iff₀ (by positivity : (0 : ℝ) < Real.log (Zz z) ^ 2)]
          linarith [hinv2]
      _ = 524288 * ((x : ℝ) / p) / Real.log z ^ 2 := by ring
  -- fiber sum → `PretenseSum`
  have hQsub : Q ⊆ (Finset.range (2 * x + 2 + 1)).filter
      (fun p => Nat.Prime p ∧ chiRe χ p = 1 ∧ z ≤ p) := by
    intro p hp
    rw [hQ] at hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  have hpsum : ∑ p ∈ Q, (1 : ℝ) / p ≤ PretenseSum χ (2 * x + 2) / Real.log z := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hQsub fun p _ _ => by positivity)
      (sum_inv_plusprime_le_pretense χ z (2 * x + 2) hz1)
  -- assemble
  have hLw : Lwin x ≠ 0 := (lt_of_lt_of_le one_pos (erT1_Lwin_ge_one hx1)).ne'
  have hlz : Real.log z ≠ 0 := hlogzpos.ne'
  have hPS0 := erT1_pretense_nonneg χ (2 * x + 2)
  have hcardR : (S.card : ℝ)
      = ∑ p ∈ Q, ((S.filter (fun n => (n + 2).minFac = p)).card : ℝ) := by
    exact_mod_cast hcard
  calc ∑ n ∈ S, Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ ∑ _n ∈ S, Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2 := Finset.sum_le_sum hW
    _ = (S.card : ℝ) * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (∑ p ∈ Q, ((S.filter (fun n => (n + 2).minFac = p)).card : ℝ))
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2) := by rw [hcardR]
    _ ≤ (∑ p ∈ Q, 524288 * ((x : ℝ) / p) / Real.log z ^ 2)
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2) :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum hfiber) (by positivity)
    _ = (∑ p ∈ Q, 524288 * ((x : ℝ) / Real.log z ^ 2) * ((1 : ℝ) / p))
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2) := by
        refine congrArg (fun s => s * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2)) ?_
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = 524288 * ((x : ℝ) / Real.log z ^ 2) * (∑ p ∈ Q, (1 : ℝ) / p)
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2) := by
        rw [← Finset.mul_sum]
    _ ≤ 524288 * ((x : ℝ) / Real.log z ^ 2) * (PretenseSum χ (2 * x + 2) / Real.log z)
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpsum (by positivity)) (by positivity)
    _ = 524288 * (((x : ℝ) / Lwin x) * (z0 z x ^ 3 * Real.exp (Real.log 2 * z0 z x))
          * PretenseSum χ (2 * x + 2)) := by
        rw [z0]
        field_simp
    _ ≤ 524288 * (((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2)) := by
        have habs := erT1_z0_cube_absorb (x := x) hz100 hx1
        have hA : (0 : ℝ) ≤ (x : ℝ) / Lwin x := div_nonneg (by positivity) (Lwin_nonneg x)
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hA) hPS0
    _ = 524288 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by ring

/-! ## §4 — the exact cover and the mixed budget -/

/-- **The `T1'` subclass cover.**  The all-plus first summand of `ER_prime_cover` splits
    exactly into its prime-power and composite-plus-part slices. -/
lemma ER_T1'_split (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    (∑ n ∈ (l2cWindow χ z x).filter (fun n => n.Prime ∧ nMinus χ (n + 2) = 1),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
      = (∑ n ∈ (l2cWindow χ z x).filter
            (fun n => n.Prime ∧ nMinus χ (n + 2) = 1 ∧ IsPrimePow (n + 2)),
            Λ n * (LamTilde χ (n + 2) - Λ (n + 2)))
        + ∑ n ∈ (l2cWindow χ z x).filter
            (fun n => n.Prime ∧ nMinus χ (n + 2) = 1 ∧ ¬ IsPrimePow (n + 2)),
            Λ n * (LamTilde χ (n + 2) - Λ (n + 2)) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
        ((l2cWindow χ z x).filter (fun n => n.Prime ∧ nMinus χ (n + 2) = 1))
        (fun n => IsPrimePow (n + 2))]
  congr 1
  · rw [Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun n _ => ?_) fun _ _ => rfl
    tauto
  · rw [Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun n _ => ?_) fun _ _ => rfl
    tauto

/-- On the window with `x ≥ 2`, a prime element is odd (it exceeds `x ≥ 2`).  The
    member-level form of the house-amendment-#2 parity guard for the `T1'` family. -/
lemma erT1_mem_odd (χ : DirichletCharacter ℂ q) {z x n : ℕ} (hx2 : 2 ≤ x)
    (hn : n ∈ l2cWindow χ z x) (hp : n.Prime) : Odd n := by
  have hxn : x < n := (Finset.mem_Ioc.mp (l2cWindow_subset χ z x hn)).1
  exact hp.odd_of_ne_two (by omega)

/-- **The house-amendment-#2 (catch #246) parity guard, explicit.**  The `T1'` family
    filter already excludes even elements — `n` is a prime `> x ≥ 2`, hence odd, in
    every `χ_ℝ(2)` case (when `χ_ℝ(2) = −1` the all-plus condition `(n+2)₋ = 1`
    independently kills even `n+2`, since `2^e` would sit in `(n+2)₋`).  The guarded
    (`Odd n`, one-predicate) and un-guarded filters coincide, so the un-guarded slice
    statements above match both the frozen `ER_prime_cover` summand and the amended
    guarded shape. -/
lemma ER_T1'_odd_guard (χ : DirichletCharacter ℂ q) {z x : ℕ} (hx2 : 2 ≤ x) :
    (l2cWindow χ z x).filter (fun n => n.Prime ∧ nMinus χ (n + 2) = 1)
      = (l2cWindow χ z x).filter
          (fun n => Odd n ∧ n.Prime ∧ nMinus χ (n + 2) = 1) := by
  classical
  refine Finset.filter_congr fun n hn => ?_
  constructor
  · rintro ⟨hp, h1⟩
    exact ⟨erT1_mem_odd χ hx2 hn hp, hp, h1⟩
  · rintro ⟨-, hp, h1⟩
    exact ⟨hp, h1⟩

/-- **The honest `T1'` budget (the Zeno partial).**  The full all-plus subclass obeys the
    `J1 + J2` mixed bound.  This is NOT the frozen `ER_T1'_bound` shape (`≤ Cmain·x/z₀`),
    which is unprovable as stated — see the module docstring and §5 NOTES. -/
theorem ER_T1'_bound_mixed (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hz8 : Lwin x ^ 8 ≤ (z : ℝ)) (hzx : (z : ℝ) ^ 3 ≤ (x : ℝ)) :
    ∑ n ∈ (l2cWindow χ z x).filter (fun n => n.Prime ∧ nMinus χ (n + 2) = 1),
        Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ 4 * ((x : ℝ) / z0 z x)
        + 524288 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by
  rw [ER_T1'_split χ z x]
  exact add_le_add (ER_T1'_pp_bound χ hsq hz100 hz8 hzx)
    (ER_T1'_comp_bound χ hsq hz100 hz8 hzx)

/-! ## §5 — NOTES: the refuted frozen shape (W3/Fable input)

The frozen `ER_T1'_bound` (`the full first summand ≤ Cmain·(x / z0 z x)`, `Cmain`
absolute) is NOT stated in this file, per iron rule 1.  The precise gap:

* **The class carries an exponential weight.**  On all-plus `M = n+2`,
  `Λ̃(M) = 2^{ω}(log M − log rad M) + 2^{ω−1}log rad M`; `ω(M)` is unbounded on the
  subclass (up to `z₀`), so per-term weights reach `e^{(log 2)z₀}L'` — which `J1`
  forbids and `J2` absorbs.
* **Truth-level violation at principal `χ`.**  For `q = 1`, `χ = 1` (allowed by
  `hsq`), the composite slice contains all `p ∈ (x,2x]` prime with `p+2 = QR`,
  `Q, R ≥ z` prime; each term is `≥ 2Λ(p)·log(p+2) ≈ 2L'²` and quantitative
  Hardy–Littlewood counts give `≍ x·log z₀ / 1` for the slice total after weight;
  at the packet corner `z ≍ L'⁸` (`z₀ ≍ L'/(8 log L') → ∞`) this exceeds
  `Cmain·x/z₀` for every fixed `Cmain`.
* **Provenance of the bug.**  `E_L` routes its all-plus class (`v = 1`, `n₊`
  composite) through `EL_T2_bound` (`J2`); the E_R roles-swap restated `T2'` as
  "single-block" (`w` a prime power), orphaning the `w = 1` composite-plus-part
  class into the `J1` row — the freeze's own `R6 COVER COMPLETENESS` open risk,
  realized.  Repair options (Fable/human tier): re-route the class into the `J2`
  ledger (consume `ER_T1'_bound_mixed` above; conclusion shapes of the other rows
  unchanged), or add a `z₀`-cap hypothesis matching the G2 window discipline.
* **Toolkit note.**  Even the slice's true size `≍ x·log z₀` is not reachable at
  `J1` grade with the repo's Mertens-1st-only toolkit (`Σ_{z≤p≤N} 1/p ≤ z₀ + c`
  is the only prime-reciprocal bound; the `log z₀`-grade Mertens-2nd is absent),
  so no proof-layer fix exists at any tier without new imported analysis.

What IS landed: `ER_T1'_split` (exact cover), `ER_T1'_pp_bound` (`≤ 4·x/z₀`, true
`J1`), `ER_T1'_comp_bound` (`≤ 524288·(x/L')·e^{5z₀}·PS(2x+2)`, the exact frozen `J2`
row shape), `ER_T1'_bound_mixed` (their sum), and — house amendment #2 (catch #246) —
`ER_T1'_odd_guard`/`erT1_mem_odd`: the parity guard is explicit and *implied* on this
family (`n` prime `> x ≥ 2` is odd in every `χ_ℝ(2)` case), so the guarded and
un-guarded filters coincide and the even-corner row does not intersect `T1'`.  At the
Horn-A consumption site (exceptional `χ`, `PS ≤ CL(log η)^{−1/2}`, `z₀` bounded) the
mixed bound recovers the intended `J1` grade. -/

end Salt.HB
