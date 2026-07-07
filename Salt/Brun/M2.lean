/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun
import Salt.Brun.CongruenceCounting
import Salt.Brun.M4

/-!
# M2 — twin-prime instantiation (blueprint milestone)

Definitions and properties of the sieve function for twin primes.
-/

/-- N2.1: Density of solutions to `n(n+2) ≡ 0 (mod d)`.
Counts the number of residue classes modulo `d` where `n(n+2) ≡ 0`.
-/
noncomputable def rho (d : ℕ) : ℕ :=
  if h : d = 0 then 0
  else
    haveI : NeZero d := ⟨h⟩
    Finset.card (Finset.univ.filter (fun n : ZMod d => n * (n + 2) = 0))

/-- Unfolds `rho d` for `d ≠ 0` into the filtered `Finset.card` expression. -/
lemma rho_pos {d : ℕ} (hd : d ≠ 0) [NeZero d] :
    rho d = Finset.card (Finset.univ.filter (fun n : ZMod d => n * (n + 2) = 0)) := by
  simp only [rho, dif_neg hd]

/-- The map `n ↦ n * (n + 2)` is strictly monotone on ℕ. -/
lemma twinProd_strictMono : ∀ m n : ℕ, m < n → m * (m + 2) < n * (n + 2) := by
  intros m n hmn
  have : m + 2 > 0 := by omega
  have : n > m := hmn
  calc m * (m + 2)
      < n * (m + 2) := Nat.mul_lt_mul_of_pos_right hmn (by omega)
    _ < n * (n + 2) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)

/-- Solutions to `n(n+2) = 0` in `ZMod p` for prime `p` are exactly `{0, -2}`. -/
lemma sol_set (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter (fun n : ZMod p => n * (n + 2) = 0)) = {0, -2} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · left; exact h1
    · right; linear_combination h2
  · rintro (h1 | h2)
    · simp [h1]
    · rw [h2]; ring

/-- N2.3 (part 1): `rho 2 = 1` — the only solution mod 2 is `n = 0`
(since `0 = -2` in `ZMod 2`). -/
theorem rho_two : rho 2 = 1 := by decide

/-- N2.3 (part 2): `rho p = 2` for odd prime `p` — the solutions `0` and `-2`
are distinct in `ZMod p` since `p ∤ 2`. -/
theorem rho_odd_prime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : rho p = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [rho_pos hp.ne_zero, sol_set p]
  have hne : (0 : ZMod p) ≠ -2 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := neg_eq_zero.mp h.symm
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

/-- N2.1 roots, represented as naturals in `[0, d)` via `ZMod.val`. -/
noncomputable def Rnat (d : ℕ) [NeZero d] : Finset ℕ :=
  (Finset.univ.filter (fun n : ZMod d => n * (n + 2) = 0)).image ZMod.val

lemma Rnat_card (d : ℕ) [NeZero d] : (Rnat d).card = rho d := by
  rw [rho_pos (NeZero.ne d)]
  exact Finset.card_image_of_injective _ (ZMod.val_injective d)

lemma Rnat_subset_range (d : ℕ) [NeZero d] : Rnat d ⊆ Finset.range d := by
  intro r hr
  simp only [Rnat, Finset.mem_image] at hr
  obtain ⟨n, _, rfl⟩ := hr
  simp [ZMod.val_lt]

lemma dvd_iff_mem_Rnat (d : ℕ) [NeZero d] (n : ℕ) : d ∣ n * (n + 2) ↔ n % d ∈ Rnat d := by
  simp only [Rnat, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hdvd
    refine ⟨(n : ZMod d), ?_, ?_⟩
    · have : ((n * (n + 2) : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      push_cast at this
      convert this using 2
    · rw [ZMod.val_natCast]
  · rintro ⟨m, hm, hmn⟩
    have heq : (n : ZMod d) = m := by
      rw [← ZMod.natCast_mod n d, ← hmn, ZMod.natCast_val, ZMod.cast_id]
    have : ((n * (n + 2) : ℕ) : ZMod d) = 0 := by push_cast; rw [heq]; exact hm
    rwa [ZMod.natCast_eq_zero_iff] at this

/-- Membership in `Rnat d` for a representative already below `d`. -/
lemma mem_Rnat_iff {d : ℕ} [NeZero d] (r : ℕ) (hr : r < d) : r ∈ Rnat d ↔ d ∣ r * (r + 2) := by
  rw [dvd_iff_mem_Rnat d r, Nat.mod_eq_of_lt hr]

lemma Rnat_lt {d : ℕ} [NeZero d] {r : ℕ} (hr : r ∈ Rnat d) : r < d :=
  Finset.mem_range.mp (Rnat_subset_range d hr)

/-- N2.2: `rho` is multiplicative on coprime moduli. Solutions to `n(n+2)≡0`
mod `m*n` correspond bijectively, via CRT, to pairs of solutions mod `m` and
mod `n`. -/
theorem rho_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : m.Coprime n) :
    rho (m * n) = rho m * rho n := by
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (m * n) := ⟨mul_ne_zero hm hn⟩
  rw [← Rnat_card (m * n), ← Rnat_card m, ← Rnat_card n, ← Finset.card_product]
  apply Finset.card_bij (fun r _ => (r % m, r % n))
  · intro r hr
    have hrlt : r < m * n := Rnat_lt hr
    have hdvd : m * n ∣ r * (r + 2) := (mem_Rnat_iff r hrlt).mp hr
    simp only [Finset.mem_product]
    refine ⟨(mem_Rnat_iff _ (Nat.mod_lt r hm.bot_lt)).mpr ?_,
      (mem_Rnat_iff _ (Nat.mod_lt r hn.bot_lt)).mpr ?_⟩
    · have hm' : m ∣ r * (r + 2) := (dvd_mul_right m n).trans hdvd
      have hcong : (r % m) * (r % m + 2) ≡ r * (r + 2) [MOD m] :=
        (Nat.mod_modEq r m).mul ((Nat.mod_modEq r m).add_right 2)
      exact (Nat.modEq_zero_iff_dvd).mp (hcong.trans (Nat.modEq_zero_iff_dvd.mpr hm'))
    · have hn' : n ∣ r * (r + 2) := (dvd_mul_left n m).trans hdvd
      have hcong : (r % n) * (r % n + 2) ≡ r * (r + 2) [MOD n] :=
        (Nat.mod_modEq r n).mul ((Nat.mod_modEq r n).add_right 2)
      exact (Nat.modEq_zero_iff_dvd).mp (hcong.trans (Nat.modEq_zero_iff_dvd.mpr hn'))
  · intro r1 h1 r2 h2 heq
    have hlt1 : r1 < m * n := Rnat_lt h1
    have hlt2 : r2 < m * n := Rnat_lt h2
    simp only [Prod.mk.injEq] at heq
    have hm : r1 ≡ r2 [MOD m] := heq.1
    have hn : r1 ≡ r2 [MOD n] := heq.2
    have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hm, hn⟩
    exact (Nat.mod_eq_of_lt hlt1) ▸ (Nat.mod_eq_of_lt hlt2) ▸ this
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product] at hab
    have halt : a < m := Rnat_lt hab.1
    have hblt : b < n := Rnat_lt hab.2
    obtain ⟨k, hka, hkb⟩ := Nat.chineseRemainder hcop a b
    set r := k % (m * n) with hr_def
    have hrm : r ≡ k [MOD m] := by
      rw [Nat.ModEq, hr_def, Nat.mod_mod_of_dvd _ (dvd_mul_right m n)]
    have hrn : r ≡ k [MOD n] := by
      rw [Nat.ModEq, hr_def, Nat.mod_mod_of_dvd _ (dvd_mul_left n m)]
    have hra : r ≡ a [MOD m] := hrm.trans hka
    have hrb : r ≡ b [MOD n] := hrn.trans hkb
    have hfa : r % m = a := by
      have h : r % m = a % m := hra
      rwa [Nat.mod_eq_of_lt halt] at h
    have hfb : r % n = b := by
      have h : r % n = b % n := hrb
      rwa [Nat.mod_eq_of_lt hblt] at h
    refine ⟨r, ?_, Prod.ext hfa hfb⟩
    apply (mem_Rnat_iff r (Nat.mod_lt k (Nat.pos_of_ne_zero (mul_ne_zero hm hn)))).mpr
    have hma : m ∣ a * (a + 2) := (mem_Rnat_iff a halt).mp hab.1
    have hnb : n ∣ b * (b + 2) := (mem_Rnat_iff b hblt).mp hab.2
    have hcm : r * (r + 2) ≡ a * (a + 2) [MOD m] := hra.mul (hra.add_right 2)
    have hcn : r * (r + 2) ≡ b * (b + 2) [MOD n] := hrb.mul (hrb.add_right 2)
    have hdm : m ∣ r * (r + 2) :=
      (Nat.modEq_zero_iff_dvd).mp (hcm.trans (Nat.modEq_zero_iff_dvd.mpr hma))
    have hdn : n ∣ r * (r + 2) :=
      (Nat.modEq_zero_iff_dvd).mp (hcn.trans (Nat.modEq_zero_iff_dvd.mpr hnb))
    exact hcop.mul_dvd_of_dvd_of_dvd hdm hdn

/-- N2.4: the count of `n ∈ Icc 1 N` with `d ∣ n(n+2)` differs from the
expected `N * rho d / d` by at most `rho d`. -/
theorem progression_count_bound (d N : ℕ) (hd : d ≠ 0) :
    haveI : NeZero d := ⟨hd⟩
    |(((Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2))).card : ℝ) - N * rho d / d| ≤ rho d := by
  haveI : NeZero d := ⟨hd⟩
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hset_eq :
      ((Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2))).card = congCount d (Rnat d) N := by
    unfold congCount
    congr 1
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hdvd⟩
      exact ⟨hn, (dvd_iff_mem_Rnat d n).mp hdvd⟩
    · rintro ⟨hn, hmem⟩
      exact ⟨hn, (dvd_iff_mem_Rnat d n).mpr hmem⟩
  rw [hset_eq]
  have hbound := congCount_bound d (Rnat d) hdpos N
  have hinter : Rnat d ∩ Finset.range d = Rnat d := Finset.inter_eq_left.mpr (Rnat_subset_range d)
  rwa [hinter, Rnat_card d] at hbound

lemma omega_mul_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : m.Coprime n) :
    omega (m * n) = omega m + omega n := by
  unfold omega
  rw [Nat.primeFactors_mul hm hn, Finset.card_union_of_disjoint hcop.disjoint_primeFactors]

lemma omega_prime {p : ℕ} (hp : p.Prime) : omega p = 1 := by
  unfold omega
  rw [hp.primeFactors, Finset.card_singleton]

/-- N2.7 (part 2): `rho d ≤ 2^ω(d)` for squarefree `d`. Each prime factor
contributes at most a factor of `2` to `rho` (by `rho_two`/`rho_odd_prime`),
and `rho` is multiplicative on the (pairwise coprime) distinct prime factors
of a squarefree number. Part 1 (`|rem d| ≤ rho d`) is `progression_count_bound`
above, once `rem` is instantiated against the eventual sieve (N2.6). -/
theorem rho_squarefree_le : ∀ d : ℕ, Squarefree d → rho d ≤ 2 ^ omega d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases eq_or_ne d 1 with rfl | hd1
    · have h1 : rho 1 = 1 := by decide
      have h2 : omega 1 = 0 := by simp [omega, Nat.primeFactors_one]
      rw [h1, h2]; norm_num
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
      obtain ⟨d', rfl⟩ := hpd
      have hcop : p.Coprime d' := (Nat.squarefree_mul_iff.mp hd).1
      have hd'sq : Squarefree d' := (Nat.squarefree_mul_iff.mp hd).2.2
      have hd'ne0 : d' ≠ 0 := hd'sq.ne_zero
      have hd'lt : d' < p * d' := by
        have h2 := hp.two_le
        have hpos := hd'sq.ne_zero.bot_lt
        nlinarith
      have hind : rho d' ≤ 2 ^ omega d' := ih d' hd'lt hd'sq
      have hrhop : rho p ≤ 2 := by
        rcases eq_or_ne p 2 with rfl | hpodd
        · rw [rho_two]; norm_num
        · rw [rho_odd_prime hp hpodd]
      rw [rho_mul_of_coprime hp.ne_zero hd'ne0 hcop, omega_mul_coprime hp.ne_zero hd'ne0 hcop,
        omega_prime hp, pow_add, pow_one]
      exact Nat.mul_le_mul hrhop hind

/-- The error in approximating the count of `n ∈ Icc 1 N` with `d ∣ n(n+2)`
by its expected value `N * rho d / d` (the sieve's `rem`, before an actual
`SelbergSieve` instance exists to state it via `s.rem` — see N2.6). -/
noncomputable def rem (d N : ℕ) : ℝ :=
  (((Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2))).card : ℝ) - N * rho d / d

/-- N2.7 (part 1, restated): `|rem d| ≤ rho d`, i.e. `progression_count_bound`
in terms of `rem`. -/
lemma rem_abs_le (d N : ℕ) (hd : d ≠ 0) : |rem d N| ≤ rho d :=
  progression_count_bound d N hd

lemma sum_cube_le_pow4 (y : ℕ) : ∑ d ∈ Finset.range y, d ^ 3 ≤ y ^ 4 := by
  calc ∑ d ∈ Finset.range y, d ^ 3
      ≤ ∑ _d ∈ Finset.range y, y ^ 3 := by
        apply Finset.sum_le_sum
        intro d hd
        simp only [Finset.mem_range] at hd
        exact Nat.pow_le_pow_left hd.le 3
    _ = y * y ^ 3 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ = y ^ 4 := by ring

/-- N4.2: `Σ_{d<y, squarefree} 3^ω(d) * |rem d| ≤ y⁴`. Combines `rem_abs_le`
(N2.7 part 1) with `rho_squarefree_le` (N2.7 part 2, giving
`3^ω(d)*rho(d) ≤ 6^ω(d)`), then `six_pow_omega_le_d_cubed` (N4.1,
`6^ω(d) ≤ d³`), then the crude bound `Σ_{d<y} d³ ≤ y⁴`. -/
theorem N4_2 (y N : ℕ) :
    ∑ d ∈ (Finset.range y).filter Squarefree, (3 : ℝ) ^ omega d * |rem d N|
      ≤ (y : ℝ) ^ 4 := by
  have step1 : ∑ d ∈ (Finset.range y).filter Squarefree, (3 : ℝ) ^ omega d * |rem d N|
      ≤ ∑ d ∈ (Finset.range y).filter Squarefree, (6 : ℝ) ^ omega d := by
    apply Finset.sum_le_sum
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    have hdne : d ≠ 0 := hd.2.ne_zero
    have h1 : |rem d N| ≤ (rho d : ℝ) := rem_abs_le d N hdne
    have h2 : (rho d : ℝ) ≤ 2 ^ omega d := by exact_mod_cast rho_squarefree_le d hd.2
    calc (3 : ℝ) ^ omega d * |rem d N| ≤ (3 : ℝ) ^ omega d * (rho d : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (3 : ℝ) ^ omega d * 2 ^ omega d := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 6 ^ omega d := by rw [← mul_pow]; norm_num
  have step2 : ∑ d ∈ (Finset.range y).filter Squarefree, (6 : ℝ) ^ omega d
      ≤ ∑ d ∈ (Finset.range y).filter Squarefree, (d : ℝ) ^ 3 := by
    apply Finset.sum_le_sum
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    exact_mod_cast six_pow_omega_le_d_cubed hd.2
  have step3 : ∑ d ∈ (Finset.range y).filter Squarefree, (d : ℝ) ^ 3
      ≤ ∑ d ∈ Finset.range y, (d : ℝ) ^ 3 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intros; positivity
  have step4 : ∑ d ∈ Finset.range y, (d : ℝ) ^ 3 ≤ (y : ℝ) ^ 4 := by
    have hnat := sum_cube_le_pow4 y
    calc ∑ d ∈ Finset.range y, (d : ℝ) ^ 3
        = ((∑ d ∈ Finset.range y, d ^ 3 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (y : ℝ) ^ 4 := by exact_mod_cast hnat
  linarith [step1, step2, step3, step4]
