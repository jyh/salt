/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Brun.CongruenceCounting

/-!
# GB-M2 — the binary-Goldbach local density (rebuild nodes GB-1..GB-4)

The Goldbach-sieve analogue of the twin track's `Salt/Brun/M2.lean`, for the
polynomial `m ↦ m * (n - m)` with `n` a PARAMETER (`n` even where the sieve
uses it). Everything mirrors the twin `rho`/`Rnat`/CRT chain, but the local
roots now depend on `n`: modulo a prime `p` the solution set is `{0, ↑n}`, so
the two roots coincide exactly when `p ∣ n` (the singular-series structure).

Canonical internal condition. Truncated ℕ subtraction `n - m` is NOT periodic
in `m`, so the CRT bookkeeping runs on the subtraction-free congruence
`m * n ≡ m * m [MOD d]` (equal to `d ∣ m * (n - m)` whenever `m ≤ n`).

* **GB-1** `rhoG`, `RnatG`, `sol_setG` — the local roots.
* **GB-2** `rhoG_prime_dvd` / `rhoG_prime_not_dvd` — the values `1` / `2`.
* **GB-3** `rhoG_mul_of_coprime` — CRT multiplicativity.
* **GB-4** `rhoG_squarefree_le`, `goldProgression_count_bound` — count + remainder.
-/

namespace Salt.Entropy.Chowla

/-- GB-1: density of solutions to `m * (n - m) ≡ 0 (mod d)`. Counts the residue
classes `m : ZMod d` with `m * (↑n - m) = 0`. -/
noncomputable def rhoG (n d : ℕ) : ℕ :=
  if h : d = 0 then 0
  else
    haveI : NeZero d := ⟨h⟩
    Finset.card (Finset.univ.filter (fun m : ZMod d => m * ((n : ZMod d) - m) = 0))

/-- Unfolds `rhoG n d` for `d ≠ 0` into the filtered `Finset.card` expression. -/
lemma rhoG_pos {n d : ℕ} (hd : d ≠ 0) [NeZero d] :
    rhoG n d =
      Finset.card (Finset.univ.filter (fun m : ZMod d => m * ((n : ZMod d) - m) = 0)) := by
  simp only [rhoG, dif_neg hd]

/-- GB-1 roots, represented as naturals in `[0, d)` via `ZMod.val`. -/
noncomputable def RnatG (n d : ℕ) [NeZero d] : Finset ℕ :=
  (Finset.univ.filter (fun m : ZMod d => m * ((n : ZMod d) - m) = 0)).image ZMod.val

lemma RnatG_card (n d : ℕ) [NeZero d] : (RnatG n d).card = rhoG n d := by
  rw [rhoG_pos (NeZero.ne d)]
  exact Finset.card_image_of_injective _ (ZMod.val_injective d)

lemma RnatG_subset_range (n d : ℕ) [NeZero d] : RnatG n d ⊆ Finset.range d := by
  intro r hr
  simp only [RnatG, Finset.mem_image] at hr
  obtain ⟨m, _, rfl⟩ := hr
  simp [ZMod.val_lt]

lemma RnatG_lt {n d : ℕ} [NeZero d] {r : ℕ} (hr : r ∈ RnatG n d) : r < d :=
  Finset.mem_range.mp (RnatG_subset_range n d hr)

/-- `RnatG n 1 = {0}`, so `rhoG n 1 = 1` (base case for the squarefree bound). -/
lemma rhoG_one {n : ℕ} : rhoG n 1 = 1 := by
  rw [rhoG_pos (n := n) one_ne_zero,
    Finset.filter_true_of_mem (fun m _ => Subsingleton.elim _ _)]
  decide

/-- Solutions to `m * (n - m) = 0` in `ZMod p` for prime `p` are exactly
`{0, ↑n}` (roots `m = 0` and `m = ↑n`). -/
lemma sol_setG (n p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter (fun m : ZMod p => m * ((n : ZMod p) - m) = 0))
      = {0, (n : ZMod p)} := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · left; exact h1
    · right; rw [sub_eq_zero] at h2; exact h2.symm
  · rintro (h1 | h2)
    · rw [h1]; ring
    · rw [h2]; ring

/-- GB-2: `rhoG n p = 1` for a prime `p ∣ n` — the roots `0` and `↑n` coincide
(this is the `p = 2`, `n` even case among others). -/
theorem rhoG_prime_dvd {n p : ℕ} (hp : p.Prime) (h : p ∣ n) : rhoG n p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [rhoG_pos hp.ne_zero, sol_setG n p]
  have hn0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr h
  rw [hn0, Finset.pair_eq_singleton, Finset.card_singleton]

/-- GB-2: `rhoG n p = 2` for a prime `p ∤ n` — the roots `0` and `↑n` are
distinct (this is the `p = 2`, `n` odd case among others). -/
theorem rhoG_prime_not_dvd {n p : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) : rhoG n p = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [rhoG_pos hp.ne_zero, sol_setG n p]
  have hne : (0 : ZMod p) ≠ (n : ZMod p) := by
    intro heq
    exact h ((ZMod.natCast_eq_zero_iff n p).mp heq.symm)
  rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

/-- The `ZMod` root equation is the subtraction-free congruence
`r * n ≡ r * r [MOD d]` (uses `r * (n - r) = r * n - r * r`). -/
lemma zmod_eq_iff_congr {n d : ℕ} (r : ℕ) :
    ((r : ZMod d) * ((n : ZMod d) - r) = 0) ↔ r * n ≡ r * r [MOD d] := by
  have key : ((r : ZMod d) * ((n : ZMod d) - r) = 0)
      ↔ ((r * n : ℕ) : ZMod d) = ((r * r : ℕ) : ZMod d) := by
    push_cast
    constructor <;> intro h <;> linear_combination h
  rw [key]
  exact ZMod.natCast_eq_natCast_iff _ _ _

/-- Membership in `RnatG` for a representative below `d`, in `ZMod` form. -/
lemma mem_RnatG_iff_zmod {n d : ℕ} [NeZero d] {r : ℕ} (hr : r < d) :
    r ∈ RnatG n d ↔ (r : ZMod d) * ((n : ZMod d) - r) = 0 := by
  simp only [RnatG, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨m, hm, hmr⟩
    have hmeq : (r : ZMod d) = m := by rw [← hmr, ZMod.natCast_zmod_val]
    rw [hmeq]; exact hm
  · intro h
    exact ⟨(r : ZMod d), h, by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hr]⟩

/-- Membership in `RnatG` for `r < d`, as the canonical congruence. -/
lemma mem_RnatG_iff {n d : ℕ} [NeZero d] {r : ℕ} (hr : r < d) :
    r ∈ RnatG n d ↔ r * n ≡ r * r [MOD d] := by
  rw [mem_RnatG_iff_zmod hr, zmod_eq_iff_congr]

/-- For `m ≤ n`, divisibility `d ∣ m * (n - m)` is the canonical congruence
`m * n ≡ m * m [MOD d]` (uses `m * (n - m) + m * m = m * n`). -/
lemma dvd_iff_congr {n d m : ℕ} (hmn : m ≤ n) :
    d ∣ m * (n - m) ↔ m * n ≡ m * m [MOD d] := by
  have key : m * (n - m) + m * m = m * n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hmn]
  constructor
  · intro hdvd
    calc m * n = m * (n - m) + m * m := key.symm
      _ ≡ 0 + m * m [MOD d] := (Nat.modEq_zero_iff_dvd.mpr hdvd).add_right _
      _ = m * m := Nat.zero_add _
  · intro hcong
    apply Nat.modEq_zero_iff_dvd.mp
    have h2 : m * (n - m) + m * m ≡ 0 + m * m [MOD d] := by
      rw [key, Nat.zero_add]; exact hcong
    exact Nat.ModEq.add_right_cancel' (m * m) h2

/-- The canonical congruence depends on `m` only through `m % d`. -/
lemma congr_mod {n d m : ℕ} :
    (m * n ≡ m * m [MOD d]) ↔ ((m % d) * n ≡ (m % d) * (m % d) [MOD d]) := by
  have hm : m % d ≡ m [MOD d] := Nat.mod_modEq m d
  constructor
  · intro h
    calc (m % d) * n ≡ m * n [MOD d] := hm.mul_right n
      _ ≡ m * m [MOD d] := h
      _ ≡ (m % d) * (m % d) [MOD d] := (hm.mul hm).symm
  · intro h
    calc m * n ≡ (m % d) * n [MOD d] := hm.symm.mul_right n
      _ ≡ (m % d) * (m % d) [MOD d] := h
      _ ≡ m * m [MOD d] := hm.mul hm

/-- For `m ≤ n`, `d ∣ m * (n - m)` iff `m % d` is a root modulo `d`. -/
lemma dvd_iff_mem_RnatG {n d : ℕ} [NeZero d] {m : ℕ} (hmn : m ≤ n) :
    d ∣ m * (n - m) ↔ m % d ∈ RnatG n d := by
  rw [dvd_iff_congr hmn, congr_mod,
    ← mem_RnatG_iff (Nat.mod_lt m (Nat.pos_of_ne_zero (NeZero.ne d)))]

/-- GB-3: `rhoG n` is multiplicative on coprime moduli. Solutions modulo
`a * b` correspond bijectively, via CRT, to pairs of solutions modulo `a` and
modulo `b`. -/
theorem rhoG_mul_of_coprime {n a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : a.Coprime b) : rhoG n (a * b) = rhoG n a * rhoG n b := by
  haveI : NeZero a := ⟨ha⟩
  haveI : NeZero b := ⟨hb⟩
  haveI : NeZero (a * b) := ⟨mul_ne_zero ha hb⟩
  rw [← RnatG_card n (a * b), ← RnatG_card n a, ← RnatG_card n b, ← Finset.card_product]
  apply Finset.card_bij (fun r _ => (r % a, r % b))
  · intro r hr
    have hrlt : r < a * b := RnatG_lt hr
    have hcong : r * n ≡ r * r [MOD a * b] := (mem_RnatG_iff hrlt).mp hr
    simp only [Finset.mem_product]
    refine ⟨(mem_RnatG_iff (Nat.mod_lt r ha.bot_lt)).mpr ?_,
      (mem_RnatG_iff (Nat.mod_lt r hb.bot_lt)).mpr ?_⟩
    · exact congr_mod.mp (hcong.of_mul_right b)
    · exact congr_mod.mp (hcong.of_mul_left a)
  · intro r1 h1 r2 h2 heq
    have hlt1 : r1 < a * b := RnatG_lt h1
    have hlt2 : r2 < a * b := RnatG_lt h2
    simp only [Prod.mk.injEq] at heq
    have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨heq.1, heq.2⟩
    exact (Nat.mod_eq_of_lt hlt1) ▸ (Nat.mod_eq_of_lt hlt2) ▸ this
  · rintro ⟨x, y⟩ hxy
    simp only [Finset.mem_product] at hxy
    have hxlt : x < a := RnatG_lt hxy.1
    have hylt : y < b := RnatG_lt hxy.2
    obtain ⟨k, hkx, hky⟩ := Nat.chineseRemainder hcop x y
    set r := k % (a * b) with hr_def
    have hrx : r ≡ k [MOD a] := by
      rw [Nat.ModEq, hr_def, Nat.mod_mod_of_dvd _ (dvd_mul_right a b)]
    have hry : r ≡ k [MOD b] := by
      rw [Nat.ModEq, hr_def, Nat.mod_mod_of_dvd _ (dvd_mul_left b a)]
    have hrxx : r ≡ x [MOD a] := hrx.trans hkx
    have hryy : r ≡ y [MOD b] := hry.trans hky
    have hfx : r % a = x := by
      have h : r % a = x % a := hrxx; rwa [Nat.mod_eq_of_lt hxlt] at h
    have hfy : r % b = y := by
      have h : r % b = y % b := hryy; rwa [Nat.mod_eq_of_lt hylt] at h
    refine ⟨r, ?_, Prod.ext hfx hfy⟩
    apply (mem_RnatG_iff (show r < a * b from
      Nat.mod_lt k (Nat.pos_of_ne_zero (mul_ne_zero ha hb)))).mpr
    have hax : x * n ≡ x * x [MOD a] := (mem_RnatG_iff hxlt).mp hxy.1
    have hby : y * n ≡ y * y [MOD b] := (mem_RnatG_iff hylt).mp hxy.2
    have hda : r * n ≡ r * r [MOD a] :=
      (hrxx.mul_right n).trans (hax.trans (hrxx.mul hrxx).symm)
    have hdb : r * n ≡ r * r [MOD b] :=
      (hryy.mul_right n).trans (hby.trans (hryy.mul hryy).symm)
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hda, hdb⟩

/-- GB-4: `rhoG n d ≤ 2 ^ ω(d)` for squarefree `d`. Each prime factor
contributes at most `2` (`rhoG n p ≤ 2` uniformly), and `rhoG n` is
multiplicative on the pairwise-coprime distinct prime factors. -/
theorem rhoG_squarefree_le (n : ℕ) :
    ∀ d : ℕ, Squarefree d → rhoG n d ≤ 2 ^ d.primeFactors.card := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases eq_or_ne d 1 with rfl | hd1
    · rw [rhoG_one, Nat.primeFactors_one, Finset.card_empty]; norm_num
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
      obtain ⟨d', rfl⟩ := hpd
      have hcop : p.Coprime d' := (Nat.squarefree_mul_iff.mp hd).1
      have hd'sq : Squarefree d' := (Nat.squarefree_mul_iff.mp hd).2.2
      have hd'ne0 : d' ≠ 0 := hd'sq.ne_zero
      have hd'lt : d' < p * d' := by
        have h2 := hp.two_le
        have hpos := hd'sq.ne_zero.bot_lt
        nlinarith
      have hind : rhoG n d' ≤ 2 ^ d'.primeFactors.card := ih d' hd'lt hd'sq
      have hrhop : rhoG n p ≤ 2 := by
        by_cases hpn : p ∣ n
        · rw [rhoG_prime_dvd hp hpn]; norm_num
        · rw [rhoG_prime_not_dvd hp hpn]
      rw [rhoG_mul_of_coprime hp.ne_zero hd'ne0 hcop,
        Nat.primeFactors_mul hp.ne_zero hd'ne0,
        Finset.card_union_of_disjoint hcop.disjoint_primeFactors,
        hp.primeFactors, Finset.card_singleton, pow_add, pow_one]
      exact Nat.mul_le_mul hrhop hind

/-- GB-4: the count of `m ∈ Icc 1 N` (with `N ≤ n`, so `n - m` is honest) with
`d ∣ m * (n - m)` differs from the expected `N * rhoG n d / d` by at most
`rhoG n d`. Driven by `congCount_bound` with the solution set `RnatG n d`. -/
theorem goldProgression_count_bound (n d N : ℕ) (hd : d ≠ 0) (hN : N ≤ n) :
    haveI : NeZero d := ⟨hd⟩
    |(((Finset.Icc 1 N).filter (fun m => d ∣ m * (n - m))).card : ℝ)
      - N * rhoG n d / d| ≤ rhoG n d := by
  haveI : NeZero d := ⟨hd⟩
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hset_eq :
      ((Finset.Icc 1 N).filter (fun m => d ∣ m * (n - m))).card
        = congCount d (RnatG n d) N := by
    unfold congCount
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hm1, hmN⟩, hdvd⟩
      exact ⟨⟨hm1, hmN⟩, (dvd_iff_mem_RnatG (le_trans hmN hN)).mp hdvd⟩
    · rintro ⟨⟨hm1, hmN⟩, hmem⟩
      exact ⟨⟨hm1, hmN⟩, (dvd_iff_mem_RnatG (le_trans hmN hN)).mpr hmem⟩
  rw [hset_eq]
  have hbound := congCount_bound d (RnatG n d) hdpos N
  have hinter : RnatG n d ∩ Finset.range d = RnatG n d :=
    Finset.inter_eq_left.mpr (RnatG_subset_range n d)
  rwa [hinter, RnatG_card n d] at hbound

-- Smoke tests (kernel-checked via `decide`).
example : rhoG 6 3 = 1 := by decide
example : rhoG 6 5 = 2 := by decide
example : rhoG 6 2 = 1 := by decide
example : rhoG 5 2 = 2 := by decide
example : rhoG 6 15 = 2 := by decide

end Salt.Entropy.Chowla
