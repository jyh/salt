/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Kloosterman
import Mathlib

/-!
# Weil track, Stepanov's auxiliary polynomial (W4.1a/b)

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder, ~13:30 entry), following
Harcos §5 (equations (18)–(19)). This is the heart of the Stepanov method for the
hyperelliptic point count `y² = f(x)`.

* **W4.1a — the ansatz** (`stepanovAux`): for a polynomial `f : F[X]`, exponent `ℓ`,
  parameter `J`, and coefficient data `r s : Fin J → F[X]`,
  `h_a := f^ℓ · ∑_{0≤j<J} (r_j + s_j · f^{(q-1)/2}) · X^{jq}`  (Harcos (18)),
  with `q := Fintype.card F`. Degree bookkeeping: `stepanovAux_summand_natDegree_le`
  (per block) and `stepanovAux_natDegree_le` (the total, used by the dimension count).

* **band separation** (`X_pow_dvd_of_range_sum_eq_zero`): the algebraic heart of the
  non-vanishing argument. If `∑_{j<J} g_j X^{jq} = 0` and the coefficients below the
  minimal index `i` vanish, then `X^q ∣ g_i` — the `X^{jq}` blocks isolate the lowest
  nonzero coefficient modulo `X^q`.

* **W4.1b — non-vanishing** (`stepanovAux_ne_zero`): if `f` is not a square in the
  algebraic closure and the coefficient data is not all zero (with the degree bounds
  (19) and `f(0) ≠ 0`), then `h_a ≠ 0`. Argument: were `h_a = 0`, band separation at the
  minimal nonzero index `i` gives `r_i + s_i f^{(q-1)/2} ≡ 0 (mod X^q)`; squaring and
  multiplying by `f`, together with `f^q ≡ f(0) (mod X^q)`, forces `r_i² f = f(0) s_i²`,
  so `f` is a square in `\overline{F}[X]` — a contradiction.
-/

namespace Salt.Weil

open Polynomial
open scoped BigOperators

/-! ### W4.1a — the Stepanov ansatz and its degree -/

variable {F : Type*} [Field F]

/-- **The Stepanov auxiliary polynomial** (Harcos (18)). For `f : F[X]`, exponent `ℓ`,
parameter `J`, and coefficient data `r s : Fin J → F[X]`,
`h_a := f^ℓ · ∑_{0≤j<J} (r_j + s_j · f^{(q-1)/2}) · X^{jq}`, with `q := Fintype.card F`.
The `(q-1)/2` power is the quadratic-residue twist and the `X^{jq}` windows carry the `J`
free coefficient vectors of the linear system. -/
noncomputable def stepanovAux [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X]) :
    F[X] :=
  f ^ ℓ * ∑ j : Fin J,
    (r j + s j * f ^ ((Fintype.card F - 1) / 2)) * X ^ ((j : ℕ) * Fintype.card F)

/-- **Degree of a single block** (Harcos (18)–(19)). With `deg r_j, deg s_j ≤ B`, the `j`-th
summand `(r_j + s_j f^{(q-1)/2}) X^{jq}` has degree at most `B + (q-1)/2·deg f + jq`. -/
theorem stepanovAux_summand_natDegree_le [Fintype F] {J : ℕ} (f : F[X]) (r s : Fin J → F[X])
    (j : Fin J) {B : ℕ} (hr : (r j).natDegree ≤ B) (hs : (s j).natDegree ≤ B) :
    ((r j + s j * f ^ ((Fintype.card F - 1) / 2)) * X ^ ((j : ℕ) * Fintype.card F)).natDegree
      ≤ B + (Fintype.card F - 1) / 2 * f.natDegree + (j : ℕ) * Fintype.card F := by
  have hA : (r j + s j * f ^ ((Fintype.card F - 1) / 2)).natDegree
      ≤ B + (Fintype.card F - 1) / 2 * f.natDegree := by
    refine (natDegree_add_le _ _).trans (max_le (hr.trans (Nat.le_add_right _ _)) ?_)
    exact natDegree_mul_le.trans (add_le_add hs natDegree_pow_le)
  calc ((r j + s j * f ^ ((Fintype.card F - 1) / 2)) * X ^ ((j : ℕ) * Fintype.card F)).natDegree
      ≤ (r j + s j * f ^ ((Fintype.card F - 1) / 2)).natDegree
          + ((X : F[X]) ^ ((j : ℕ) * Fintype.card F)).natDegree := natDegree_mul_le
    _ = (r j + s j * f ^ ((Fintype.card F - 1) / 2)).natDegree + (j : ℕ) * Fintype.card F := by
        rw [natDegree_X_pow]
    _ ≤ B + (Fintype.card F - 1) / 2 * f.natDegree + (j : ℕ) * Fintype.card F := by
        gcongr

/-- **Degree of the auxiliary polynomial** (Harcos, top of p. 12). With `deg r_j, deg s_j ≤ B`
for all `j`, `deg h_a ≤ ℓ·deg f + (B + (q-1)/2·deg f + (J-1)q)`. This is the input to the
dimension count that makes the linear system (22) solvable. -/
theorem stepanovAux_natDegree_le [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    {B : ℕ} (hr : ∀ j, (r j).natDegree ≤ B) (hs : ∀ j, (s j).natDegree ≤ B) :
    (stepanovAux f ℓ r s).natDegree
      ≤ ℓ * f.natDegree
        + (B + (Fintype.card F - 1) / 2 * f.natDegree + (J - 1) * Fintype.card F) := by
  unfold stepanovAux
  refine natDegree_mul_le.trans (add_le_add natDegree_pow_le ?_)
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine (stepanovAux_summand_natDegree_le f r s j (hr j) (hs j)).trans ?_
  have hj : (j : ℕ) ≤ J - 1 := by have := j.isLt; omega
  gcongr

/-! ### Band separation: the lowest `X^{jq}` block modulo `X^q` -/

/-- **Band separation lemma.** In `F[X]` (a domain), suppose the block sum
`∑_{0 ≤ j < J} g_j · X^{jq}` vanishes and every coefficient below the index `i` is zero.
Then `X^q ∣ g_i`: reducing the sum modulo `X^{(i+1)q}` kills every block except the `i`-th,
whose `X^{iq}` factor cancels to leave `X^q ∣ g_i`. This is the mechanism by which the
`X^{jq}` windows separate the coefficients in Harcos's non-vanishing argument. -/
theorem X_pow_dvd_of_range_sum_eq_zero {J q : ℕ} (g : ℕ → F[X])
    (i : ℕ) (hi : i < J) (hlow : ∀ j < i, g j = 0)
    (hsum : ∑ j ∈ Finset.range J, g j * X ^ (j * q) = 0) :
    (X : F[X]) ^ q ∣ g i := by
  -- `X^{(i+1)q}` divides the `i`-th block `g i * X^{iq}`.
  have hmem : i ∈ Finset.range J := Finset.mem_range.mpr hi
  have hdvd : (X : F[X]) ^ ((i + 1) * q) ∣ g i * X ^ (i * q) := by
    -- `g i * X^{iq}` is the negative of the erased sum.
    have hrec : g i * X ^ (i * q) = -∑ j ∈ (Finset.range J).erase i, g j * X ^ (j * q) := by
      have := Finset.sum_erase_add (Finset.range J) (fun j => g j * X ^ (j * q)) hmem
      linear_combination this + hsum
    rw [hrec, dvd_neg]
    refine Finset.dvd_sum fun j hj => ?_
    rcases Finset.mem_erase.mp hj with ⟨hji, _⟩
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · rw [hlow j hlt, zero_mul]; exact dvd_zero _
    · have hle : (i + 1) * q ≤ j * q := by gcongr; omega
      exact (pow_dvd_pow X hle).mul_left _
  -- Cancel the common `X^{iq}` factor.
  have hne : (X : F[X]) ^ (i * q) ≠ 0 := pow_ne_zero _ X_ne_zero
  rw [show (i + 1) * q = i * q + q by ring, pow_add, mul_comm (g i)] at hdvd
  exact (mul_dvd_mul_iff_left hne).mp hdvd

/-! ### W4.1b — non-vanishing of the auxiliary polynomial -/

/-- **Non-vanishing** (Harcos §5, p. 11). If `f(0) ≠ 0`, `q := Fintype.card F` is odd, the
coefficient degree bounds (19) `deg r_j, deg s_j < (q - deg f)/2` hold, `f` is *not* a square
in `\overline{F}[X]`, and the coefficient data is not all zero, then `h_a ≠ 0`.

Were `h_a = 0`, dividing by `f^ℓ` and applying band separation at the minimal nonzero index
`i` gives `X^q ∣ (r_i + s_i f^{(q-1)/2})`. Squaring (via the difference of squares) and
multiplying by `f`, together with the Frobenius identity `f^q ≡ f(0) (mod X^q)`, forces
`X^q ∣ (r_i² f - f(0) s_i²)`; the degree bounds make this polynomial have degree `< q`, so it
vanishes: `r_i² f = f(0) s_i²`. Over `\overline{F}`, `f(0)` is a square, hence `f` is a square
in `\overline{F}[X]` — contradicting the hypothesis. -/
theorem stepanovAux_ne_zero [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    (hqodd : Odd (Fintype.card F)) (hf0 : f.coeff 0 ≠ 0)
    (hr : ∀ j, (r j).natDegree < (Fintype.card F - f.natDegree) / 2)
    (hs : ∀ j, (s j).natDegree < (Fintype.card F - f.natDegree) / 2)
    (hns : ¬ ∃ g : (AlgebraicClosure F)[X],
      f.map (algebraMap F (AlgebraicClosure F)) = g ^ 2)
    (hnz : ∃ j, r j ≠ 0 ∨ s j ≠ 0) :
    stepanovAux f ℓ r s ≠ 0 := by
  classical
  intro hzero
  unfold stepanovAux at hzero
  set q := Fintype.card F with hq
  set m := f.natDegree with hm
  set e := (q - 1) / 2 with he_def
  set K := AlgebraicClosure F with hK
  set φ := algebraMap F K with hφ
  have hf : f ≠ 0 := fun h => hf0 (by rw [h]; simp)
  -- Extend the coefficient data to `ℕ → F[X]` by zero, and form the block coefficients `g`.
  set R : ℕ → F[X] := fun n => if h : n < J then r ⟨n, h⟩ else 0 with hR
  set S : ℕ → F[X] := fun n => if h : n < J then s ⟨n, h⟩ else 0 with hS
  set g : ℕ → F[X] := fun n => R n + S n * f ^ e with hg
  have hRj : ∀ j : Fin J, R (j : ℕ) = r j := by
    intro j; rw [hR]; simp only [j.isLt, dif_pos]
  have hSj : ∀ j : Fin J, S (j : ℕ) = s j := by
    intro j; rw [hS]; simp only [j.isLt, dif_pos]
  -- `∑_{j<J} g_j X^{jq} = 0`, obtained from `h_a = 0` by cancelling `f^ℓ ≠ 0`.
  have hconv : ∑ j : Fin J, (r j + s j * f ^ e) * X ^ ((j : ℕ) * q)
      = ∑ n ∈ Finset.range J, g n * X ^ (n * q) := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => g n * X ^ (n * q)) J]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg]; simp only [hRj j, hSj j]
  have hsum0 : ∑ n ∈ Finset.range J, g n * X ^ (n * q) = 0 := by
    rw [hconv] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero ℓ hf)
  -- The minimal index `i` with `(r_i, s_i) ≠ 0`.
  have hex : ∃ n, R n ≠ 0 ∨ S n ≠ 0 := by
    obtain ⟨j, hj⟩ := hnz
    exact ⟨(j : ℕ), by rw [hRj j, hSj j]; exact hj⟩
  set i := Nat.find hex with hi_def
  have hi_spec : R i ≠ 0 ∨ S i ≠ 0 := Nat.find_spec hex
  have hi_min : ∀ n < i, R n = 0 ∧ S n = 0 := by
    intro n hn
    simpa only [not_or, not_ne_iff] using Nat.find_min hex hn
  have hiJ : i < J := by
    by_contra hle
    have hR0 : R i = 0 := by simp only [hR, dif_neg hle]
    have hS0 : S i = 0 := by simp only [hS, dif_neg hle]
    exact hi_spec.elim (· hR0) (· hS0)
  -- Band separation: `X^q ∣ g_i = r_i + s_i f^{(q-1)/2}`.
  have hlow : ∀ n < i, g n = 0 := by
    intro n hn; rw [hg]; simp only [(hi_min n hn).1, (hi_min n hn).2, zero_mul, add_zero]
  have hdvd : (X : F[X]) ^ q ∣ R i + S i * f ^ e := by
    have := X_pow_dvd_of_range_sum_eq_zero g i hiJ hlow hsum0
    rwa [hg] at this
  -- Degree facts for `R i, S i`.
  have hRi_deg : (R i).natDegree < (q - m) / 2 := by rw [hRj ⟨i, hiJ⟩]; exact hr _
  have hSi_deg : (S i).natDegree < (q - m) / 2 := by rw [hSj ⟨i, hiJ⟩]; exact hs _
  have hqm : m + 2 ≤ q := by have := hRi_deg; omega
  -- Odd `q` gives `2·e + 1 = q`, hence `f^e · f^e · f = f^q`.
  obtain ⟨k, hk⟩ := hqodd
  have hfe : f ^ e * f ^ e * f = f ^ q := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  -- Frobenius: `X^q ∣ f^q - C (f 0)`.
  obtain ⟨p, hp_char, n, hp_prime, hpn⟩ := FiniteField.card' F
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : CharP F p := hp_char
  have hCcq : (C (f.coeff 0)) ^ q = C (f.coeff 0) := by
    rw [← C_pow]; congr 1; exact FiniteField.pow_card _
  have hpow : (f - C (f.coeff 0)) ^ q = f ^ q - C (f.coeff 0) := by
    have hchar := sub_pow_char_pow f (C (f.coeff 0)) n
    rw [← hpn] at hchar
    rw [hchar, hCcq]
  have hfrob : (X : F[X]) ^ q ∣ f ^ q - C (f.coeff 0) := by
    rw [← hpow]; exact pow_dvd_pow_of_dvd X_dvd_sub_C q
  -- Assemble `X^q ∣ r_i² f - C (f 0) s_i²`.
  have hexp : f * ((R i + S i * f ^ e) * (R i - S i * f ^ e))
      = (R i) ^ 2 * f - (S i) ^ 2 * f ^ q := by
    linear_combination (-(S i) ^ 2) * hfe
  have h2 : (X : F[X]) ^ q ∣ (R i) ^ 2 * f - (S i) ^ 2 * f ^ q := by
    have := (hdvd.mul_right (R i - S i * f ^ e)).mul_left f
    rwa [hexp] at this
  have h3 : (X : F[X]) ^ q ∣ (S i) ^ 2 * f ^ q - (S i) ^ 2 * C (f.coeff 0) := by
    have := hfrob.mul_left ((S i) ^ 2)
    rwa [mul_sub] at this
  have hP : (X : F[X]) ^ q ∣ (R i) ^ 2 * f - C (f.coeff 0) * (S i) ^ 2 := by
    have hadd := dvd_add h2 h3
    have heq : ((R i) ^ 2 * f - (S i) ^ 2 * f ^ q)
        + ((S i) ^ 2 * f ^ q - (S i) ^ 2 * C (f.coeff 0))
        = (R i) ^ 2 * f - C (f.coeff 0) * (S i) ^ 2 := by ring
    rwa [heq] at hadd
  -- The degree bounds force the divided polynomial to vanish.
  have hdeg : ((R i) ^ 2 * f - C (f.coeff 0) * (S i) ^ 2).natDegree < q := by
    have e1 : ((R i) ^ 2 * f).natDegree ≤ 2 * (R i).natDegree + m := by
      have hp2 : ((R i) ^ 2).natDegree ≤ 2 * (R i).natDegree := natDegree_pow_le
      calc ((R i) ^ 2 * f).natDegree ≤ ((R i) ^ 2).natDegree + f.natDegree := natDegree_mul_le
        _ ≤ 2 * (R i).natDegree + m := by omega
    have e2 : (C (f.coeff 0) * (S i) ^ 2).natDegree ≤ 2 * (S i).natDegree := by
      have hp2 : ((S i) ^ 2).natDegree ≤ 2 * (S i).natDegree := natDegree_pow_le
      calc (C (f.coeff 0) * (S i) ^ 2).natDegree
          ≤ (C (f.coeff 0)).natDegree + ((S i) ^ 2).natDegree := natDegree_mul_le
        _ ≤ 2 * (S i).natDegree := by rw [natDegree_C]; omega
    refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt e1 (by omega)
    · exact lt_of_le_of_lt e2 (by omega)
  have hPzero : (R i) ^ 2 * f - C (f.coeff 0) * (S i) ^ 2 = 0 := by
    by_contra hne
    have := natDegree_le_of_dvd hP hne
    rw [natDegree_X_pow] at this
    omega
  have hEq : (R i) ^ 2 * f = C (f.coeff 0) * (S i) ^ 2 := sub_eq_zero.mp hPzero
  -- `r_i ≠ 0`, so its image under `φ` is nonzero.
  have hCc : C (f.coeff 0) ≠ 0 := by rw [Ne, C_eq_zero]; exact hf0
  have hRine : R i ≠ 0 := by
    intro hR0
    rw [hR0] at hEq
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hEq
    rcases mul_eq_zero.mp hEq.symm with h | h
    · exact hCc h
    · exact hi_spec.elim (· hR0) (· (sq_eq_zero_iff.mp h))
  -- Pass to `\overline{F}[X]` and extract the square, contradicting `hns`.
  have hinj : Function.Injective φ := φ.injective
  have hmap : (R i).map φ ^ 2 * f.map φ = C (φ (f.coeff 0)) * (S i).map φ ^ 2 := by
    have := congrArg (Polynomial.map φ) hEq
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C] using this
  have hφc : φ (f.coeff 0) ≠ 0 := by
    rw [Ne, ← map_zero φ]; exact fun h => hf0 (hinj h)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (φ (f.coeff 0)) (n := 2) (by norm_num)
  have hCd : C (φ (f.coeff 0)) = (C d) ^ 2 := by rw [← hd, C_pow]
  have hAB : (R i).map φ ^ 2 * f.map φ = (C d * (S i).map φ) ^ 2 := by
    rw [mul_pow, ← hCd]; exact hmap
  have hA : (R i).map φ ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hRine
  have hdvdA : (R i).map φ ∣ C d * (S i).map φ :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by norm_num)).mp ⟨f.map φ, hAB.symm⟩
  obtain ⟨w, hw⟩ := hdvdA
  have hfsq : f.map φ = w ^ 2 := by
    have hB : (C d * (S i).map φ) ^ 2 = (R i).map φ ^ 2 * w ^ 2 := by rw [hw]; ring
    rw [hB] at hAB
    exact mul_left_cancel₀ (pow_ne_zero 2 hA) hAB
  exact hns ⟨w, hfsq⟩

end Salt.Weil
