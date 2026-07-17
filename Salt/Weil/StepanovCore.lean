/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Stepanov
import Mathlib

/-!
# Weil track, the Stepanov core (W4.1c/d/e)

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder), following Harcos §5,
equations (17)–(23) and Theorem 7. This module carries the three load-bearing steps of the
Stepanov method for the point count of `y² = f(x)`:

* **W4.1d — the dimension count** (`stepanov_dimension_count`, `finrank_degreeLT`,
  `finrank_pi_degreeLT`): the constraints (22) form a homogeneous linear system whose number
  of variables `2·J·B` (with `B := ⌈(q-m)/2⌉` the degree bound (19)) exceeds the number of
  equations; therefore a nonzero coefficient vector `(r, s)` exists. The engine is
  `LinearMap.ker_ne_bot_of_finrank_lt`, and the dimension arithmetic is `finrank_degreeLT`.

* **W4.1c — the vanishing reduction** (`stepanovAux_hasseDeriv_eval`,
  `stepanovAux_dvd_of_reduced_eval_zero`): for `x ∈ F` (a point of the locus `N_a`) the
  `k`-th Hasse derivative of `h_a := stepanovAux f ℓ r s` evaluated at `x` collapses, via the
  characteristic-`p` identity `(X+Y)^{jq} ≡ X^{jq} (mod Y^q)` and `x^{jq} = x^j`, to the linear
  expression `∑_j (E^k(r_j f^ℓ + s_j f^{ℓ+e}))(x) · x^j =: (Q_k).eval x`. Hence if `Q_k` vanishes
  at `x` for every `k < ℓ`, then `x` is a root of `h_a` of multiplicity `≥ ℓ`
  (`X_sub_C_pow_dvd_iff_hasseDeriv`).

* **W4.1e — the count bound** (`stepanov_multiplicity_card_le`): combining the multiplicity
  `≥ ℓ` at each of the `|N_a|` distinct points with `h_a ≠ 0` and the degree bound gives
  `ℓ · |N_a| ≤ deg h_a`, the Stepanov inequality feeding Theorem 7.
-/

namespace Salt.Weil

open Polynomial Module
open scoped BigOperators

/-! ### W4.1d — the dimension count -/

variable {F : Type*} [Field F]

/-- **The abstract dimension count.** A linear map from a strictly larger space has a
genuinely nonzero vector in its kernel. This is the engine behind Harcos's
"more variables than equations ⇒ a nonzero solution" (Harcos p. 12). -/
theorem exists_nonzero_mem_ker_of_finrank_lt
    {V W : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (φ : V →ₗ[F] W) (h : finrank F W < finrank F V) :
    ∃ v : V, v ≠ 0 ∧ φ v = 0 := by
  obtain ⟨v, hv_mem, hv_ne⟩ :=
    (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt h)
  exact ⟨v, hv_ne, hv_mem⟩

/-- The space of polynomials of degree `< n` has dimension `n` (Harcos (19)). -/
theorem finrank_degreeLT (n : ℕ) : finrank F (degreeLT F n) = n := by
  rw [finrank_eq_card_basis (degreeLT.basis F n), Fintype.card_fin]

/-- Dimension of the coefficient space of `J` polynomials each of degree `< n`. -/
theorem finrank_pi_degreeLT (J n : ℕ) : finrank F (Fin J → degreeLT F n) = J * n := by
  rw [finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    finrank_degreeLT, smul_eq_mul]

/-- **The Stepanov dimension count** (Harcos p. 12). The coefficient space of the ansatz
is `(Fin J → degreeLT F B) × (Fin J → degreeLT F B)`: the `r_j`'s and `s_j`'s, each of degree
`< B` (the bound (19), `B = ⌈(q-m)/2⌉`). The constraints (22) are packaged as a linear map
`φ` into a product of `ℓ` degree-`< D` spaces. Whenever the count `ℓ·D < 2·J·B` holds, a
nonzero coefficient vector `(r, s)` lies in the kernel — a nonzero solution of (22). The
consumer (W4.1e) supplies `φ`, `B`, `D` and the count. -/
theorem stepanov_dimension_count {J ℓ B D : ℕ}
    (φ : ((Fin J → degreeLT F B) × (Fin J → degreeLT F B)) →ₗ[F] (Fin ℓ → degreeLT F D))
    (hcount : ℓ * D < 2 * (J * B)) :
    ∃ v : (Fin J → degreeLT F B) × (Fin J → degreeLT F B), v ≠ 0 ∧ φ v = 0 := by
  refine exists_nonzero_mem_ker_of_finrank_lt φ ?_
  rw [finrank_prod, finrank_pi_degreeLT, finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, finrank_degreeLT, smul_eq_mul]
  omega

/-- The degree-shift atom: multiplying a degree-`< d` polynomial by `X^e` lands it in
degree `< e + d` (the `WithBot`-degree bookkeeping for the constraint map). -/
theorem Xpow_mul_mem_degreeLT (e d : ℕ) (u : F[X]) (hu : u ∈ degreeLT F d) :
    X ^ e * u ∈ degreeLT F (e + d) := by
  rw [mem_degreeLT] at hu ⊢
  refine (degree_mul_le _ _).trans_lt ?_
  rw [degree_X_pow, Nat.cast_add]
  exact WithBot.add_lt_add_of_le_of_lt WithBot.coe_ne_bot le_rfl hu

/-! ### W4.1c — the vanishing reduction (Harcos (17)–(22)) -/

/-- Char-`p` monomial fact: `hasseDeriv b (X^q) = 0` for `0 < b < q`, because `p ∣ (p^n).choose b`
(with `q = p^n = #F`). This seeds the `(X+Y)^{jq} ≡ X^{jq} (mod Y^q)` collapse. -/
theorem hasseDeriv_X_pow_card_eq_zero [Fintype F] {b : ℕ} (hb0 : 0 < b)
    (hbq : b < Fintype.card F) : hasseDeriv b ((X : F[X]) ^ Fintype.card F) = 0 := by
  obtain ⟨p, hp_char, n, hp_prime, hpn⟩ := FiniteField.card' F
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : CharP F p := hp_char
  rw [X_pow_eq_monomial, hasseDeriv_monomial, mul_one]
  have hdvd : p ∣ (Fintype.card F).choose b := by
    rw [hpn]; exact hp_prime.dvd_choose_pow (by omega) (by omega)
  rw [show ((Fintype.card F).choose b : F) = 0 from (CharP.cast_eq_zero_iff F p _).mpr hdvd,
    monomial_zero_right]

/-- The `(X^q)^j` form of the char-`p` vanishing, by induction on `j` via the Leibniz rule. -/
theorem hasseDeriv_X_card_pow_eq_zero [Fintype F] {b : ℕ} (hb0 : 0 < b)
    (hbq : b < Fintype.card F) (j : ℕ) :
    hasseDeriv b (((X : F[X]) ^ Fintype.card F) ^ j) = 0 := by
  induction j with
  | zero => rw [pow_zero]; exact hasseDeriv_apply_one (k := b) hb0
  | succ j ih =>
    rw [pow_succ', hasseDeriv_mul]
    refine Finset.sum_eq_zero fun cd hcd => ?_
    rw [Finset.mem_antidiagonal] at hcd
    rcases Nat.eq_zero_or_pos cd.1 with hc | hc
    · have hd : cd.2 = b := by omega
      rw [hd, ih, mul_zero]
    · rw [hasseDeriv_X_pow_card_eq_zero hc (by omega), zero_mul]

/-- The `X^{jq}` form: `hasseDeriv b (X^{jq}) = 0` for `0 < b < q`. -/
theorem hasseDeriv_X_pow_mul_card_eq_zero [Fintype F] {b : ℕ} (hb0 : 0 < b)
    (hbq : b < Fintype.card F) (j : ℕ) :
    hasseDeriv b ((X : F[X]) ^ (j * Fintype.card F)) = 0 := by
  rw [pow_mul']
  exact hasseDeriv_X_card_pow_eq_zero hb0 hbq j

/-- The block identity `hasseDeriv k (g · X^{jq}) = hasseDeriv k g · X^{jq}` for `k < q`: the
window `X^{jq}` carries no cross terms since its lower Hasse derivatives vanish in char `p`. -/
theorem hasseDeriv_mul_X_pow_block [Fintype F] (g : F[X]) {k : ℕ} (j : ℕ)
    (hk : k < Fintype.card F) :
    hasseDeriv k (g * (X : F[X]) ^ (j * Fintype.card F))
      = hasseDeriv k g * (X : F[X]) ^ (j * Fintype.card F) := by
  have hsingle : ∑ ij ∈ Finset.antidiagonal k,
        hasseDeriv ij.1 g * hasseDeriv ij.2 ((X : F[X]) ^ (j * Fintype.card F))
      = hasseDeriv k g * hasseDeriv 0 ((X : F[X]) ^ (j * Fintype.card F)) := by
    refine Finset.sum_eq_single_of_mem (k, 0) (Finset.mem_antidiagonal.mpr (add_zero k)) ?_
    rintro ⟨c, d⟩ hcd hne
    rw [Finset.mem_antidiagonal] at hcd
    have hd2 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · exact absurd (by simp only [Prod.mk.injEq]; omega) hne
      · exact hd0
    dsimp only
    rw [hasseDeriv_X_pow_mul_card_eq_zero hd2 (by omega), mul_zero]
  rw [hasseDeriv_mul, hsingle, hasseDeriv_zero']

/-! ### Harcos Lemma 10 — the `f`-power divisibility -/

/-- **Lemma 10 core** (`g = 1`): `f^(n-k) ∣ hasseDeriv k (f^n)` for `k ≤ n`. Induction on `n` via
the Leibniz rule: the `i = 0` term carries the extra factor `f`, and every `i ≥ 1` term already
has a high enough `f`-power. This is the divisibility that — with the matching degree drop —
sharpens the reduced polynomials from the `(20)` form to the `(21)`/`(22)` degree bound. -/
theorem pow_dvd_hasseDeriv_pow (f : F[X]) (n : ℕ) :
    ∀ k, k ≤ n → f ^ (n - k) ∣ hasseDeriv k (f ^ n) := by
  induction n with
  | zero =>
    intro k hk
    interval_cases k
    simp
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_ge k (n + 1) with hkn | hkn
    · have hklen : k ≤ n := by omega
      rw [pow_succ', hasseDeriv_mul]
      refine Finset.dvd_sum fun ij hij => ?_
      rw [Finset.mem_antidiagonal] at hij
      rcases Nat.eq_zero_or_pos ij.1 with hi0 | hi0
      · have hi2 : ij.2 = k := by omega
        rw [hi0, hi2, hasseDeriv_zero']
        calc f ^ (n + 1 - k) = f * f ^ (n - k) := by rw [← pow_succ']; congr 1; omega
          _ ∣ f * hasseDeriv k (f ^ n) := mul_dvd_mul_left f (ih k hklen)
      · have hi2n : ij.2 ≤ n := by omega
        have hle : n + 1 - k ≤ n - ij.2 := by omega
        exact (pow_dvd_pow f hle).trans ((ih ij.2 hi2n).mul_left _)
    · have hz : n + 1 - k = 0 := by omega
      rw [hz, pow_zero]; exact one_dvd _

/-- **Lemma 10** (general `g`): `f^(ℓ-k) ∣ hasseDeriv k (g · f^ℓ)` for `k ≤ ℓ`. This factors each
`E^k(r_j f^ℓ)` as `r_j^{(k)} · f^{ℓ-k}`, the shape behind Harcos (20). -/
theorem pow_dvd_hasseDeriv_mul_pow (f g : F[X]) (ℓ k : ℕ) (hk : k ≤ ℓ) :
    f ^ (ℓ - k) ∣ hasseDeriv k (g * f ^ ℓ) := by
  rw [hasseDeriv_mul]
  refine Finset.dvd_sum fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  have hle : ℓ - k ≤ ℓ - ij.2 := by omega
  exact (pow_dvd_pow f hle).trans ((pow_dvd_hasseDeriv_pow f ℓ ij.2 (by omega)).mul_left _)

/-- **W4.1c — the reduced polynomial** `Q_k := ∑_j E^k(r_j f^ℓ + s_j f^{ℓ+e}) · X^j` (Harcos
(20)–(22)), `F`-linear in the coefficient data `(r, s)`. Evaluating the `k`-th Hasse derivative of
the ansatz at any point returns `(Q_k).eval x`. -/
noncomputable def reducedPoly [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    (k : ℕ) : F[X] :=
  ∑ j : Fin J,
    hasseDeriv k (r j * f ^ ℓ + s j * f ^ (ℓ + (Fintype.card F - 1) / 2)) * X ^ (j : ℕ)

theorem reducedPoly_eval [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    (x : F) (k : ℕ) :
    (reducedPoly f ℓ r s k).eval x
      = ∑ j : Fin J,
          (hasseDeriv k (r j * f ^ ℓ + s j * f ^ (ℓ + (Fintype.card F - 1) / 2))).eval x
            * x ^ (j : ℕ) := by
  unfold reducedPoly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_pow, eval_X]

/-- **W4.1c — the vanishing reduction** (Harcos (20)–(22)). The `k`-th Hasse derivative of the
ansatz, evaluated at any `x ∈ F`, equals `(Q_k).eval x`: the char-`p` identity
`hasseDeriv b (X^{jq}) = 0` collapses the Leibniz sum to the `X^{jq}` window, and `x^{jq} = x^j`
on the finite field folds the windows onto the reduced polynomial. -/
theorem stepanovAux_hasseDeriv_eval [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ)
    (r s : Fin J → F[X]) (x : F) {k : ℕ} (hk : k < Fintype.card F) :
    (hasseDeriv k (stepanovAux f ℓ r s)).eval x = (reducedPoly f ℓ r s k).eval x := by
  rw [reducedPoly_eval]
  set q := Fintype.card F with hq
  set e := (q - 1) / 2 with he
  have hrw : stepanovAux f ℓ r s
      = ∑ j : Fin J, (r j * f ^ ℓ + s j * f ^ (ℓ + e)) * X ^ ((j : ℕ) * q) := by
    unfold stepanovAux
    rw [← hq, ← he, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring
  rw [hrw, map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hasseDeriv_mul_X_pow_block _ _ hk, eval_mul, eval_pow, eval_X]
  congr 1
  rw [pow_mul]
  exact FiniteField.pow_card _

/-- **W4.1c — the multiplicity certificate** (Harcos (17)). If the reduced polynomial `Q_k`
vanishes *at* `x` for every `k < ℓ` (with `ℓ ≤ q`), then `x` is a root of the ansatz of
multiplicity `≥ ℓ`. At a point of the locus `N_a`, where `f(x)^{(q-1)/2} = a` folds the `(22)`
linear conditions into `Q_k(x) = 0`, this delivers the high-order zeros; note `Q_k(x) = 0` is the
honest per-point condition — the *global* identity `Q_k = 0` collapses to the zero ansatz. -/
theorem stepanovAux_dvd_of_reduced_eval_zero [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ)
    (r s : Fin J → F[X]) (x : F) (hℓq : ℓ ≤ Fintype.card F)
    (hred : ∀ k, k < ℓ → (reducedPoly f ℓ r s k).eval x = 0) :
    (X - C x) ^ ℓ ∣ stepanovAux f ℓ r s := by
  rw [X_sub_C_pow_dvd_iff_hasseDeriv]
  intro k hk
  rw [stepanovAux_hasseDeriv_eval f ℓ r s x (lt_of_lt_of_le hk hℓq)]
  exact hred k hk

/-! ### W4.1e — the count bound -/

/-- **W4.1e — the Stepanov count bound.** If `h ≠ 0` and each element of a finite set `T` of
distinct field elements is a root of `h` of multiplicity `≥ ℓ`, then `ℓ · |T| ≤ deg h`. With
`h = h_a` and `T = N_a` this is Harcos's `ℓ(N₀ + N_a) ≤ deg h_a` feeding Theorem 7. -/
theorem stepanov_multiplicity_card_le {h : F[X]} (hh : h ≠ 0) (ℓ : ℕ) (T : Finset F)
    (hT : ∀ x ∈ T, (X - C x) ^ ℓ ∣ h) : ℓ * T.card ≤ h.natDegree := by
  have hdvd : (∏ x ∈ T, (X - C x) ^ ℓ) ∣ h := by
    refine Finset.prod_dvd_of_coprime ?_ hT
    intro x _ y _ hxy
    exact (pairwise_coprime_X_sub_C Function.injective_id hxy).pow
  have hdeg := natDegree_le_of_dvd hdvd hh
  rw [natDegree_prod _ _ (fun x _ => pow_ne_zero ℓ (monic_X_sub_C x).ne_zero)] at hdeg
  have hterm : ∀ x ∈ T, ((X - C x) ^ ℓ).natDegree = ℓ := by
    intro x _; rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul] at hdeg
  rw [mul_comm ℓ T.card]; exact hdeg

end Salt.Weil
