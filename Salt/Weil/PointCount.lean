/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.StepanovCore
import Mathlib

/-!
# Weil track, the point count (W5): the tight-degree bridge and Theorem 7

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder), following Harcos §5,
equations (12)–(23), Theorem 7 and Remark 4. This module carries the last analytic step of
the Stepanov face: the sharp degree control on the reduced polynomials (Harcos (21)), the
`a`-form of the constraint system (22) on the locus `N_a`, and the Weil–Stepanov point-count
bound (Theorem 7) for `y² = f(x)`.

* **the tight-degree bridge** (`exists_quotient_hasseDeriv_mul_pow`,
  `reducedPoly_dvd`): the degree companion to `pow_dvd_hasseDeriv_mul_pow` (Harcos Lemma 10,
  eq. (16)/(21)). Not only does `f^{ℓ-k}` divide `hasseDeriv k (g·f^ℓ)`; the quotient `g^{(k)}`
  has `natDegree ≤ deg g + k·(m-1)` with `m := deg f`. Consequently `f^{ℓ-k} ∣ reducedPoly` and
  `reducedPoly` has a controlled degree — the degree input (21) to the equation count on p. 12.
-/

namespace Salt.Weil

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F]

/-! ### The tight-degree bridge (Harcos Lemma 10, eq. (16)/(21)) -/

/-- **The tight-degree bridge** (Harcos Lemma 10, the degree half, eq. (16)/(21)). Companion to
`pow_dvd_hasseDeriv_mul_pow`: not only does `f^{ℓ-k}` divide `hasseDeriv k (g·f^ℓ)`, but the
quotient `g^{(k)}` has controlled degree. With `f ≠ 0`, `m := deg f ≥ 1` and `k ≤ ℓ`,
`hasseDeriv k (g·f^ℓ) = f^{ℓ-k}·u` for some `u` with `deg u ≤ deg g + k·(m-1)`.

Proof: the divisibility gives `u`; the degree drop `deg (E^k h) ≤ deg h − k`
(`natDegree_hasseDeriv_le`) together with `deg h = (ℓ-k)·m + deg u` (domain factorisation)
pins `deg u` after the `ℕ`-arithmetic identities `(ℓ-k)m + km = ℓm` and `k(m-1) + k = km`. -/
theorem exists_quotient_hasseDeriv_mul_pow (f g : F[X]) (hf : f ≠ 0) (hm : 1 ≤ f.natDegree)
    (ℓ k : ℕ) (hk : k ≤ ℓ) :
    ∃ u : F[X], hasseDeriv k (g * f ^ ℓ) = f ^ (ℓ - k) * u ∧
      u.natDegree ≤ g.natDegree + k * (f.natDegree - 1) := by
  obtain ⟨u, hu⟩ := pow_dvd_hasseDeriv_mul_pow f g ℓ k hk
  refine ⟨u, hu, ?_⟩
  set m := f.natDegree with hm_def
  set h := hasseDeriv k (g * f ^ ℓ) with hh_def
  -- Numerator degree, keeping the `- k` for tightness.
  have hnd : h.natDegree ≤ (g * f ^ ℓ).natDegree - k := natDegree_hasseDeriv_le _ _
  have hmul : (g * f ^ ℓ).natDegree ≤ g.natDegree + ℓ * m := by
    refine natDegree_mul_le.trans ?_
    gcongr
    exact natDegree_pow_le
  rcases eq_or_ne h 0 with h0 | h0
  · -- `h = 0` forces `u = 0` since `f^{ℓ-k} ≠ 0`.
    have hzero : f ^ (ℓ - k) * u = 0 := by rw [← hu]; exact h0
    have hu0 : u = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hf)
    rw [hu0]; simp
  · -- `h ≠ 0`: factor the degree and finish with `ℕ`-arithmetic.
    have hpow_ne : f ^ (ℓ - k) ≠ 0 := pow_ne_zero _ hf
    have hne : f ^ (ℓ - k) * u ≠ 0 := by rw [← hu]; exact h0
    have hu_ne : u ≠ 0 := right_ne_zero_of_mul hne
    have hfact : h.natDegree = (ℓ - k) * m + u.natDegree := by
      rw [hu, natDegree_mul hpow_ne hu_ne, natDegree_pow]
    have p1 : (ℓ - k) * m + k * m = ℓ * m := by rw [← Nat.add_mul, Nat.sub_add_cancel hk]
    have p2 : k * (m - 1) + k = k * m := by rw [← Nat.mul_succ]; congr 1; omega
    omega

/-- **`f^{ℓ-k}` divides the reduced polynomial** (Harcos (20)). Every summand of `reducedPoly`
is `hasseDeriv k` of `r_j f^ℓ + s_j f^{ℓ+e}`, and both `f^ℓ` and `f^{ℓ+e}` carry a factor `f^ℓ`,
so `f^{ℓ-k}` divides each `hasseDeriv k` term (via `pow_dvd_hasseDeriv_mul_pow`). -/
theorem reducedPoly_dvd [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    {k : ℕ} (hk : k ≤ ℓ) :
    f ^ (ℓ - k) ∣ reducedPoly f ℓ r s k := by
  unfold reducedPoly
  refine Finset.dvd_sum fun j _ => ?_
  refine Dvd.dvd.mul_right ?_ _
  rw [map_add]
  refine dvd_add (pow_dvd_hasseDeriv_mul_pow f (r j) ℓ k hk) ?_
  -- `s_j f^{ℓ+e} = (s_j f^e) f^ℓ`, so the same divisibility applies with `g := s_j f^e`.
  have hrw : s j * f ^ (ℓ + (Fintype.card F - 1) / 2)
      = (s j * f ^ ((Fintype.card F - 1) / 2)) * f ^ ℓ := by rw [pow_add]; ring
  rw [hrw]
  exact pow_dvd_hasseDeriv_mul_pow f (s j * f ^ ((Fintype.card F - 1) / 2)) ℓ k hk

/-! ### The `a`-form of the constraint system (Harcos (22)) and the count bound (13) -/

/-- **`N_0` is automatic** (Harcos (17), the `f(x) = 0` branch). At a root of `f` the reduced
polynomial `Q_k` vanishes for every `k < ℓ`, with no constraint on `(r, s)`: `Q_k = f^{ℓ-k}·P_k`
by `reducedPoly_dvd` and `f(x)^{ℓ-k} = 0` since `ℓ - k ≥ 1`. -/
theorem reducedPoly_eval_eq_zero_of_eval_zero [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ)
    (r s : Fin J → F[X]) {x : F} (hx : f.eval x = 0) {k : ℕ} (hk : k < ℓ) :
    (reducedPoly f ℓ r s k).eval x = 0 := by
  obtain ⟨P, hP⟩ := reducedPoly_dvd f ℓ r s (le_of_lt hk)
  rw [hP, eval_mul, eval_pow, hx, zero_pow (by omega : ℓ - k ≠ 0), zero_mul]

/-- **The `a`-form** (Harcos (20)→(22)). On the locus `N_a = {x : f(x)^{(q-1)/2} = a}`, the reduced
polynomial `Q_k` evaluated at `x` factors as `f(x)^{ℓ-k}` times the value at `x` of the
*`a`-linear combination* `∑_j (r_j^{(k)} + a·s_j^{(k)}) X^j` — the Harcos (22) polynomial. The
quotients `r_j^{(k)}, s_j^{(k)}` come from the tight-degree bridge, so they satisfy the (21)
degree bound `deg ≤ deg r_j + k(m-1)`. Substituting `f(x)^{(q-1)/2} = a` collapses the extra
`f^{(q-1)/2}` on the `s`-block to the constant `a`. -/
theorem reducedPoly_eval_on_Na [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    (hf : f ≠ 0) (hm : 1 ≤ f.natDegree) (a : F) {k : ℕ} (hk : k ≤ ℓ) (x : F)
    (hx : (f.eval x) ^ ((Fintype.card F - 1) / 2) = a) :
    ∃ rk sk : Fin J → F[X],
      (∀ j, (rk j).natDegree ≤ (r j).natDegree + k * (f.natDegree - 1)) ∧
      (∀ j, (sk j).natDegree ≤ (s j).natDegree + k * (f.natDegree - 1)) ∧
      (reducedPoly f ℓ r s k).eval x
        = (f.eval x) ^ (ℓ - k) * (∑ j : Fin J, (rk j + C a * sk j) * X ^ (j : ℕ)).eval x := by
  classical
  set e := (Fintype.card F - 1) / 2 with he
  choose rk hrk hrk_deg using fun j =>
    exists_quotient_hasseDeriv_mul_pow f (r j) hf hm ℓ k hk
  choose sk hsk hsk_deg using fun j =>
    exists_quotient_hasseDeriv_mul_pow f (s j) hf hm (ℓ + e) k (by omega)
  refine ⟨rk, sk, hrk_deg, hsk_deg, ?_⟩
  rw [reducedPoly_eval]
  have hRHS : (∑ j : Fin J, (rk j + C a * sk j) * X ^ (j : ℕ)).eval x
      = ∑ j : Fin J, ((rk j).eval x + a * (sk j).eval x) * x ^ (j : ℕ) := by
    rw [eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_mul, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  rw [hRHS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpow : (f.eval x) ^ ((ℓ + e) - k) = (f.eval x) ^ (ℓ - k) * a := by
    rw [← hx, ← pow_add]; congr 1; omega
  rw [map_add, eval_add, hrk j, hsk j]
  simp only [eval_mul, eval_pow]
  rw [hpow]; ring

/-- **The Stepanov count bound** (Harcos (13), numerator). If the auxiliary polynomial `h_a` is
nonzero and, at every point of a finite locus `T` where `f(x) ≠ 0`, the reduced polynomials
`Q_k` (`k < ℓ`) vanish — i.e. `(r, s)` solves (22) on `T` — then `ℓ·|T| ≤ deg h_a`. The `f(x)=0`
points of `T` are handled automatically (`reducedPoly_eval_eq_zero_of_eval_zero`); the assembly
is `stepanovAux_dvd_of_reduced_eval_zero` (multiplicity `≥ ℓ` at each point) fed into
`stepanov_multiplicity_card_le`. Combined with `stepanovAux_natDegree_le` this yields (13). -/
theorem stepanov_locus_card_le [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    (hℓq : ℓ ≤ Fintype.card F) (hne : stepanovAux f ℓ r s ≠ 0) (T : Finset F)
    (hNa : ∀ k, k < ℓ → ∀ x ∈ T, f.eval x ≠ 0 → (reducedPoly f ℓ r s k).eval x = 0) :
    ℓ * T.card ≤ (stepanovAux f ℓ r s).natDegree := by
  refine stepanov_multiplicity_card_le hne ℓ T (fun x hx => ?_)
  refine stepanovAux_dvd_of_reduced_eval_zero f ℓ r s x hℓq (fun k hk => ?_)
  rcases eq_or_ne (f.eval x) 0 with h0 | h0
  · exact reducedPoly_eval_eq_zero_of_eval_zero f ℓ r s h0 hk
  · exact hNa k hk x hx h0

/-! ### The dimension-count arithmetic (Harcos p. 12)

The constraints (22) form a homogeneous linear system in the coefficients of `r_j, s_j`. By (19)
the number of variables is `2·J·⌈(q-m)/2⌉ ≥ J(q-m)`; by (21) the number of equations for fixed
`k` is `≤ (q-m)/2 + k(m-1) + J`, so summing over `0 ≤ k < ℓ` the total is
`< ℓ((q-m)/2 + J) + (ℓ²/2)(m-1)`. A nonzero solution exists once variables exceed equations,
i.e. `J(q-m) ≥ ℓ((q-m)/2 + J) + (ℓ²/2)(m-1)`, equivalently `(J - ℓ/2)(q-m-ℓ) ≥ ℓ²m/2`. Imposing
`ℓ ≤ q/3` and `m < q/6` (the Theorem 7 hypotheses) gives `q-m-ℓ ≥ q/2`, so `J := ⌈ℓ/2 + ℓ²m/q⌉`
suffices; with `ℓ := ⌈√q⌉` the final bound `ℓ(N₀+N_a) ≤ deg h_a` yields `N₀+N_a < q/2 + O_m(√q)`,
which is Harcos (13).

The landed engine `stepanov_dimension_count` uses a *uniform* degree bound `D` on the `ℓ`
constraint blocks, i.e. `D := (q-m)/2 + (ℓ-1)(m-1) + J` (the maximal `D_k`), so it needs
`ℓ·D < 2·J·B`. This is looser than Harcos's exact `∑_k D_k` by a factor ≈ 2 on the `(m-1)`-term,
absorbed by taking `J` slightly above the optimum. A concrete Harcos-shaped instance: -/

/-- Sanity check that the (uniform-`D`) dimension count fires for Harcos-shaped parameters
`q = 100`, `m = 10`, `ℓ = 10 = ⌈√q⌉`, `B = (q-m)/2 = 45`, `J = 16` (the optimum `15` bumped by
one to absorb the uniform bound), `D = (q-m)/2 + (ℓ-1)(m-1) + J = 45 + 81 + 16 = 142`: the count
`ℓ·D = 1420 < 1440 = 2·J·B` holds, so a nonzero coefficient vector exists. -/
example :
    ∃ v : (Fin 16 → degreeLT F 45) × (Fin 16 → degreeLT F 45),
      v ≠ 0 ∧ (0 : ((Fin 16 → degreeLT F 45) × (Fin 16 → degreeLT F 45)) →ₗ[F]
        (Fin 10 → degreeLT F 142)) v = 0 :=
  stepanov_dimension_count 0 (by norm_num)

/-! ### Theorem 7 — the Weil–Stepanov point count for `y² = f(x)` -/

/-- **The point count** `N := #{(x, y) : y² = f(x)}` for the hyperelliptic curve of Theorem 7. -/
noncomputable def pointCount [Fintype F] (f : F[X]) : ℕ :=
  Nat.card {p : F × F // p.2 ^ 2 = f.eval p.1}

/-- **Harcos (12) — the elementary point-count identity.** Fibering over `x` and counting the
solutions of `y² = f(x)` with the quadratic character (`quadraticChar_card_sqrts`: a point `x`
contributes `1 + χ(f(x))`), the point count is `N = q + ∑_x χ(f(x))`. This is `N − q = N₁ − N₋₁`,
the honest elementary route: the character sum is exactly the quantity Stepanov's (13) bounds. -/
theorem pointCount_sub_card [Fintype F] [DecidableEq F] (f : F[X]) (hF : ringChar F ≠ 2) :
    (pointCount f : ℤ) = Fintype.card F + ∑ x : F, quadraticChar F (f.eval x) := by
  have hfib : ∀ x : F, (Nat.card {y : F // y ^ 2 = f.eval x} : ℤ)
      = quadraticChar F (f.eval x) + 1 := by
    intro x
    have hcard : Nat.card {y : F // y ^ 2 = f.eval x}
        = {y : F | y ^ 2 = f.eval x}.toFinset.card := by
      rw [← Set.ncard_eq_toFinset_card']
      exact Nat.card_coe_set_eq _
    rw [hcard]
    exact_mod_cast quadraticChar_card_sqrts hF (f.eval x)
  unfold pointCount
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a b : F => b ^ 2 = f.eval a)),
    Nat.card_sigma]
  push_cast
  simp_rw [hfib]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

/-- **The Weil–Stepanov combine** (Harcos, end of §5). Given the two Stepanov locus bounds
`N₀ + N₁ ≤ B` and `N₀ + N₋₁ ≤ B` (from `stepanov_locus_card_le` for `a = ±1`), together with
`N₀ + N₁ + N₋₁ = q`, the deviation `N − q = N₁ − N₋₁` of the point count satisfies
`|N₁ − N₋₁| ≤ 2B − q`. With `B < q/2 + O_m(√q)` this is `|N − q| < O_m(√q)` — Theorem 7. Pure
`ℤ`-arithmetic, isolating the counting glue from the (Fable-blocked) `(22)`-solution existence. -/
theorem pointCount_abs_sub_le {N₀ N₁ Nm1 q B : ℤ} (hq : N₀ + N₁ + Nm1 = q)
    (h0 : 0 ≤ N₀) (hb1 : N₀ + N₁ ≤ B) (hbm1 : N₀ + Nm1 ≤ B) :
    |N₁ - Nm1| ≤ 2 * B - q := by
  rw [abs_le]; constructor <;> omega

end Salt.Weil
