/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.GaussSum
import Salt.BV.Completion
import Salt.Weil.Kloosterman
import Salt.Weil.Descent
import Mathlib

/-!
# HB-F-COMP — the incomplete Kloosterman-sum bound (the completion port)

Link 3 of the registered `HB-ENGINE` campaign (`docs/exploration/s3-hb3-design.md`,
"HB-ENGINE — REGISTERED"), taken as an independently-valuable down payment: the
classical incomplete-Kloosterman estimate obtained by re-pointing the corpus's
finite-Fourier interval-cutoff machinery (`Salt/BV/Completion.lean`, built for
Dirichlet sums) at the complete Kloosterman sums (`Salt/Weil/Kloosterman.lean`,
`Salt/Weil/Descent.lean`).

**The completion method.** For a prime `p` and an interval `[1, Z]` (`Z ≤ p`) on
the unit representatives, the incomplete Kloosterman sum
`∑_{t unit, val t ≤ Z} ψ(a·t + b·t⁻¹)` is expanded through the sharp-indicator DFT
`1_{n ≤ Z} = ∑_{h<p} ĉ_h(Z)·e(hn/p)` (`Salt.BV.fourierCutoff_indicator`). The
frequency twist `e(h·val t/p)` **is** the additive character `ψ(h·t)`
(`e_bridge`, via `Salt.LS.stdAddChar_eq_e` + `e`-periodicity), so each frequency
collapses the twisted sum to a *complete* Kloosterman sum at the shifted first
argument:
`incomplete = ∑_{h<p} ĉ_h(Z)·S(a + h, b; p)`.
Bounding termwise by the uniform Weil sup `‖S(a+h, b; p)‖ ≤ 2√p`
(`norm_kloosterman_shift_le`) and the `Z`-uniform `L¹` mass
`∑_{h<p} ‖ĉ_h(Z)‖ ≤ 2 + log p` (`Salt.BV.sum_norm_fourierCutoff_le`) gives
`‖incomplete‖ ≤ 2√p·(2 + log p)` (`norm_incomplete_kloosterman_le`).

**The degenerate frequency (honest accounting).** Exactly one `h ∈ [0, p)` makes
`a + h = 0`, where the Weil bound is unavailable. Rather than the crude `‖S‖ ≤ p−1`
(which, weighted by the cutoff coefficient, would inject an `O(p)` term and destroy
the estimate), we compute the Ramanujan value `S(0, b; p) = −1` exactly
(`kloosterman_zero`, additive orthogonality over the units), giving the *uniform*
sup `‖S(a+h, b; p)‖ ≤ 2√p` for **every** `h` with no exceptional term — a cleaner
constant than the design memo anticipated.

Verbatim reuse from `BV/Completion`: `fourierCutoff`, `fourierCutoff_indicator`,
`sum_norm_fourierCutoff_le` (unchanged — the `e`-based cutoff is character-agnostic,
not Dirichlet-baked; only its `bilinear_factorization` corollary bakes in `χ`). From
the Weil suite: `norm_kloosterman_le_two_sqrt'`, `norm_kloosterman_le_sub_one`, the
`kloosterman` definition. New glue: the `e ↔ ψ` bridge, the degenerate value, the
shifted uniform sup, and the completion assembly.
-/

namespace Salt.Weil

open scoped BigOperators
open Salt.LS Salt.BV

/-! ### The `e ↔ ψ` bridge -/

/-- `e` vanishes on the natural casts: `e (j) = 1` (1-periodicity iterated). -/
private lemma e_natCast (j : ℕ) : e (j : ℝ) = 1 := by
  induction j with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, e_add_one]; exact ih

/-- `e (j/p)` depends only on `j mod p` (the `e`-periodicity used to reduce the
frequency twist modulo the character period). -/
private lemma e_div_p_mod {p : ℕ} [NeZero p] (j : ℕ) :
    e ((j : ℝ) / p) = e (((j % p : ℕ) : ℝ) / p) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hj : (j : ℝ) / p = ((j / p : ℕ) : ℝ) + ((j % p : ℕ) : ℝ) / p := by
    have hdm : (j : ℝ) = (p : ℝ) * ((j / p : ℕ) : ℝ) + ((j % p : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod j p).symm
    rw [hdm]; field_simp
  rw [hj, e_add, e_natCast, one_mul]

/-- **The frequency-twist bridge.** The cutoff frequency `e(h·val t/p)` at a unit `t`
is the standard additive character `ψ` at `h·t`: `ψ((h : ZMod p)·t) = e(h·(val t)/p)`.
`stdAddChar_eq_e` turns `ψ` into `e` at the Farey point, and `e`-periodicity reduces
`((h : ZMod p)·t).val ≡ h·(val t) (mod p)`. -/
private lemma e_bridge {p : ℕ} [NeZero p] (h : ℕ) (t : (ZMod p)ˣ) :
    (ZMod.stdAddChar ((h : ZMod p) * (t : ZMod p)) : ℂ)
      = e ((h : ℝ) * ((t : ZMod p).val : ℝ) / (p : ℝ)) := by
  rw [Salt.LS.stdAddChar_eq_e]
  set v : ℕ := (t : ZMod p).val with hv
  set M : ℕ := ((h : ZMod p) * (t : ZMod p)).val with hM
  have hMmod : M % p = (h * v) % p := by
    have h1 : M = (h % p) * v % p := by rw [hM, ZMod.val_mul, ZMod.val_natCast]
    rw [h1, Nat.mod_mod]
    exact (Nat.mod_modEq h p).mul_right v
  rw [show (h : ℝ) * (v : ℝ) = ((h * v : ℕ) : ℝ) by push_cast; ring]
  rw [e_div_p_mod M, e_div_p_mod (h * v), hMmod]

/-- **The completion term identity.** The cutoff frequency times a Kloosterman
summand at `(a, b)` is the summand at the shifted argument `(a + h, b)`:
`e(h·val t/p)·ψ(a·t + b·t⁻¹) = ψ((a + h)·t + b·t⁻¹)`. -/
private lemma key_term {p : ℕ} [Fact p.Prime] (a b : ZMod p) (h : ℕ) (t : (ZMod p)ˣ) :
    e ((h : ℝ) * ((t : ZMod p).val : ℝ) / (p : ℝ))
        * ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p))
      = ZMod.stdAddChar ((a + (h : ZMod p)) * (t : ZMod p)
          + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)) := by
  rw [show (a + (h : ZMod p)) * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)
        = (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p))
          + (h : ZMod p) * (t : ZMod p) by ring,
      AddChar.map_add_eq_mul ZMod.stdAddChar
        (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)) ((h : ZMod p) * (t : ZMod p)),
      e_bridge, mul_comm]

/-! ### The degenerate frequency `S(0, b; p) = −1` -/

/-- A field sum over `ZMod p` vanishing at `0` reindexes to a sum over the units
(re-derivation of `LFunction.sum_units_eq_sum_field`, which is `private` there). -/
private theorem sum_units_eq_field {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommMonoid M]
    (F : ZMod p → M) (h0 : F 0 = 0) :
    ∑ x : ZMod p, F x = ∑ t : (ZMod p)ˣ, F (t : ZMod p) := by
  rw [← Finset.sum_erase Finset.univ h0]
  refine (Finset.sum_bij (fun (t : (ZMod p)ˣ) _ => (t : ZMod p)) ?_ ?_ ?_ ?_).symm
  · intro t _; exact Finset.mem_erase.mpr ⟨Units.ne_zero t, Finset.mem_univ _⟩
  · intro t₁ _ t₂ _ h; exact Units.ext h
  · intro x hx; exact ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
  · intro t _; rfl

/-- **The Ramanujan value.** `S(0, b; p) = −1` for `b ≠ 0`: reindex `t ↦ t⁻¹` to
`∑_{t unit} ψ(b·t)`, then additive orthogonality `∑_{v : ZMod p} ψ(b·v) = 0`
(`AddChar.sum_mulShift` at the primitive `ψ`) leaves exactly the missing `v = 0`
term `−ψ(0) = −1`. This is what lets the degenerate frequency ride the uniform
`2√p` sup instead of the crude `p − 1`. -/
private theorem kloosterman_zero {p : ℕ} [Fact p.Prime] (b : ZMod p) (hb : b ≠ 0) :
    kloosterman (0 : ZMod p) b = -1 := by
  have hk : kloosterman (0 : ZMod p) b
      = ∑ s : (ZMod p)ˣ, (ZMod.stdAddChar (b * (s : ZMod p)) : ℂ) := by
    unfold kloosterman
    rw [← Equiv.sum_comp (Equiv.inv (ZMod p)ˣ)
        (fun s : (ZMod p)ˣ => ZMod.stdAddChar (b * (s : ZMod p)))]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [Equiv.inv_apply, zero_mul, zero_add]
  rw [hk]
  have hsum0 : ∑ v : ZMod p, (ZMod.stdAddChar (b * v) : ℂ) = 0 := by
    have hcm : ∀ v : ZMod p, b * v = v * b := fun v => mul_comm b v
    simp_rw [hcm]
    rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar p)]
    simp [hb]
  set F : ZMod p → ℂ :=
    fun w => (ZMod.stdAddChar (b * w) : ℂ) - (if w = 0 then 1 else 0) with hF
  have hF0 : F 0 = 0 := by simp [hF, AddChar.map_zero_eq_one]
  have hbridge := sum_units_eq_field F hF0
  have hite : ∑ v : ZMod p, (if v = (0 : ZMod p) then (1 : ℂ) else 0) = 1 := by
    rw [Finset.sum_ite_eq' Finset.univ (0 : ZMod p) (fun _ => (1 : ℂ))]; simp
  have hLHS : ∑ v : ZMod p, F v = -1 := by
    simp only [hF, Finset.sum_sub_distrib, hsum0, hite]; ring
  have hRHS : ∑ s : (ZMod p)ˣ, F (s : ZMod p)
      = ∑ s : (ZMod p)ˣ, (ZMod.stdAddChar (b * (s : ZMod p)) : ℂ) := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [hF, if_neg (Units.ne_zero s), sub_zero]
  rw [← hRHS, ← hbridge]; exact hLHS

/-- **The uniform shifted sup.** For `b ≠ 0` and **every** integer shift `h`,
`‖S(a + h, b; p)‖ ≤ 2√p`: the Weil bound `norm_kloosterman_le_two_sqrt'` on the
generic frequencies, and the Ramanujan value `‖S(0, b; p)‖ = 1 ≤ 2√p` on the single
degenerate one. -/
private theorem norm_kloosterman_shift_le {p : ℕ} [Fact p.Prime] (a b : ZMod p) (hb : b ≠ 0)
    (h : ℕ) : ‖kloosterman (a + (h : ZMod p)) b‖ ≤ 2 * Real.sqrt p := by
  by_cases hah : a + (h : ZMod p) = 0
  · rw [hah, kloosterman_zero b hb, norm_neg, norm_one]
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    have hs : (1 : ℝ) ≤ Real.sqrt p := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hp1
    linarith
  · exact norm_kloosterman_le_two_sqrt' (a + (h : ZMod p)) b hah hb

/-! ### The incomplete Kloosterman bound -/

/-- **HB-F-COMP — the incomplete Kloosterman bound.** For any prime `p`, `b ≠ 0`,
and an interval `[1, Z]` (`Z ≤ p`) on the unit representatives,
`‖∑_{t unit, val t ≤ Z} ψ(a·t + b·t⁻¹)‖ ≤ 2√p·(2 + log p)`.

The completion identity `fourierCutoff_indicator` expands the sharp cutoff into the
`p` frequency twists; `e_bridge`/`key_term` collapse each twist to a complete
Kloosterman sum `S(a + h, b; p)`; the uniform Weil sup (`norm_kloosterman_shift_le`)
and the `Z`-uniform `L¹` mass (`sum_norm_fourierCutoff_le`) close the estimate.
No `a ≠ 0` or odd-`p` hypothesis is needed — the degenerate frequency is absorbed by
the exact Ramanujan value, not a crude bound. -/
theorem norm_incomplete_kloosterman_le {p : ℕ} [Fact p.Prime]
    (a b : ZMod p) (hb : b ≠ 0) (Z : ℕ) (hZ : Z ≤ p) :
    ‖∑ t ∈ Finset.univ.filter (fun t : (ZMod p)ˣ => (t : ZMod p).val ≤ Z),
        (ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)) : ℂ)‖
      ≤ 2 * Real.sqrt p * (2 + Real.log p) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hexpand :
      (∑ t ∈ Finset.univ.filter (fun t : (ZMod p)ˣ => (t : ZMod p).val ≤ Z),
          (ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)) : ℂ))
        = ∑ h ∈ Finset.range p, fourierCutoff p Z h * kloosterman (a + (h : ZMod p)) b := by
    rw [Finset.sum_filter]
    have hif : ∀ t : (ZMod p)ˣ,
        (if (t : ZMod p).val ≤ Z then
            (ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)) : ℂ)
          else 0)
          = (if (t : ZMod p).val ≤ Z then (1 : ℂ) else 0)
              * ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)) := by
      intro t
      by_cases hc : (t : ZMod p).val ≤ Z
      · rw [if_pos hc, if_pos hc, one_mul]
      · rw [if_neg hc, if_neg hc, zero_mul]
    rw [Finset.sum_congr rfl (fun t _ => hif t)]
    have hind : ∀ t : (ZMod p)ˣ,
        (if (t : ZMod p).val ≤ Z then (1 : ℂ) else 0)
          = ∑ h ∈ Finset.range p,
              fourierCutoff p Z h * e ((h : ℝ) * ((t : ZMod p).val : ℝ) / (p : ℝ)) := by
      intro t
      exact fourierCutoff_indicator p Z ((t : ZMod p).val) hp0
        ((ZMod.val_pos).mpr (Units.ne_zero t)) (ZMod.val_lt (t : ZMod p)).le hZ
    rw [Finset.sum_congr rfl (fun t _ => by rw [hind t, Finset.sum_mul])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    unfold kloosterman
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [mul_assoc, key_term a b h t]
  rw [hexpand]
  calc ‖∑ h ∈ Finset.range p, fourierCutoff p Z h * kloosterman (a + (h : ZMod p)) b‖
      ≤ ∑ h ∈ Finset.range p, ‖fourierCutoff p Z h * kloosterman (a + (h : ZMod p)) b‖ :=
        norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.range p, ‖fourierCutoff p Z h‖ * (2 * Real.sqrt p) := by
        refine Finset.sum_le_sum (fun h _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_kloosterman_shift_le a b hb h) (norm_nonneg _)
    _ = (∑ h ∈ Finset.range p, ‖fourierCutoff p Z h‖) * (2 * Real.sqrt p) := by
        rw [Finset.sum_mul]
    _ ≤ (2 + Real.log p) * (2 * Real.sqrt p) :=
        mul_le_mul_of_nonneg_right (sum_norm_fourierCutoff_le p Z hp0 hZ) (by positivity)
    _ = 2 * Real.sqrt p * (2 + Real.log p) := by ring

/-- Smoke: the bound applies at the full interval `Z = p` (all units), i.e. to the
complete Kloosterman sum, with no residual hypotheses beyond `b ≠ 0`. -/
example {p : ℕ} [Fact p.Prime] (a b : ZMod p) (hb : b ≠ 0) :
    ‖∑ t ∈ Finset.univ.filter (fun t : (ZMod p)ˣ => (t : ZMod p).val ≤ p),
        (ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)) : ℂ)‖
      ≤ 2 * Real.sqrt p * (2 + Real.log p) :=
  norm_incomplete_kloosterman_le a b hb p le_rfl

end Salt.Weil
