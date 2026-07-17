/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.LocalFactor
import Salt.Weil.ArtinSchreier
import Salt.Weil.Orbits
import Mathlib

/-!
# Weil track, node W2 — the moment ↔ eigenvalue layer (Harcos §3, Thms 5–6, Cor 3)

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder). This is the layer the Weil
descent (W5) consumes: it packages the `𝔽_{p^n}` Kloosterman sums as the power sums
`α^n + β^n` of the local roots produced in `Salt.Weil.LocalFactor`.

Following Harcos §3:

* **The twisted moment** (`kloostermanMoment a b n`): the `𝔽_{p^n}`-Kloosterman sum
  `∑_{t} ψ(Tr_n(a·t + b·t⁻¹))` over `t ∈ 𝔽_{p^n}ˣ`, where `ψ = ZMod.stdAddChar` and `Tr_n`
  is the absolute trace `𝔽_{p^n} → 𝔽_p`. The additive character `ψ ∘ Tr_n` on `𝔽_{p^n}` is
  `traceAddChar p n`. `norm_kloostermanMoment_le` is the trivial bound
  `‖moment‖ ≤ #𝔽_{p^n}ˣ`.

* **F2 — Thm 6, `n = 1`** (`kloostermanMoment_one`): the base case
  `kloostermanMoment a b 1 = kloosterman a b`, via the algebra equivalence
  `GaloisField p 1 ≃ₐ[𝔽_p] 𝔽_p` (`GaloisField.equivZmodP`) under which `Tr_1 = id`
  (`Algebra.trace_self_apply`) and the units reindex `Units.mapEquiv`. Wrapped against the
  local power sum in `kloostermanMoment_one_eq_neg_localPowerSum`:
  `kloostermanMoment a b 1 = −localPowerSum S p 1` with `S = (kloosterman a b).re` (real by
  `kloosterman_im`), i.e. `M₁ = −P₁ = S`, the `n = 1` instance of Thm 6.

The full Thm 6 (`M_n = −(α^n + β^n)` for all `n ≥ 1`) needs the Euler-product / L-function
log-derivative apparatus (Thm 5 + Cor 2 coefficient extraction) which is not yet in the
substrate; see the executor report for the precise gap and route.
-/

namespace Salt.Weil

open scoped BigOperators
open ComplexConjugate

/-! ### Fintype/decidability plumbing for `GaloisField` -/

noncomputable instance instFintypeGaloisField (p n : ℕ) [Fact p.Prime] :
    Fintype (GaloisField p n) := Fintype.ofFinite _

noncomputable instance instDecidableEqGaloisField (p n : ℕ) [Fact p.Prime] :
    DecidableEq (GaloisField p n) := Classical.decEq _

variable {p : ℕ} [Fact p.Prime]

instance : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-! ### The trace additive character and the twisted moment -/

/-- The additive character `ψ_n = ψ ∘ Tr_n` on `𝔽_{p^n}`, where `ψ = ZMod.stdAddChar` is the
standard primitive additive character on `𝔽_p` and `Tr_n : 𝔽_{p^n} → 𝔽_p` is the absolute
trace. Built as `ZMod.stdAddChar.compAddMonoidHom (Algebra.trace _ _).toAddMonoidHom`. -/
noncomputable def traceAddChar (p n : ℕ) [Fact p.Prime] : AddChar (GaloisField p n) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom (Algebra.trace (ZMod p) (GaloisField p n)).toAddMonoidHom

@[simp] theorem traceAddChar_apply (p n : ℕ) [Fact p.Prime] (z : GaloisField p n) :
    traceAddChar p n z = ZMod.stdAddChar (Algebra.trace (ZMod p) (GaloisField p n) z) := rfl

/-- The **twisted Kloosterman moment** `M_n(a, b) = ∑_{t} ψ(Tr_n(a·t + b·t⁻¹))` over units
`t ∈ 𝔽_{p^n}ˣ`, the `𝔽_{p^n}`-Kloosterman sum with the trace character. The sum runs over
the *units*, so `t⁻¹` is the group inverse. The scalars `a b : 𝔽_p` are pushed into `𝔽_{p^n}`
via `algebraMap`. This is the `n`-th moment whose value Harcos Thm 6 identifies with
`−(α^n + β^n)` for the local roots `α, β` of `Salt.Weil.LocalFactor`. -/
noncomputable def kloostermanMoment (a b : ZMod p) (n : ℕ) : ℂ :=
  ∑ t : (GaloisField p n)ˣ,
    traceAddChar p n
      (algebraMap (ZMod p) (GaloisField p n) a * (t : GaloisField p n) +
        algebraMap (ZMod p) (GaloisField p n) b *
          ((t⁻¹ : (GaloisField p n)ˣ) : GaloisField p n))

/-- **Trivial bound.** `‖M_n(a, b)‖ ≤ #𝔽_{p^n}ˣ` from the triangle inequality and
`‖ψ_n z‖ = 1`. (For `n ≥ 1`, `#𝔽_{p^n}ˣ = p^n − 1`.) -/
theorem norm_kloostermanMoment_le (a b : ZMod p) (n : ℕ) :
    ‖kloostermanMoment a b n‖ ≤ (Fintype.card (GaloisField p n)ˣ : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_congr rfl (fun t _ => AddChar.norm_apply _ _), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **Reality.** `conj M_n(a, b) = M_n(a, b)`: the reindex `t ↦ −t` pairs each summand
`ψ_n(a·t + b·t⁻¹)` with its complex conjugate `ψ_n(−(a·t + b·t⁻¹))`, mirroring
`kloosterman_conj`. Hence every moment is real, matching the real power sums `localPowerSum`
of the descent. -/
theorem kloostermanMoment_conj (a b : ZMod p) (n : ℕ) :
    conj (kloostermanMoment a b n) = kloostermanMoment a b n := by
  have hR : 0 < ringChar (GaloisField p n) := by
    rw [← Algebra.ringChar_eq (ZMod p) (GaloisField p n), ZMod.ringChar_zmod_n]
    exact (Fact.out : p.Prime).pos
  unfold kloostermanMoment
  rw [map_sum, ← Equiv.sum_comp (Equiv.neg (GaloisField p n)ˣ)
    (fun t : (GaloisField p n)ˣ => traceAddChar p n
      (algebraMap (ZMod p) (GaloisField p n) a * (t : GaloisField p n) +
        algebraMap (ZMod p) (GaloisField p n) b *
          ((t⁻¹ : (GaloisField p n)ˣ) : GaloisField p n)))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [AddChar.starComp_apply hR, AddChar.inv_apply]
  simp only [Equiv.neg_apply]
  congr 1
  have hinv : ((-t : (GaloisField p n)ˣ)⁻¹ : (GaloisField p n)ˣ) = -t⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
  rw [hinv]
  simp only [Units.val_neg]
  ring

/-- Reality, imaginary-part form: every moment has zero imaginary part. -/
theorem kloostermanMoment_im (a b : ZMod p) (n : ℕ) :
    (kloostermanMoment a b n).im = 0 :=
  Complex.conj_eq_iff_im.mp (kloostermanMoment_conj a b n)

/-! ### F2 — the `n = 1` case (Thm 6 base) -/

/-- **F2 / Harcos Thm 6, `n = 1`.** The first moment is the ordinary `𝔽_p`-Kloosterman sum:
`M₁(a, b) = S(a, b; p)`. Proof: transport the sum along the algebra equivalence
`e : GaloisField p 1 ≃ₐ[𝔽_p] 𝔽_p` (`GaloisField.equivZmodP`), under which `Tr_1 = id`
(`Algebra.trace_eq_of_algEquiv` + `Algebra.trace_self_apply`), the units reindex by
`Units.mapEquiv e`, and `e` fixes the base-field scalars `a, b`. -/
theorem kloostermanMoment_one (a b : ZMod p) :
    kloostermanMoment a b 1 = kloosterman a b := by
  set e : GaloisField p 1 ≃ₐ[ZMod p] ZMod p := GaloisField.equivZmodP p with he
  have htr : ∀ z : GaloisField p 1,
      Algebra.trace (ZMod p) (GaloisField p 1) z = e z := by
    intro z
    rw [← Algebra.trace_eq_of_algEquiv e z, Algebra.trace_self_apply]
  have hAa : e (algebraMap (ZMod p) (GaloisField p 1) a) = a := by
    rw [AlgEquiv.commutes]; simp
  have hAb : e (algebraMap (ZMod p) (GaloisField p 1) b) = b := by
    rw [AlgEquiv.commutes]; simp
  set E : (GaloisField p 1)ˣ ≃* (ZMod p)ˣ :=
    Units.mapEquiv e.toRingEquiv.toMulEquiv with hE
  have hcoe : ∀ u : (GaloisField p 1)ˣ,
      e (u : GaloisField p 1) = ((E u : (ZMod p)ˣ) : ZMod p) := by
    intro u; rw [hE, Units.coe_mapEquiv]; rfl
  unfold kloostermanMoment kloosterman
  refine Fintype.sum_bijective E E.bijective _ _ (fun t => ?_)
  rw [traceAddChar_apply, htr]
  congr 1
  rw [map_add, map_mul, map_mul, hAa, hAb, hcoe t, hcoe (t⁻¹), map_inv E t]

/-- **F2, power-sum form.** `M₁(a, b) = −P₁ = −localPowerSum S p 1` with `S = (kloosterman a
b).re` (the real value of `S(a, b; p)`, real by `kloosterman_im`). Since `P₁ = −S`, this is
`M₁ = S`, the `n = 1` instance of Harcos Thm 6. -/
theorem kloostermanMoment_one_eq_neg_localPowerSum (a b : ZMod p) :
    kloostermanMoment a b 1 = -localPowerSum (kloosterman a b).re p 1 := by
  rw [kloostermanMoment_one, localPowerSum_one, neg_neg]
  refine Complex.ext ?_ ?_
  · simp
  · simp [kloosterman_im a b]

/-! ### The `m`-twist and the Corollary 3 curve-count collapse -/

/-- `Tr_n(m·z) = m·Tr_n(z)` for a base-field scalar `m : 𝔽_p` (`𝔽_p`-linearity of the
trace). -/
private theorem trace_smul_arg (m : ZMod p) {n : ℕ} (z : GaloisField p n) :
    Algebra.trace (ZMod p) (GaloisField p n)
        (algebraMap (ZMod p) (GaloisField p n) m * z)
      = m * Algebra.trace (ZMod p) (GaloisField p n) z := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- **The `m`-twist.** Scaling `(a, b) ↦ (m·a, m·b)` twists the trace character by `m`:
`M_n(m·a, m·b) = ∑_{t} ψ(m·Tr_n(a·t + b·t⁻¹))`. This is the `m`-th term of the character
expansion in Harcos Cor 3, since `m·Tr_n = Tr_n(m·—)` by base-field linearity. -/
theorem kloostermanMoment_twist (a b m : ZMod p) (n : ℕ) :
    kloostermanMoment (m * a) (m * b) n =
      ∑ t : (GaloisField p n)ˣ, ZMod.stdAddChar (m *
        Algebra.trace (ZMod p) (GaloisField p n)
          (algebraMap (ZMod p) (GaloisField p n) a * (t : GaloisField p n) +
            algebraMap (ZMod p) (GaloisField p n) b *
              ((t⁻¹ : (GaloisField p n)ˣ) : GaloisField p n))) := by
  unfold kloostermanMoment
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [traceAddChar_apply]
  congr 1
  have harg :
      algebraMap (ZMod p) (GaloisField p n) (m * a) * (t : GaloisField p n) +
          algebraMap (ZMod p) (GaloisField p n) (m * b) *
            ((t⁻¹ : (GaloisField p n)ˣ) : GaloisField p n)
        = algebraMap (ZMod p) (GaloisField p n) m *
            (algebraMap (ZMod p) (GaloisField p n) a * (t : GaloisField p n) +
              algebraMap (ZMod p) (GaloisField p n) b *
                ((t⁻¹ : (GaloisField p n)ˣ) : GaloisField p n)) := by
    rw [map_mul, map_mul]; ring
  rw [harg, trace_smul_arg]

/-- **Corollary 3, the curve-count collapse (ArtinSchreier form).** Summing the twisted
moments over all `m ∈ 𝔽_p` and applying additive orthogonality collapses the character sum
to the Artin–Schreier fiber count:
`∑_{m ∈ 𝔽_p} M_n(m·a, m·b) = ∑_{t ∈ 𝔽_{p^n}ˣ} #{x : x^p − x = a·t + b·t⁻¹}`.
This is the step of Harcos Cor 3 that consumes `card_artinSchreier_solutions`
(`Salt.Weil.ArtinSchreier`): for each `t`, `∑_{m} ψ(m·Tr_n(a·t+b·t⁻¹)) = p·[Tr_n = 0]`,
and `#{x : x^p − x = a·t + b·t⁻¹} = p·[Tr_n = 0]` too. The remaining step of Cor 3
(completing the square `at² − (x^p−x)t + b = 0 ↦ y² = (x^p−x)² − 4ab`, valid for odd `p`
and `ab ≠ 0`) rewrites the right-hand fiber count as the hyperelliptic-curve point count. -/
theorem sum_kloostermanMoment_twist (a b : ZMod p) {n : ℕ} (hn : n ≠ 0) :
    ∑ m : ZMod p, kloostermanMoment (m * a) (m * b) n =
      ∑ t : (GaloisField p n)ˣ, (Nat.card {x : GaloisField p n //
        x ^ p - x = algebraMap (ZMod p) (GaloisField p n) a * (t : GaloisField p n) +
          algebraMap (ZMod p) (GaloisField p n) b *
            ((t⁻¹ : (GaloisField p n)ˣ) : GaloisField p n)} : ℂ) := by
  simp_rw [kloostermanMoment_twist]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p),
    card_artinSchreier_solutions p n hn, ZMod.card]

end Salt.Weil
