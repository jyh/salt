/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.PsiDefs

/-!
# Large sieve track, nodes L8.2 + L8.3: the BDH variance toolkit

Design: `docs/blueprints/largesieve.md` (W5, BDH). Two independent pieces
consumed by L8.4 (Barban–Davenport–Halberstam):

* **L8.2** (`sum_vonMangoldt_sq_le`): the crude `∑_{n ≤ x} Λ(n)² ≤ C·x·log x`
  bound. Route: `Λ n ≤ log n ≤ log x` on `Icc 1 x`
  (`ArithmeticFunction.vonMangoldt_le_log`), so
  `∑ Λ(n)² ≤ (log x) · ∑ Λ(n) = (log x) · ψ(x)`, then Chebyshev's explicit
  upper bound `ψ(x) ≤ (log 4 + 4) · x`
  (`Chebyshev.psi_le_const_mul_self`, `Mathlib/NumberTheory/Chebyshev.lean`,
  2025). Constant latitude used exactly as the doctrine allows: the landed
  constant is `log 4 + 4` (mathlib's own Chebyshev constant), not the
  `2 log 4` suggested in the node sketch — nothing downstream cares about the
  exact numeral. `Chebyshev.psi` is bridged to the track's `psiTot`-style
  `Finset.Icc 1 x` sum via `Chebyshev.psi_eq_sum_Icc` + `Nat.floor_natCast`
  + `vonMangoldt 0 = 0` (kills the extra `Icc 0 x` vs `Icc 1 x` term).

* **L8.3** (`variance_eq`): the exact residue-variance identity
  `∑_{a reduced} ‖ψ(x;q,a) − ψ(x,χ₀)/φ(q)‖² = (1/φ(q)) ∑_{χ≠χ₀} ‖ψ(x,χ)‖²`.
  Route — finite Plancherel on the units of `ZMod q`:
  1. `psiChi_eq_sum_psiAP`: for **any** `χ : DirichletCharacter ℂ q`,
     `ψ(x,χ) = ∑_{a reduced} χ(a) · ψ(x;q,a)` (residues fiber `Icc 1 x` by
     `n % q`; `Finset.sum_fiberwise_of_maps_to` + `χ(a) = 0` at non-units
     via `MulChar.map_nonunit` drops the non-coprime residues). In
     particular for the principal character `χ₀ = (1 : DirichletCharacter ℂ q)`,
     `ψ(x,χ₀) = ∑_{a reduced} ψ(x;q,a)` (**not** `psiTot x`, since `χ₀`
     vanishes off the coprime residues — exactly as the node brief warns).
  2. `sum_normSq_psiChi_eq`: **full** orthogonality,
     `∑_{χ : DirichletCharacter ℂ q} ‖ψ(x,χ)‖² = φ(q) · ∑_{a reduced} ψ(x;q,a)²`,
     via mathlib's `DirichletCharacter.sum_characters_eq` (full second
     orthogonality relation over **all** `χ`, found in the pin's
     `Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean` — the PB-floor
     fallback hypothesis was **not** needed, see the report). The `Fintype
     (DirichletCharacter ℂ q)` instance is automatic (`CommRing`/`IsDomain`
     ℂ); `HasEnoughRootsOfUnity ℂ n` resolves automatically for every `n`
     since `ℂ` is algebraically closed
     (`RootsOfUnity/AlgebraicallyClosed.lean`). The double-sum expansion uses
     `conj (χ b) = χ (b⁻¹)` for units `b` (proved directly by cancellation,
     not via the `χ⁻¹`/`Ring.inverse` route) to fold the conjugate into a
     single character evaluation `χ(a·b⁻¹)`, then collapses via
     `sum_characters_eq (a * b⁻¹)`.
  3. `variance_eq` assembles both facts algebraically: writing
     `T = ∑_{a reduced} ψ(x;q,a)` and `Q = ∑_{a reduced} ψ(x;q,a)²`, both
     sides reduce to `Q − T²/φ(q)` (mean-subtraction identity; `field_simp`
     once `φ(q) ≠ 0` is in hand from `Nat.totient_pos`).

Integrability/measurability: none — everything is a finite `Finset` sum.
-/

namespace Salt.LS

open ArithmeticFunction Finset ComplexConjugate

/-! ## L8.2 — the crude `Λ²` bound -/

/-- **L8.2.** The crude second-moment bound on von Mangoldt: for `x ≥ 2`,
`∑_{n ≤ x} Λ(n)² ≤ (log 4 + 4) · x · log x`. Route: `Λ n ≤ log n ≤ log x`
turns the square into a single power weighted by `log x`, then Chebyshev's
explicit bound `ψ(x) ≤ (log 4 + 4) x` closes it. Constant latitude used: the
node sketch's `2 log 4` is replaced by mathlib's own Chebyshev constant. -/
theorem sum_vonMangoldt_sq_le (x : ℕ) (hx : 2 ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2 ≤ (Real.log 4 + 4) * x * Real.log x := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast le_trans one_le_two hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have step1 : ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2
      ≤ (∑ n ∈ Finset.Icc 1 x, vonMangoldt n) * Real.log x := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hnx : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hn.2
    have hle : vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hlog : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
    have hnn : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    nlinarith
  have step2 : ∑ n ∈ Finset.Icc 1 x, vonMangoldt n = Chebyshev.psi (x : ℝ) := by
    rw [Chebyshev.psi]
    simp only [Nat.floor_natCast]
    congr 1
  have step3 : Chebyshev.psi (x : ℝ) ≤ (Real.log 4 + 4) * x :=
    Chebyshev.psi_le_const_mul_self (by positivity)
  calc ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n) ^ 2
      ≤ (∑ n ∈ Finset.Icc 1 x, vonMangoldt n) * Real.log x := step1
    _ = Chebyshev.psi (x : ℝ) * Real.log x := by rw [step2]
    _ ≤ (Real.log 4 + 4) * x * Real.log x := mul_le_mul_of_nonneg_right step3 hlogx

/-! ## L8.3 — character orthogonality → residue-class variance -/

/-- The `ψ(x,χ)` expansion over reduced residues: any `χ : DirichletCharacter ℂ q`
satisfies `ψ(x,χ) = ∑_{a reduced} χ(a) · ψ(x;q,a)`. Non-coprime residues drop
out because `χ` vanishes at non-units (`MulChar.map_nonunit`); the `Icc 1 x`
range is fibered by `n % q` (`Finset.sum_fiberwise_of_maps_to`). In particular
`ψ(x,χ₀) = ∑_{a reduced} ψ(x;q,a)` for the principal character `χ₀`, **not**
`psiTot x` — the coprimality filter is essential. -/
theorem psiChi_eq_sum_psiAP {q : ℕ} [NeZero q] (x : ℕ) (χ : DirichletCharacter ℂ q) :
    psiChi x χ
      = ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), χ (a : ZMod q) * (psiAP x q a : ℂ) := by
  set S := (Finset.range q).filter (Nat.Coprime q) with hS
  have hmaps : ∀ n ∈ Finset.Icc 1 x, n % q ∈ Finset.range q := fun n _ =>
    Finset.mem_range.mpr (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q)))
  have step1 : psiChi x χ = ∑ a ∈ Finset.range q, χ (a : ZMod q) * (psiAP x q a : ℂ) := by
    rw [psiChi, ← Finset.sum_fiberwise_of_maps_to hmaps
      (fun n => (vonMangoldt n : ℂ) * χ (n : ZMod q))]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have ha' : a % q = a := Nat.mod_eq_of_lt (Finset.mem_range.mp ha)
    have hcast : (psiAP x q a : ℂ) = ∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % q = a),
        (vonMangoldt n : ℂ) := by
      unfold psiAP
      rw [ha', Complex.ofReal_sum]
    rw [hcast, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Finset.mem_filter] at hn
    have hnq : (n : ZMod q) = (a : ZMod q) := by rw [← ZMod.natCast_mod n q, hn.2]
    rw [hnq]; ring
  have step2 : ∑ a ∈ S, χ (a : ZMod q) * (psiAP x q a : ℂ)
      = ∑ a ∈ Finset.range q, χ (a : ZMod q) * (psiAP x q a : ℂ) := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases hc : Nat.Coprime q a
    · simp [hc]
    · have hnu : ¬ IsUnit (a : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime]; exact fun h => hc h.symm
      simp [hc, MulChar.map_nonunit χ hnu]
  rw [step1, ← step2]

/-- **Full second orthogonality**, Parseval form: summing `‖ψ(x,χ)‖²` over
*all* `χ : DirichletCharacter ℂ q` (not just non-principal) equals
`φ(q) · ∑_{a reduced} ψ(x;q,a)²`. Route: expand each `ψ(x,χ)` via
`psiChi_eq_sum_psiAP`, form the double sum over reduced residues `a, b`, and
collapse the inner `∑_χ χ(a)·conj(χ(b))` via mathlib's full character
orthogonality `DirichletCharacter.sum_characters_eq` (found directly in the
pin; the conductor/primitivity machinery of L7.1–L7.2 was **not** needed
here — this is the *unrestricted* character sum, available for every
modulus with `HasEnoughRootsOfUnity ℂ _`, which resolves automatically since
`ℂ` is algebraically closed). -/
theorem sum_normSq_psiChi_eq {q : ℕ} [NeZero q] (x : ℕ) :
    ∑ χ : DirichletCharacter ℂ q, ‖psiChi x χ‖ ^ 2
      = (q.totient : ℝ) * ∑ a ∈ (Finset.range q).filter (Nat.Coprime q), (psiAP x q a) ^ 2 := by
  set S := (Finset.range q).filter (Nat.Coprime q) with hS
  -- The orthogonality kernel: `∑_χ χ(a)·conj(χ(b)) = φ(q)` if `a = b`, else `0`,
  -- for `b` a unit. `conj (χ b) = χ (b⁻¹)` is proved directly by cancellation
  -- (avoiding the `χ⁻¹`/`Ring.inverse` bridge), then `χ(a)·χ(b⁻¹) = χ(a·b⁻¹)`
  -- folds into a single character evaluation.
  have double_sum_key : ∀ (a b : ZMod q), IsUnit b →
      ∑ χ : DirichletCharacter ℂ q, χ a * conj (χ b) = if a = b then (q.totient : ℂ) else 0 := by
    intro a b hb
    have conj_bridge : ∀ χ : DirichletCharacter ℂ q, conj (χ b) = χ (b⁻¹) := by
      intro χ
      have hb1 : χ (b⁻¹) * χ b = 1 := by
        rw [← map_mul, (ZMod.inv_mul_eq_one_of_isUnit hb b).mpr rfl, map_one]
      have hne : χ b ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hb1; exact one_ne_zero hb1.symm
      have hinv : (χ b)⁻¹ * χ b = 1 := inv_mul_cancel₀ hne
      have final : χ (b⁻¹) = (χ b)⁻¹ := mul_right_cancel₀ hne (hb1.trans hinv.symm)
      rw [starRingEnd_apply, MulChar.star_apply', MulChar.inv_apply_eq_inv']
      exact final.symm
    calc ∑ χ : DirichletCharacter ℂ q, χ a * conj (χ b)
        = ∑ χ : DirichletCharacter ℂ q, χ a * χ (b⁻¹) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [conj_bridge χ]
      _ = ∑ χ : DirichletCharacter ℂ q, χ (a * b⁻¹) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [map_mul]
      _ = if a * b⁻¹ = 1 then (q.totient : ℂ) else 0 :=
          DirichletCharacter.sum_characters_eq ℂ (a * b⁻¹)
      _ = if a = b then (q.totient : ℂ) else 0 := by
          congr 1
          rw [mul_comm, ZMod.inv_mul_eq_one_of_isUnit hb a]
          exact propext eq_comm
  -- Assemble the complex-valued double sum identity, then descend to ℝ.
  have keyC : ∑ χ : DirichletCharacter ℂ q, (psiChi x χ * conj (psiChi x χ))
      = (q.totient : ℂ) * ∑ a ∈ S, (psiAP x q a : ℂ) ^ 2 := by
    calc ∑ χ : DirichletCharacter ℂ q, (psiChi x χ * conj (psiChi x χ))
        = ∑ χ : DirichletCharacter ℂ q,
            (∑ a ∈ S, χ a * (psiAP x q a : ℂ)) * (∑ b ∈ S, conj (χ b) * (psiAP x q b : ℂ)) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [psiChi_eq_sum_psiAP x χ]
          congr 1
          rw [map_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [map_mul, Complex.conj_ofReal]
      _ = ∑ χ : DirichletCharacter ℂ q, ∑ a ∈ S, ∑ b ∈ S,
            (psiAP x q a : ℂ) * (psiAP x q b : ℂ) * (χ a * conj (χ b)) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
          ring
      _ = ∑ a ∈ S, ∑ b ∈ S, (psiAP x q a : ℂ) * (psiAP x q b : ℂ)
            * ∑ χ : DirichletCharacter ℂ q, χ a * conj (χ b) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ a ∈ S, ∑ b ∈ S, (psiAP x q a : ℂ) * (psiAP x q b : ℂ)
            * (if a = b then (q.totient : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
          have hbu : IsUnit (b : ZMod q) := by
            rw [ZMod.isUnit_iff_coprime]
            rw [hS, Finset.mem_filter] at hb
            exact hb.2.symm
          have hab : a ∈ Finset.range q := (Finset.mem_filter.mp (hS ▸ ha)).1
          have hbb : b ∈ Finset.range q := (Finset.mem_filter.mp (hS ▸ hb)).1
          have hcongr : ((a : ZMod q) = (b : ZMod q)) = (a = b) := by
            rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (Finset.mem_range.mp hab),
              Nat.mod_eq_of_lt (Finset.mem_range.mp hbb)]
          rw [double_sum_key (a : ZMod q) (b : ZMod q) hbu]
          simp only [hcongr]
      _ = ∑ a ∈ S, (psiAP x q a : ℂ) ^ 2 * (q.totient : ℂ) := by
          refine Finset.sum_congr rfl (fun a ha => ?_)
          have h0 : ∀ b ∈ S, b ≠ a →
              (psiAP x q a : ℂ) * (psiAP x q b : ℂ)
                * (if a = b then (q.totient : ℂ) else 0) = 0 := by
            intro b _ hne
            simp [Ne.symm hne]
          have h1 : a ∉ S →
              (psiAP x q a : ℂ) * (psiAP x q a : ℂ) * (if a = a then (q.totient : ℂ) else 0) = 0 :=
            fun h => absurd ha h
          rw [Finset.sum_eq_single a h0 h1]
          simp [sq]
      _ = (q.totient : ℂ) * ∑ a ∈ S, (psiAP x q a : ℂ) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          ring
  have real_of_complex : (((∑ χ : DirichletCharacter ℂ q, ‖psiChi x χ‖ ^ 2 : ℝ) : ℂ))
      = (((q.totient : ℝ) * ∑ a ∈ S, (psiAP x q a) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [← keyC]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [← Complex.mul_conj']
  exact_mod_cast real_of_complex

/-- **L8.3.** The residue-class variance identity: the sum-of-squares
discrepancy of `ψ(x;q,a)` from its mean `ψ(x,χ₀)/φ(q)` over reduced residues
equals `(1/φ(q))` times the non-principal character energy. Both sides reduce
to `Q − T²/φ(q)` where `T = ∑_{a reduced} ψ(x;q,a)` and `Q = ∑_{a reduced}
ψ(x;q,a)²`, given `sum_normSq_psiChi_eq` and `Nat.totient_eq_card_coprime`
(the size of the reduced-residue Finset is `φ(q)` by definition). -/
theorem variance_eq {q : ℕ} [NeZero q] (x : ℕ) :
    ∑ a ∈ (Finset.range q).filter (Nat.Coprime q),
        ‖(psiAP x q a : ℂ) - psiChi x (1 : DirichletCharacter ℂ q) / (Nat.totient q : ℂ)‖ ^ 2
      = (1 / (Nat.totient q : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            ‖psiChi x χ‖ ^ 2 := by
  set S := (Finset.range q).filter (Nat.Coprime q) with hS
  set T : ℝ := ∑ a ∈ S, psiAP x q a with hT
  set Q : ℝ := ∑ a ∈ S, (psiAP x q a) ^ 2 with hQ
  have hcard : S.card = q.totient := (Nat.totient_eq_card_coprime q).symm
  have htot_pos : (0 : ℝ) < (q.totient : ℝ) := by
    have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast this
  have htot_ne : (q.totient : ℝ) ≠ 0 := ne_of_gt htot_pos
  -- `ψ(x,χ₀) = (T : ℂ)`, the reduced-residue total (not `psiTot x`).
  have expand1 : psiChi x (1 : DirichletCharacter ℂ q) = (T : ℂ) := by
    rw [hT, psiChi_eq_sum_psiAP x (1 : DirichletCharacter ℂ q), Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have hcop : Nat.Coprime q a := (Finset.mem_filter.mp (hS ▸ ha)).2
    have hu : IsUnit (a : ZMod q) := by rw [ZMod.isUnit_iff_coprime]; exact hcop.symm
    rw [MulChar.one_apply hu, one_mul]
  have hLHS : ∑ a ∈ S,
      ‖(psiAP x q a : ℂ) - psiChi x (1 : DirichletCharacter ℂ q) / (Nat.totient q : ℂ)‖ ^ 2
      = Q - T ^ 2 / q.totient := by
    have expand_sq : ∑ a ∈ S, (psiAP x q a - T / q.totient) ^ 2
        = Q - 2 * (T / q.totient) * T + S.card * (T / q.totient) ^ 2 := by
      have hpt : ∀ a ∈ S, (psiAP x q a - T / q.totient) ^ 2
          = (psiAP x q a) ^ 2 - 2 * (T / q.totient) * psiAP x q a + (T / q.totient) ^ 2 := by
        intro a _; ring
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hQ, hT]
    have hterm : ∀ a ∈ S,
        ‖(psiAP x q a : ℂ) - psiChi x (1 : DirichletCharacter ℂ q) / (Nat.totient q : ℂ)‖ ^ 2
          = (psiAP x q a - T / q.totient) ^ 2 := by
      intro a _
      rw [expand1, show ((T : ℂ)) / (q.totient : ℂ) = (((T / q.totient : ℝ)) : ℂ) by
          push_cast; ring,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_congr rfl hterm, expand_sq, hcard]
    field_simp
    ring
  have hsumsq : ∑ χ : DirichletCharacter ℂ q, ‖psiChi x χ‖ ^ 2 = q.totient * Q := by
    rw [hQ]; exact sum_normSq_psiChi_eq x
  have hone_sq : ‖psiChi x (1 : DirichletCharacter ℂ q)‖ ^ 2 = T ^ 2 := by
    rw [expand1, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hRHS : (1 / (Nat.totient q : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖psiChi x χ‖ ^ 2
      = Q - T ^ 2 / q.totient := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : DirichletCharacter ℂ q)), hsumsq, hone_sq]
    field_simp
  rw [hLHS, hRHS]

end Salt.LS
