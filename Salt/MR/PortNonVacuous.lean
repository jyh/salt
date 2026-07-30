/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PortClose

/-!
# THE PORT'S NON-VACUITY CERTIFICATES — proved, not argued

⟦PORT-AUDIT, 2026-07-30⟧ The port's headline terminals are stated BEHIND GATES:
`PortClose.halaszPrimesChi_pointwise_of_gates` hands out `USetChi.HalaszPrimesChi C c q T`
only after the uniform height floor `T₀ ≤ T` and the four `q`-vs-`T` gates G1–G4, and
`PortClose.mmuChiRate_holds_gated` hands out its rate only inside the conductor window
`q ≤ (log y)^12` and the height window `|t| ≤ y`.  A gated theorem whose gates are
unsatisfiable is a true theorem about the empty set.  This file certifies, IN THE KERNEL,
that none of them is.

## What is certified

* `gates_jointly_satisfiable` — for ANY `T₀ ≥ 3`, ANY `Kq`, ANY `Ks > 0` and ANY modulus `q`,
  a single height `T` meets the floor `T₀ ≤ T` **and** G1, G2, G3, G4 **simultaneously**.
  The witness is explicit: `T = (exp (exp s) − 1)/5` with
  `s = max(a₁, a₂, 1, (4/3)·log M, loglog(5T₀+1))`, `M = max(b₁, b₂, 1)`, where `a₁, a₂` are
  G1's and G2's `loglog(5T+1)` demands and `b₁, b₂` are G3's and G4's demands on the growth
  factor `(log(5T+1))^{3/4}·(loglog(5T+1))^4`.  The `4/3` is what pays for the `3/4`.
* `socket_nonvacuous` — the composition: there are absolute `C, c > 0` such that for EVERY
  modulus `q ≠ 0` there is a height `T ≥ 3` at which `HalaszPrimesChi C c q T` holds
  OUTRIGHT, with no hypothesis in front of it.  The gated pair row really does inhabit the
  socket, at every modulus.
* `mmuChiRate_instantiated` — the `χ`-twisted Möbius rate fired at the EXTREME height
  `t = y` (the top of `MmuChiRate`'s `|t| ≤ y` window), at saving `A = 1`.
* `q_one_in_range` — the conductor gate `q ≤ (log y)^12` is met by `q = 1` from `y = 3` on,
  so the rate's `∀ q` body is not quantifying over nothing.

## The price, named

**G1 is the binding gate.**  `vkStripConst q = 5000·q` (linear, `rfl`), so G1 reads
`8·log(40000 · 5000 q) ≤ loglog(5T+1)`, i.e.

  `log(5T+1) ≥ (2·10⁸ · q)^8`,   `T ≳ exp((2·10⁸ q)^8)/5`.

At `q = 1` that is `T ≳ exp(10^66)` — astronomical, and satisfiable, which is the whole
point of `gates_jointly_satisfiable`.  Growth in the modulus is `exp(q^8)`.  This is fine
for the x-scale consumers (the loglog demand is ~153 + 96·log log q against the ladder's
≫ 285), but it is why the gates cannot be absorbed into a uniform `T₀`: `HalaszPrimesChi`'s
old shape fixed `T₀` before `∀ q`, and every gate here grows with `q` (see PortClose §2's
quantifier-order note).

`Kq` and `Ks` remain `∃`-bound with only positivity exposed, so the certificates say "the
row lives in the T-large-enough regime", never "at this named numeric T".  That is what an
asymptotic socket with one ineffective constant (`Ks`, the Siegel gate) is entitled to
claim, and it is stated here rather than left to prose.
-/

namespace Salt.MR

/-! ## §1 — the four gates, jointly satisfiable at every modulus -/

/-- **THE JOINT-SATISFIABILITY CERTIFICATE.**  For ANY constants `T₀ ≥ 3`, `Kq`, `Ks > 0`
and ANY modulus `q`, there is a height `T` meeting the height floor `T₀ ≤ T` AND all four
gates G1–G4 of `halaszPrimesChi_pointwise_of_gates` simultaneously.

The witness is explicit — `T = (exp (exp s) − 1)/5`, so that `log(5T+1) = exp s` and
`loglog(5T+1) = s`, with

  `s = max(a₁, a₂, 1, (4/3)·log M, loglog(5T₀+1))`,  `M = max(b₁, b₂, 1)`,

`a₁ = 8·log(40000·vkStripConst q)` (G1), `a₂ = 8 + log(20000(vkStripConst q + 8104))/100`
(G2), `b₁ = Kq·log(q(exp(exp 100)+3))` (G3), `b₂ = q^{1/16}/Ks` (G4).  G1 and G2 are then
literally `a₁ ≤ s` and `a₂ ≤ s`; G3 and G4 follow from
`M ≤ exp(s·3/4) ≤ (log(5T+1))^{3/4} ≤ (log(5T+1))^{3/4}·s^4` — the `4/3` in `s` is exactly
what pays for the `3/4` exponent, and `s ≥ 1` is what makes the `s^4` factor free.  No
hypothesis on `Kq` is needed: it enters only through `b₁ ≤ M`. -/
theorem gates_jointly_satisfiable {T₀ Kq Ks : ℝ} (hT₀ : 3 ≤ T₀) (hKs : 0 < Ks) (q : ℕ) :
    ∃ T : ℝ, T₀ ≤ T ∧
      8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) ∧
      8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
          ≤ Real.log (Real.log (5 * T + 1)) ∧
      Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
          ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) ∧
      (q : ℝ) ^ ((1 : ℝ) / 16)
          ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) := by
  set a₁ : ℝ := 8 * Real.log (40000 * vkStripConst q) with ha₁
  set a₂ : ℝ := 8 + Real.log (20000 * (vkStripConst q + 8104)) / 100 with ha₂
  set b₁ : ℝ := Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3)) with hb₁
  set b₂ : ℝ := (q : ℝ) ^ ((1 : ℝ) / 16) / Ks with hb₂
  set M : ℝ := max (max b₁ b₂) 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hM0 : (0 : ℝ) < M := by linarith
  have hT₀pos : (0 : ℝ) < 5 * T₀ + 1 := by linarith
  have hlT₀ : (0 : ℝ) < Real.log (5 * T₀ + 1) := Real.log_pos (by linarith)
  set s : ℝ := max (max (max a₁ a₂) 1)
      (max (4 / 3 * Real.log M) (Real.log (Real.log (5 * T₀ + 1)))) with hsdef
  have hs1 : (1 : ℝ) ≤ s := le_trans (le_max_right (max a₁ a₂) 1) (le_max_left _ _)
  have hsa₁ : a₁ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hsa₂ : a₂ ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hsM : 4 / 3 * Real.log M ≤ s := le_trans (le_max_left _ _) (le_max_right _ _)
  have hsT : Real.log (Real.log (5 * T₀ + 1)) ≤ s :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  set L : ℝ := Real.exp s with hLdef
  set T : ℝ := (Real.exp L - 1) / 5 with hTdef
  -- the two evaluation facts
  have h5T : 5 * T + 1 = Real.exp L := by rw [hTdef]; ring
  have hlog : Real.log (5 * T + 1) = L := by rw [h5T, Real.log_exp]
  have hloglog : Real.log (Real.log (5 * T + 1)) = s := by rw [hlog, hLdef, Real.log_exp]
  -- the shape facts
  have hLs : L ^ ((3 : ℝ) / 4) = Real.exp (s * (3 / 4)) := by
    rw [hLdef, Real.rpow_def_of_pos (Real.exp_pos s), Real.log_exp]
  have hs4 : (1 : ℝ) ≤ s ^ (4 : ℕ) := one_le_pow₀ hs1
  have hMub : M ≤ Real.exp (s * (3 / 4)) := by
    have h : Real.log M ≤ s * (3 / 4) := by linarith
    calc M = Real.exp (Real.log M) := (Real.exp_log hM0).symm
      _ ≤ Real.exp (s * (3 / 4)) := Real.exp_le_exp.mpr h
  have hprod : M ≤ L ^ ((3 : ℝ) / 4) * s ^ (4 : ℕ) := by
    rw [hLs]
    have h := mul_le_mul_of_nonneg_left hs4 (Real.exp_pos (s * (3 / 4))).le
    rw [mul_one] at h
    linarith
  -- the height floor
  have hTT₀ : T₀ ≤ T := by
    have hLge : Real.log (5 * T₀ + 1) ≤ L := by
      calc Real.log (5 * T₀ + 1) = Real.exp (Real.log (Real.log (5 * T₀ + 1))) :=
            (Real.exp_log hlT₀).symm
        _ ≤ Real.exp s := Real.exp_le_exp.mpr hsT
        _ = L := hLdef.symm
    have h2 : 5 * T₀ + 1 ≤ Real.exp L := by
      calc 5 * T₀ + 1 = Real.exp (Real.log (5 * T₀ + 1)) := (Real.exp_log hT₀pos).symm
        _ ≤ Real.exp L := Real.exp_le_exp.mpr hLge
    rw [hTdef]; linarith
  refine ⟨T, hTT₀, ?_, ?_, ?_, ?_⟩
  · rw [hloglog]; exact hsa₁
  · rw [hloglog]; exact hsa₂
  · rw [hloglog, hlog]
    have hb : b₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  · rw [hloglog, hlog]
    have hq : (q : ℝ) ^ ((1 : ℝ) / 16) = Ks * b₂ := by
      rw [hb₂]; field_simp
    rw [hq]
    have hb : b₂ ≤ L ^ ((3 : ℝ) / 4) * s ^ (4 : ℕ) :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hprod
    exact mul_le_mul_of_nonneg_left hb hKs.le

/-- **THE NON-VACUITY CERTIFICATE.**  The gated pair row really does deliver the pointwise
socket: there are absolute `C, c > 0` such that for EVERY modulus `q ≠ 0` there is a height
`T ≥ 3` at which `USetChi.HalaszPrimesChi C c q T` holds outright — no gate, no floor, no
hypothesis in front of it.

Composition only: `halaszPrimesChi_pointwise_of_gates` supplies `(C, c, T₀, Kq, Ks)` and the
gated row, `gates_jointly_satisfiable` supplies the `T` that clears all five conditions at
once, and `3 ≤ T₀ ≤ T` gives the socket's own height floor.  The `T` it produces is the
astronomical one named in the header (`T ≳ exp(10^66)` at `q = 1`); non-vacuity is a
statement about inhabitation, not about size. -/
theorem socket_nonvacuous :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (q : ℕ) [NeZero q], ∃ T : ℝ, 3 ≤ T ∧ HalaszPrimesChi C c q T := by
  obtain ⟨C, c, T₀, Kq, Ks, hC, hc, hT₀, hKq, hKs, hpt⟩ := halaszPrimesChi_pointwise_of_gates
  refine ⟨C, c, hC, hc, ?_⟩
  intro q _
  obtain ⟨T, hT, hG1, hG2, hG3, hG4⟩ := gates_jointly_satisfiable (Kq := Kq) hT₀ hKs q
  exact ⟨T, le_trans hT₀ hT, hpt q T hT hG1 hG2 hG3 hG4⟩

/-! ## §2 — the twisted Möbius rate, fired inside its own windows -/

/-- **THE RATE, AT THE EXTREME HEIGHT.**  `mmuChiRate_holds_gated` at saving `A = 1` and at
the TOP of its height window, `t = y` (`|t| ≤ y` is met with equality, so the `t`-uniformity
is not being read at a soft interior point): for `y` past an ineffective threshold and every
`χ` mod `q` with `q ≤ (log y)^12`,

  `‖MmuChi χ y y‖ ≤ C·y/(log y)`.

The conductor window is inhabited from `y = 3` on by `q_one_in_range`. -/
theorem mmuChiRate_instantiated :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ (Real.log y) ^ (12 : ℕ) →
        ‖MmuChi χ (y : ℝ) y‖ ≤ C * y / (Real.log y) ^ (1 : ℝ) := by
  obtain ⟨C, x₀, hC, h⟩ := mmuChiRate_holds_gated 1 one_pos
  exact ⟨C, x₀, hC, fun y hy q _ χ hq =>
    h y hy q χ hq (y : ℝ) (by rw [abs_of_nonneg (Nat.cast_nonneg y)])⟩

/-- The conductor gate `q ≤ (log y)^12` is met by `q = 1` from `y = 3` on (`log 3 > 1`), so
`mmuChiRate_instantiated`'s `∀ q` body is not quantifying over an empty range. -/
theorem q_one_in_range {y : ℕ} (hy : 3 ≤ y) : ((1 : ℕ) : ℝ) ≤ (Real.log y) ^ (12 : ℕ) := by
  have h3 : (3 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have h1 : (1 : ℝ) ≤ Real.log (y : ℝ) := by
    rw [Real.le_log_iff_exp_le hy0]
    linarith [Real.exp_one_lt_d9]
  simpa using one_le_pow₀ h1

end Salt.MR
