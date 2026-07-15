/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.TwinBar.ParityWall

/-!
# The parity wall — assembly (Q6a-2)

Design: `docs/exploration/q6a-design.md` (D4/D5, post-gate). Builds on the landed
witness pair `Salt/TwinBar/ParityWall.lean` (`sPlus`/`sMinus`, `siftedSum` values,
`|rem d| ≤ 1 + |M_λ(⌊x/d⌋)|`, `SieveAgree`, `sieveAgree_pair`) and the effective
Liouville summatory rate `Salt/TwinBar/LambdaRate.lean` (`MmuRate`,
`LambdaSummatory`, `LambdaSummatory_of_MmuRate`), plus the landed linear-sieve
vocabulary `Salt/Chen/LinearSieve.lean` (`rosserRemainder`, `TruncSieve`,
`errSum_lam_le`, `rosserSieve`).

## What this file lands

* **The concrete core** (the gate's PRIMARY deliverable, unconditional) —
  `rosser_floor_undershoot`: the landed Rosser floor
  `V(s) = totalMass·mainSum(μ⁻) − errSum(μ⁻)` at the LOWER witness satisfies
  `V(sMinus x) ≤ 2 + errSum(sPlus x, μ⁻)`, while `siftedSum(sMinus x) =
  2(π(x) − π(√x))`.  The floor computed from the SHARED main term undershoots
  the true prime mass by the error budget.  Pure algebra + the landed
  lower-Möbius plumbing; inhabited by construction (`μ⁻` = any lower-Möbius
  weight, e.g. the Rosser lower weights `rosserSieve 2 D`).

* **The tolerant wall (shape c)** — `parity_wall`: for the level `D`, budget `B`
  with `rosserRemainder(sPlus/sMinus x, D) ≤ B`, ANY `SieveAgree`-tolerant lower
  certificate `Φ` obeys `Φ(sMinus x) ≤ 2 + 2B`.  Unconditional/algebraic; the
  analytic input is factored into the `rosserRemainder ≤ B` hypotheses,
  discharged by the budget lemma below.

* **The budget lemma** (conditional on `MmuRate` via `LambdaSummatory`) —
  `rosserRemainder_sPlus_le`/`rosserRemainder_sMinus_le`: at level `⌊√x⌋`,
  `rosserRemainder ≤ ⌊√x⌋ + C·x/(log x)^(A−1)`, effective, `= o(π(x) − π(√x))`.

* **The vanishing-proportion corollary** — `no_parity_beating_certificate`: no
  tolerant lower certificate captures a positive proportion of the prime mass of
  `sMinus x` for large `x`.

* **The inhabitation witness** (D5.2, anti-vacuity) — `phiLowerR`, the landed
  lower-Möbius floor packaged as `BoundingSieve → ℝ`, is UNCONDITIONALLY
  `SieveAgree`-tolerant (`phiLowerR_tolerant`) and, given the standard Rosser
  support bound (the single BJS ingredient the corpus abstracts as
  `errSum_lam_le`'s hypothesis), a certificate (`phiLowerR_certificate`).

The wall SHIPS conditional only on the single clean `MmuRate` Prop (the flagged
`Q6a-4`); everything algebraic is unconditional.
-/

open ArithmeticFunction Finset
open scoped Nat.Prime

namespace Salt.TwinBar

/-! ## Nonnegativity trivia -/

/-- `errSum μ ≥ 0` (a sum of `|μ d|·|rem d| ≥ 0`). -/
lemma errSum_nonneg (s : BoundingSieve) (mu : ℕ → ℝ) : 0 ≤ s.errSum mu := by
  rw [BoundingSieve.errSum]
  exact Finset.sum_nonneg fun d _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- `rosserRemainder s bound ≥ 0`. -/
lemma rosserRemainder_nonneg (s : BoundingSieve) (bound : ℝ) :
    0 ≤ Salt.Chen.rosserRemainder s bound := by
  rw [Salt.Chen.rosserRemainder]
  refine Finset.sum_nonneg fun d _ => ?_
  split_ifs <;> positivity

/-! ## The concrete core (D4) — the Rosser floor undershoots

The lower-Möbius floor value `V(s) = totalMass·mainSum(μ⁻) − errSum(μ⁻)`.  For any
lower-Möbius weight `μ⁻`, `V(sMinus x) ≤ 2 + errSum(sPlus x, μ⁻)`, because the main
term reads only the shared fields (`prodPrimes`, `nu`, `totalMass`) and `V(sPlus x)
≤ siftedSum(sPlus x) = 2`. -/

/-- The Rosser floor value `V(s) = totalMass·mainSum(μ⁻) − errSum(μ⁻)`. -/
noncomputable def rosserFloor (s : BoundingSieve) (muMinus : ℕ → ℝ) : ℝ :=
  s.totalMass * s.mainSum muMinus - s.errSum muMinus

/-- The witness pair shares the main term `totalMass·mainSum(μ)` (both read only the
`rfl`-equal fields `prodPrimes`, `nu`, `totalMass`). -/
lemma mainTerm_sPlus_eq_sMinus (x : ℕ) (mu : ℕ → ℝ) :
    (sPlus x).totalMass * (sPlus x).mainSum mu
      = (sMinus x).totalMass * (sMinus x).mainSum mu := by
  simp only [BoundingSieve.mainSum, sPlus_prodPrimes, sMinus_prodPrimes, sPlus_nu,
    sMinus_nu, sPlus_totalMass, sMinus_totalMass]

/-- **The concrete core** (the gate's PRIMARY deliverable, unconditional): for any
lower-Möbius weight `μ⁻`, the Rosser floor at the LOWER witness undershoots:
`V(sMinus x) ≤ 2 + errSum(sPlus x, μ⁻)`.  The main term is shared with the UPPER
witness, whose floor is `≤ siftedSum(sPlus x) = 2`; the two floors differ only by
the error budget, so the lower floor cannot exceed `2` by more than
`errSum(sPlus x, μ⁻)` — yet `siftedSum(sMinus x) = 2(π(x) − π(√x))` is the whole
prime mass. -/
theorem rosser_floor_undershoot (x : ℕ) (hx : 2 ≤ x) (muMinus : ℕ → ℝ)
    (hlm : Salt.BrunLower.IsLowerMoebius muMinus) :
    rosserFloor (sMinus x) muMinus ≤ 2 + (sPlus x).errSum muMinus := by
  have hVplus : rosserFloor (sPlus x) muMinus ≤ 2 := by
    have h := Salt.BrunLower.siftedSum_ge_mainSum_errSum_of_lowerMoebius muMinus hlm (s := sPlus x)
    rw [siftedSum_sPlus x hx] at h
    exact h
  have hM := mainTerm_sPlus_eq_sMinus x muMinus
  have herr : 0 ≤ (sMinus x).errSum muMinus := errSum_nonneg _ _
  unfold rosserFloor at hVplus ⊢
  rw [← hM]
  linarith [hVplus, herr]

/-- **The undershoot, stated against the true prime mass** (D4's divergence punch,
concrete form): the lower floor is `≤ 2 + errSum(sPlus x, μ⁻)`, yet the lower
witness's sifted sum is the entire prime mass `2(π(x) − π(√x))`.  When the error
budget is `o(π(x) − π(√x))` (the budget lemma below, under `MmuRate`), the floor
captures a vanishing proportion. -/
theorem rosser_floor_vs_prime_mass (x : ℕ) (hx : 2 ≤ x) (muMinus : ℕ → ℝ)
    (hlm : Salt.BrunLower.IsLowerMoebius muMinus) :
    rosserFloor (sMinus x) muMinus ≤ 2 + (sPlus x).errSum muMinus
      ∧ (sMinus x).siftedSum
          = 2 * ((Nat.primeCounting x : ℝ) - (Nat.primeCounting (Nat.sqrt x) : ℝ)) :=
  ⟨rosser_floor_undershoot x hx muMinus hlm, siftedSum_sMinus x hx⟩

/-! ## The tolerant wall (shape c, D4)

Any `SieveAgree`-tolerant lower certificate `Φ` obeys `Φ(sMinus x) ≤ 2 + 2B`.  The
proof: the witness pair `SieveAgree`s at any budget both meet (`sieveAgree_pair`);
tolerance bounds `|Φ(sPlus x) − Φ(sMinus x)| ≤ 2B`; the certificate bound gives
`Φ(sPlus x) ≤ siftedSum(sPlus x) = 2`. -/

/-- **The parity wall** (D4, shape c, post-gate: on `sMinus`, tolerant form).  For a
level `D` and budget `B` that the pair's Rosser remainders both meet, every
tolerantly-`SieveAgree`-invariant lower-bound certificate `Φ` captures at most
`2 + 2B` from the prime-detecting witness `sMinus x` — while its true sifted sum is
`2(π(x) − π(√x))`.  No invariant certificate captures a positive proportion of the
primes (made effective by the budget lemma + `no_parity_beating_certificate`). -/
theorem parity_wall (x : ℕ) (hx : 2 ≤ x) (D : ℕ) (B : ℝ)
    (hplus : Salt.Chen.rosserRemainder (sPlus x) (D : ℝ) ≤ B)
    (hminus : Salt.Chen.rosserRemainder (sMinus x) (D : ℝ) ≤ B)
    (Φ : BoundingSieve → ℝ)
    (htol : ∀ s t, SieveAgree s t D B → |Φ s - Φ t| ≤ 2 * B)
    (hcert : ∀ s, Φ s ≤ s.siftedSum) :
    Φ (sMinus x) ≤ 2 + 2 * B := by
  have hagree : SieveAgree (sPlus x) (sMinus x) D B := sieveAgree_pair x D B hplus hminus
  have htol' := htol (sPlus x) (sMinus x) hagree
  have hcertp : Φ (sPlus x) ≤ 2 := by
    have := hcert (sPlus x)
    rwa [siftedSum_sPlus x hx] at this
  rcases abs_le.mp htol' with ⟨h1, _⟩
  linarith [h1, hcertp]

/-! ## The inhabitation witness (D5.2, anti-vacuity)

The landed lower-Möbius floor, packaged as a `BoundingSieve → ℝ` function using the
Rosser *remainder* (the exact budget `SieveAgree` controls).  It is UNCONDITIONALLY
tolerant (`phiLowerR_tolerant`) and — given the standard Rosser support bound (the
single BJS ingredient abstracted as `errSum_lam_le`'s hypothesis) — a certificate
(`phiLowerR_certificate`).  So the wall's hypothesis class is inhabited by the real
lower consumer.

Packaging choice (recorded): the honest floor `totalMass·mainSum(μ⁻) − errSum(μ⁻)`
is a certificate for free (lower-Möbius) but its tolerance needs `errSum ≤
rosserRemainder`; the remainder-packaged floor here has tolerance for free (it reads
`rosserRemainder`, which `SieveAgree` bounds directly) and its certificate property
needs the same `errSum ≤ rosserRemainder` link.  Either way exactly ONE of the two
properties consumes the Rosser support bound; we take the packaging whose tolerance
(the wall's defining hypothesis) is unconditional. -/

/-- The landed lower-Möbius floor packaged with the Rosser remainder:
`Φ_lower(s) = totalMass·mainSum(μ⁻) − rosserRemainder(s, D)`. -/
noncomputable def phiLowerR (muMinus : ℕ → ℝ) (D : ℕ) (s : BoundingSieve) : ℝ :=
  s.totalMass * s.mainSum muMinus - Salt.Chen.rosserRemainder s (D : ℝ)

/-- **`phiLowerR` is `SieveAgree`-tolerant, UNCONDITIONALLY**: under `SieveAgree s t D
B` the main terms cancel (shared fields) and the remainders are both in `[0, B]`, so
`|Φ_lower s − Φ_lower t| = |rR(t) − rR(s)| ≤ B ≤ 2B`. -/
theorem phiLowerR_tolerant (muMinus : ℕ → ℝ) (D : ℕ) (s t : BoundingSieve) (B : ℝ)
    (h : SieveAgree s t D B) :
    |phiLowerR muMinus D s - phiLowerR muMinus D t| ≤ 2 * B := by
  obtain ⟨hpp, hnu, htm, hrs, hrt⟩ := h
  have hmain : s.mainSum muMinus = t.mainSum muMinus := by
    simp only [BoundingSieve.mainSum, hpp, hnu]
  have hns := rosserRemainder_nonneg s (D : ℝ)
  have hnt := rosserRemainder_nonneg t (D : ℝ)
  unfold phiLowerR
  rw [htm, hmain]
  rw [abs_le]
  constructor <;> linarith [hrs, hrt, hns, hnt]

/-- **`phiLowerR` (Rosser lower weights) is a lower-bound certificate**, GIVEN the
standard Rosser support bound `hsupp` (the single BJS ingredient abstracted as
`errSum_lam_le`'s hypothesis).  From the lower-Möbius bound `totalMass·mainSum(μ⁻) −
errSum(μ⁻) ≤ siftedSum` and `errSum(μ⁻) ≤ rosserRemainder(·, D)`. -/
theorem phiLowerR_certificate (S : Salt.Chen.TruncSieve) (hside : S.side = 2) (D : ℕ)
    (hsupp : ∀ (s : BoundingSieve) d, d ∣ s.prodPrimes → S.P d → (d : ℝ) < (D : ℝ))
    (s : BoundingSieve) :
    phiLowerR S.lam D s ≤ s.siftedSum := by
  have hlm := S.isLowerMoebius hside
  have hge := Salt.BrunLower.siftedSum_ge_mainSum_errSum_of_lowerMoebius S.lam hlm (s := s)
  have herr := Salt.Chen.errSum_lam_le S s (bound := (D : ℝ)) (fun d => hsupp s d)
  unfold phiLowerR
  linarith [hge, herr]

/-! ## The budget lemma (D3/D4) — the shared Rosser-remainder budget

Under the effective Liouville summatory rate (`LambdaSummatory A`, discharged from
`MmuRate`), the pair's Rosser remainder at level `⌊√x⌋` is `o(π(x) − π(√x))`:
`rosserRemainder(·, ⌊√x⌋) ≤ ⌊√x⌋ + C·x·(1 + log x)/(log x)^A`.

Derivation (honest, from the landed `|rem d| ≤ 1 + |M_λ(⌊x/d⌋)|`): drop the level
`⌊√x⌋` filter to `Icc 1 ⌊√x⌋` (nonneg terms), split `1 + |M_λ|`; the `∑ 1` crumb is
`⌊√x⌋`; on the `|M_λ|` part every `d ≤ √x` has `⌊x/d⌋ ≥ √x`, so the rate applies
with `log(⌊x/d⌋) ≥ (log x)/4` and `⌊x/d⌋ ≤ x/d`, giving
`≤ C·4^A·x/(log x)^A · ∑_{d≤√x} 1/d ≤ C·4^A·x·(1 + log x)/(log x)^A`
(the harmonic sum `∑_{d≤n} 1/d ≤ 1 + log n`). -/

/-- **The harmonic bound** `∑_{d=1}^{n} 1/d ≤ 1 + log n` (telescoping via
`1/(m+1) ≤ log(m+1) − log m`, from `1 − 1/(m+1) ≤ exp(−1/(m+1))`). -/
lemma sum_inv_Icc_le (n : ℕ) : ∑ d ∈ Finset.Icc 1 n, ((d : ℝ))⁻¹ ≤ 1 + Real.log n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hm1
      have hfrac : (m : ℝ) / ((m : ℝ) + 1) = 1 - 1 / ((m : ℝ) + 1) := by
        rw [eq_sub_iff_add_eq, ← add_div, div_self (by positivity : ((m : ℝ) + 1) ≠ 0)]
      have hpos : (0 : ℝ) < 1 - 1 / ((m : ℝ) + 1) := by
        have h1 : 1 / ((m : ℝ) + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
        linarith
      have hexp : (1 : ℝ) - 1 / ((m : ℝ) + 1) ≤ Real.exp (-(1 / ((m : ℝ) + 1))) := by
        have := Real.add_one_le_exp (-(1 / ((m : ℝ) + 1))); linarith
      have hlogle : Real.log ((m : ℝ) / ((m : ℝ) + 1)) ≤ -(1 / ((m : ℝ) + 1)) := by
        rw [hfrac]
        calc Real.log (1 - 1 / ((m : ℝ) + 1))
            ≤ Real.log (Real.exp (-(1 / ((m : ℝ) + 1)))) := Real.log_le_log hpos hexp
          _ = -(1 / ((m : ℝ) + 1)) := Real.log_exp _
      have hld : Real.log ((m : ℝ) / ((m : ℝ) + 1)) = Real.log m - Real.log ((m : ℝ) + 1) :=
        Real.log_div hm0 (by positivity)
      have hstep : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log m := by
        push_cast
        rw [inv_eq_one_div]
        rw [hld] at hlogle
        linarith
      push_cast at ih hstep ⊢
      linarith [ih, hstep]

/-- **The shared budget** (generic over the witness): from the effective Liouville
rate `|M_λ(y)| ≤ C_λ·y/(log y)^A`, any `BoundingSieve` with `prodPrimes = P(√x)` and
the landed rem bound `|rem d| ≤ 1 + |M_λ(⌊x/d⌋)|` has Rosser remainder at level `√x`
bounded by `√x + C_λ·4^A·x·(1 + log x)/(log x)^A`. -/
lemma witness_rosserRemainder_le {A : ℝ} (hA : 0 < A) {cLam : ℝ} (hcLam : 0 < cLam) {nLam : ℕ}
    (hbd : ∀ y : ℕ, nLam ≤ y → |Mlambda y| ≤ cLam * y / (Real.log y) ^ A)
    (x : ℕ) (hx16 : 16 ≤ x) (hxl : nLam ^ 2 ≤ x)
    (s : BoundingSieve) (hpp : s.prodPrimes = primorial (Nat.sqrt x))
    (hrem : ∀ d, |s.rem d| ≤ 1 + |Mlambda (x / d)|) :
    Salt.Chen.rosserRemainder s ((Nat.sqrt x : ℕ) : ℝ)
      ≤ (Nat.sqrt x : ℝ) + cLam * (4 : ℝ) ^ A * x * (1 + Real.log x) / (Real.log x) ^ A := by
  have hLpos : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hs1 : 0 < Nat.sqrt x := Nat.le_sqrt.mpr (by nlinarith [hx16])
  have hsx0 : nLam ≤ Nat.sqrt x := Nat.le_sqrt.mpr (by rw [← pow_two] at *; omega)
  have hlogs : Real.log x / 4 ≤ Real.log (Nat.sqrt x) := log_natSqrt_ge hx16
  have hCoef0 : (0 : ℝ) ≤ cLam * (4 : ℝ) ^ A * x / (Real.log x) ^ A :=
    div_nonneg (mul_nonneg (mul_nonneg hcLam.le (Real.rpow_nonneg (by norm_num) A))
      (Nat.cast_nonneg _)) (Real.rpow_nonneg hLpos.le A)
  have hCoef1 : (0 : ℝ) ≤ cLam * (4 : ℝ) ^ A / (Real.log x) ^ A :=
    div_nonneg (mul_nonneg hcLam.le (Real.rpow_nonneg (by norm_num) A))
      (Real.rpow_nonneg hLpos.le A)
  -- the per-term rate bound
  have key_d : ∀ d ∈ Finset.Icc 1 (Nat.sqrt x),
      |Mlambda (x / d)| ≤ cLam * (4 : ℝ) ^ A * x / (Real.log x) ^ A * ((d : ℝ))⁻¹ := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    obtain ⟨hd1, hds⟩ := hd
    have hd0 : 0 < d := hd1
    have hts : Nat.sqrt x ≤ x / d := by
      calc Nat.sqrt x ≤ x / Nat.sqrt x := by
              rw [Nat.le_div_iff_mul_le hs1]; exact Nat.sqrt_le x
        _ ≤ x / d := Nat.div_le_div_left hds hd0
    have htx : nLam ≤ x / d := le_trans hsx0 hts
    have hMt := hbd (x / d) htx
    have hlogt : Real.log x / 4 ≤ Real.log ((x / d : ℕ) : ℝ) := by
      refine le_trans hlogs ?_
      apply Real.log_le_log (by exact_mod_cast hs1)
      exact_mod_cast hts
    have hL4pos : 0 < Real.log x / 4 := by linarith
    have hrpow : (Real.log x / 4) ^ A ≤ (Real.log ((x / d : ℕ) : ℝ)) ^ A :=
      Real.rpow_le_rpow hL4pos.le hlogt hA.le
    calc |Mlambda (x / d)|
        ≤ cLam * ((x / d : ℕ) : ℝ) / (Real.log ((x / d : ℕ) : ℝ)) ^ A := hMt
      _ ≤ cLam * ((x / d : ℕ) : ℝ) / (Real.log x / 4) ^ A :=
            div_le_div_of_nonneg_left (mul_nonneg hcLam.le (Nat.cast_nonneg _))
              (Real.rpow_pos_of_pos hL4pos A) hrpow
      _ = cLam * ((x / d : ℕ) : ℝ) * (4 : ℝ) ^ A / (Real.log x) ^ A := by
            rw [Real.div_rpow hLpos.le (by norm_num), div_div_eq_mul_div]
      _ ≤ cLam * (4 : ℝ) ^ A * x / (Real.log x) ^ A * ((d : ℝ))⁻¹ := by
            have hcast : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) * ((d : ℝ))⁻¹ := by
              have h := Nat.cast_div_le (m := x) (n := d) (α := ℝ)
              rwa [div_eq_mul_inv] at h
            calc cLam * ((x / d : ℕ) : ℝ) * (4 : ℝ) ^ A / (Real.log x) ^ A
                = (cLam * (4 : ℝ) ^ A / (Real.log x) ^ A) * ((x / d : ℕ) : ℝ) := by ring
              _ ≤ (cLam * (4 : ℝ) ^ A / (Real.log x) ^ A) * ((x : ℝ) * ((d : ℝ))⁻¹) :=
                    mul_le_mul_of_nonneg_left hcast hCoef1
              _ = cLam * (4 : ℝ) ^ A * x / (Real.log x) ^ A * ((d : ℝ))⁻¹ := by ring
  -- the `|M_λ|` part
  have hMsum : ∑ d ∈ Finset.Icc 1 (Nat.sqrt x), |Mlambda (x / d)|
      ≤ cLam * (4 : ℝ) ^ A * x * (1 + Real.log x) / (Real.log x) ^ A := by
    calc ∑ d ∈ Finset.Icc 1 (Nat.sqrt x), |Mlambda (x / d)|
        ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt x),
            cLam * (4 : ℝ) ^ A * x / (Real.log x) ^ A * ((d : ℝ))⁻¹ := Finset.sum_le_sum key_d
      _ = (cLam * (4 : ℝ) ^ A * x / (Real.log x) ^ A) *
            ∑ d ∈ Finset.Icc 1 (Nat.sqrt x), ((d : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (cLam * (4 : ℝ) ^ A * x / (Real.log x) ^ A) * (1 + Real.log x) := by
            apply mul_le_mul_of_nonneg_left _ hCoef0
            have hle : Real.log (Nat.sqrt x) ≤ Real.log x :=
              Real.log_le_log (by exact_mod_cast hs1) (by exact_mod_cast Nat.sqrt_le_self x)
            linarith [sum_inv_Icc_le (Nat.sqrt x), hle]
      _ = cLam * (4 : ℝ) ^ A * x * (1 + Real.log x) / (Real.log x) ^ A := by ring
  -- assemble
  calc Salt.Chen.rosserRemainder s ((Nat.sqrt x : ℕ) : ℝ)
      = ∑ d ∈ Nat.divisors (primorial (Nat.sqrt x)),
          if (d : ℝ) < ((Nat.sqrt x : ℕ) : ℝ) then |s.rem d| else 0 := by
        rw [Salt.Chen.rosserRemainder, hpp]
    _ ≤ ∑ d ∈ Nat.divisors (primorial (Nat.sqrt x)),
          if (d : ℝ) < ((Nat.sqrt x : ℕ) : ℝ) then (1 + |Mlambda (x / d)|) else 0 := by
        apply Finset.sum_le_sum
        intro d _
        split_ifs with h
        · exact hrem d
        · exact le_refl _
    _ = ∑ d ∈ (Nat.divisors (primorial (Nat.sqrt x))).filter
            (fun d : ℕ => (d : ℝ) < ((Nat.sqrt x : ℕ) : ℝ)), (1 + |Mlambda (x / d)|) := by
        rw [Finset.sum_filter]
    _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt x), (1 + |Mlambda (x / d)|) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [Finset.mem_filter] at hd
          obtain ⟨hdiv, hlt⟩ := hd
          rw [Finset.mem_Icc]
          have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hdiv
          have hd_lt : d < Nat.sqrt x := by exact_mod_cast hlt
          exact ⟨hd1, le_of_lt hd_lt⟩
        · intro d _ _; positivity
    _ = (Nat.sqrt x : ℝ) + ∑ d ∈ Finset.Icc 1 (Nat.sqrt x), |Mlambda (x / d)| := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp [Finset.sum_const, Nat.card_Icc]
    _ ≤ (Nat.sqrt x : ℝ) + cLam * (4 : ℝ) ^ A * x * (1 + Real.log x) / (Real.log x) ^ A := by
        linarith [hMsum]

/-- **The budget lemma, upper witness** (D4's `Bbudget`): under `LambdaSummatory A`,
`rosserRemainder(sPlus x, ⌊√x⌋) ≤ ⌊√x⌋ + C·x·(1 + log x)/(log x)^A` for `x` large. -/
theorem rosserRemainder_sPlus_le (A : ℝ) (hA : 0 < A) (hLS : LambdaSummatory A) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ x : ℕ, x₀ ≤ x →
      Salt.Chen.rosserRemainder (sPlus x) ((Nat.sqrt x : ℕ) : ℝ)
        ≤ (Nat.sqrt x : ℝ) + C * x * (1 + Real.log x) / (Real.log x) ^ A := by
  obtain ⟨cLam, nLam, hcLam, hbd⟩ := hLS
  refine ⟨cLam * (4 : ℝ) ^ A, max 16 (nLam ^ 2), by positivity, ?_⟩
  intro x hx
  have hx16 : 16 ≤ x := le_trans (le_max_left _ _) hx
  have hxl : nLam ^ 2 ≤ x := le_trans (le_max_right _ _) hx
  exact witness_rosserRemainder_le hA hcLam hbd x hx16 hxl (sPlus x) (sPlus_prodPrimes x)
    (sPlus_rem_bound x)

/-- **The budget lemma, lower witness**: same bound for `sMinus x` (identical rem
bound), so the pair shares the `SieveAgree` budget. -/
theorem rosserRemainder_sMinus_le (A : ℝ) (hA : 0 < A) (hLS : LambdaSummatory A) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ x : ℕ, x₀ ≤ x →
      Salt.Chen.rosserRemainder (sMinus x) ((Nat.sqrt x : ℕ) : ℝ)
        ≤ (Nat.sqrt x : ℝ) + C * x * (1 + Real.log x) / (Real.log x) ^ A := by
  obtain ⟨cLam, nLam, hcLam, hbd⟩ := hLS
  refine ⟨cLam * (4 : ℝ) ^ A, max 16 (nLam ^ 2), by positivity, ?_⟩
  intro x hx
  have hx16 : 16 ≤ x := le_trans (le_max_left _ _) hx
  have hxl : nLam ^ 2 ≤ x := le_trans (le_max_right _ _) hx
  exact witness_rosserRemainder_le hA hcLam hbd x hx16 hxl (sMinus x) (sMinus_prodPrimes x)
    (sMinus_rem_bound x)

/-! ## The effective wall + the vanishing-proportion corollary (D4)

Combining the tolerant wall with the budget lemma: under `LambdaSummatory A`, every
tolerant lower certificate obeys `Φ(sMinus x) ≤ 2 + 2·(⌊√x⌋ + C·x·(1 + log x)/(log
x)^A)` for `x` large — the RHS is `o(π(x) − π(√x))` for `A > 2`, so (with the
Chebyshev lower bound `π(x) ≥ (x·log2 − log(x+1))/log x`) no tolerant certificate
captures a positive proportion of the prime mass. -/

/-- **The effective wall**: under `LambdaSummatory A`, every certificate that is
`SieveAgree`-tolerant at every level obeys the effective bound
`Φ(sMinus x) ≤ 2 + 2·(⌊√x⌋ + C·x·(1 + log x)/(log x)^A)` for `x` large. -/
theorem parity_wall_effective (A : ℝ) (hA : 0 < A) (hLS : LambdaSummatory A)
    (Φ : BoundingSieve → ℝ)
    (htol : ∀ (D : ℕ) (B : ℝ), ∀ s t, SieveAgree s t D B → |Φ s - Φ t| ≤ 2 * B)
    (hcert : ∀ s, Φ s ≤ s.siftedSum) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ x : ℕ, x₀ ≤ x →
      Φ (sMinus x)
        ≤ 2 + 2 * ((Nat.sqrt x : ℝ) + C * x * (1 + Real.log x) / (Real.log x) ^ A) := by
  obtain ⟨cLam, nLam, hcLam, hbd⟩ := hLS
  refine ⟨cLam * (4 : ℝ) ^ A, max 16 (nLam ^ 2), by positivity, ?_⟩
  intro x hx
  have hx16 : 16 ≤ x := le_trans (le_max_left _ _) hx
  have hxl : nLam ^ 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx2 : 2 ≤ x := by omega
  have hplus := witness_rosserRemainder_le hA hcLam hbd x hx16 hxl (sPlus x)
    (sPlus_prodPrimes x) (sPlus_rem_bound x)
  have hminus := witness_rosserRemainder_le hA hcLam hbd x hx16 hxl (sMinus x)
    (sMinus_prodPrimes x) (sMinus_rem_bound x)
  set B := (Nat.sqrt x : ℝ) + cLam * (4 : ℝ) ^ A * x * (1 + Real.log x) / (Real.log x) ^ A with hB
  exact parity_wall x hx2 (Nat.sqrt x) B hplus hminus Φ (htol (Nat.sqrt x) B) hcert

/-! ## Numeric / anti-vacuity sanity (D5)

The hypothesis classes are non-vacuously instantiable: the zero weight is lower
Möbius (so the concrete core `rosser_floor_undershoot` fires), and the concrete
witness numerics for the pair are landed in `ParityWall.lean`. -/

/-- The zero weight is lower Möbius (a trivial certificate; the anti-vacuity witness
for the concrete core, the nontrivial one being the Rosser lower weights). -/
lemma isLowerMoebius_zero : Salt.BrunLower.IsLowerMoebius (fun _ => 0) := by
  intro n
  simp only [Finset.sum_const_zero]
  split_ifs <;> norm_num

example : rosserFloor (sMinus 100) (fun _ => 0) ≤ 2 + (sPlus 100).errSum (fun _ => 0) :=
  rosser_floor_undershoot 100 (by norm_num) _ isLowerMoebius_zero

/-! ## The vanishing-proportion punch (D4) — `no_parity_beating_certificate`

At a FIXED level `D`, the shared budget `rosserRemainder(·, D)` is `o(π(x) − π(√x))`
(the crumb count is the constant `D` and the `M_λ`-part is `o(x/log x)` for `A > 2`),
so — combining with `pi_ge` (Chebyshev) — no lower certificate that is
`SieveAgree`-tolerant at level `D` captures a positive proportion of the prime mass
of `sMinus x`.  The hypothesis class is honestly inhabited by `phiLowerR μ⁻ D` (its
`phiLowerR_tolerant` is tolerance at exactly this level `D`, modulo the flagged
Rosser support bound for its certificate property). -/

/-- `rosserRemainder` is monotone in the truncation level. -/
lemma rosserRemainder_mono (s : BoundingSieve) {b₁ b₂ : ℝ} (h : b₁ ≤ b₂) :
    Salt.Chen.rosserRemainder s b₁ ≤ Salt.Chen.rosserRemainder s b₂ := by
  rw [Salt.Chen.rosserRemainder, Salt.Chen.rosserRemainder]
  apply Finset.sum_le_sum
  intro d _
  split_ifs with h1 h2
  · exact le_refl _
  · exact absurd (lt_of_lt_of_le h1 h) h2
  · positivity
  · exact le_refl _

/-- `π(n) ≤ n + 1` (the prime counting function counts a subset of `{0,…,n}`). -/
lemma primeCounting_le (n : ℕ) : Nat.primeCounting n ≤ n + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting']
  exact Nat.count_le Nat.Prime

open Filter Topology in
/-- `log n / n → 0`. -/
lemma tendsto_log_div_self : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  exact h.comp tendsto_natCast_atTop_atTop

open Filter Topology in
/-- `log n / √n → 0`. -/
lemma tendsto_log_div_sqrt : Tendsto (fun n : ℕ => Real.log n / Real.sqrt n) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1/(2:ℝ) by norm_num)).tendsto_div_nhds_zero
  have h2 := h.comp tendsto_natCast_atTop_atTop
  simp only [← Real.sqrt_eq_rpow] at h2
  exact h2

open Filter Topology in
/-- `(1 + log n)/(log n)^(A-1) → 0` for `A > 2`. -/
lemma tendsto_succ_log_div_rpow {A : ℝ} (hA : 2 < A) :
    Tendsto (fun n : ℕ => (1 + Real.log n) / (Real.log n) ^ (A - 1)) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun n : ℕ => 2 / (Real.log n) ^ (A - 2))
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hlp : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    have hlp : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    have hlogn : (1:ℝ) ≤ Real.log n := by
      have h13 : (1:ℝ) ≤ Real.log 3 := by
        rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
        exact Real.log_le_log (Real.exp_pos 1) he3.le
      have : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity), show A - 1 = (A - 2) + 1 by ring,
        Real.rpow_add hlp, Real.rpow_one]
    have hp : (0:ℝ) ≤ (Real.log n) ^ (A - 2) := by positivity
    have h2 : 1 + Real.log n ≤ 2 * Real.log n := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hp, hp, hlp]
  · have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hneg : Tendsto (fun u : ℝ => 2 * u ^ (-(A - 2))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (show (0:ℝ) < A - 2 by linarith)).const_mul 2
    refine Filter.Tendsto.congr' ?_ (hneg.comp hlog)
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hlp : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    simp only [Function.comp_apply]
    rw [Real.rpow_neg hlp.le]; ring

open Filter Topology in
/-- `⌊√n⌋·log n / n → 0` (bounded above by `log n / √n`). -/
lemma tendsto_natSqrt_log_div_self :
    Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ) * (Real.log n / n)) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun n : ℕ => Real.log n / Real.sqrt n) _ _ tendsto_log_div_sqrt
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hxpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hxpos
    have hlog0 : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have hsx : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
    have heq : Real.sqrt n * (Real.log n / n) = Real.log n / Real.sqrt n := by
      rw [eq_div_iff (ne_of_gt hspos)]
      have : Real.sqrt n * (Real.log n / n) * Real.sqrt n
          = Real.log n * (Real.sqrt n * Real.sqrt n) / n := by ring
      rw [this, Real.mul_self_sqrt hxpos.le, mul_div_assoc, div_self (ne_of_gt hxpos), mul_one]
    calc (Nat.sqrt n : ℝ) * (Real.log n / n)
        ≤ Real.sqrt n * (Real.log n / n) := by
          apply mul_le_mul_of_nonneg_right hsx (by positivity)
      _ = Real.log n / Real.sqrt n := heq

open Filter Topology in
/-- **No parity-beating certificate** (D4's vanishing-proportion punch).  Under
`LambdaSummatory A` (`A > 2`), for any FIXED level `D ≥ 2`, no lower-bound certificate
`Φ` that is `SieveAgree`-tolerant at level `D` captures a positive proportion of the
prime mass of `sMinus x` (`siftedSum(sMinus x) = 2(π(x) − π(√x))`) for large `x`.
The hypothesis class is honestly inhabited by the landed lower floor `phiLowerR μ⁻ D`
(tolerant at exactly level `D` by `phiLowerR_tolerant`, a certificate given the
flagged Rosser support bound by `phiLowerR_certificate`). -/
theorem no_parity_beating_certificate (A : ℝ) (hA : 2 < A) (hLS : LambdaSummatory A)
    (D : ℕ) (_hD : 2 ≤ D) (Φ : BoundingSieve → ℝ)
    (htol : ∀ s t (B : ℝ), SieveAgree s t D B → |Φ s - Φ t| ≤ 2 * B)
    (hcert : ∀ s, Φ s ≤ s.siftedSum) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in atTop, c * (sMinus x).siftedSum ≤ Φ (sMinus x) := by
  rintro ⟨c, hc, hev⟩
  obtain ⟨cLam, nLam, hcLam, hbd⟩ := hLS
  set β : ℕ → ℝ :=
    fun x => (Nat.sqrt x : ℝ) + cLam * (4 : ℝ) ^ A * x * (1 + Real.log x) / (Real.log x) ^ A
    with hβ
  -- (1) the effective ceiling: for x large, Φ(sMinus x) ≤ 2 + 2·β x
  have hceil : ∀ᶠ x : ℕ in atTop, Φ (sMinus x) ≤ 2 + 2 * β x := by
    filter_upwards [eventually_ge_atTop (max 16 (nLam ^ 2)), eventually_ge_atTop (D ^ 2)]
      with x hx hxD
    have hx16 : 16 ≤ x := le_trans (le_max_left _ _) hx
    have hxl : nLam ^ 2 ≤ x := le_trans (le_max_right _ _) hx
    have hx2 : 2 ≤ x := by omega
    have hDsx : (D : ℝ) ≤ (Nat.sqrt x : ℝ) := by
      have : D ≤ Nat.sqrt x := Nat.le_sqrt'.mpr hxD
      exact_mod_cast this
    have hp0 := witness_rosserRemainder_le (by linarith) hcLam hbd x hx16 hxl (sPlus x)
      (sPlus_prodPrimes x) (sPlus_rem_bound x)
    have hm0 := witness_rosserRemainder_le (by linarith) hcLam hbd x hx16 hxl (sMinus x)
      (sMinus_prodPrimes x) (sMinus_rem_bound x)
    have hplus : Salt.Chen.rosserRemainder (sPlus x) (D : ℝ) ≤ β x :=
      (rosserRemainder_mono (sPlus x) hDsx).trans hp0
    have hminus : Salt.Chen.rosserRemainder (sMinus x) (D : ℝ) ≤ β x :=
      (rosserRemainder_mono (sMinus x) hDsx).trans hm0
    exact parity_wall x hx2 D (β x) hplus hminus Φ (fun s t => htol s t (β x)) hcert
  -- (2) the numerator rate → 0
  have hnum : Tendsto (fun x : ℕ => (2 + 2 * β x) * (Real.log x / x)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun x : ℕ => 2 * (Real.log x / x)
        + 2 * ((Nat.sqrt x : ℝ) * (Real.log x / x))
        + 2 * cLam * (4 : ℝ) ^ A * ((1 + Real.log x) / (Real.log x) ^ (A - 1)))
        atTop (𝓝 0) := by
      have t1 := tendsto_log_div_self.const_mul 2
      have t2 := tendsto_natSqrt_log_div_self.const_mul 2
      have t3 := (tendsto_succ_log_div_rpow hA).const_mul (2 * cLam * (4 : ℝ) ^ A)
      simpa using (t1.add t2).add t3
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with x hx2
    have hlp : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx2)
    have hx0 : (x : ℝ) ≠ 0 := by positivity
    have hlx : Real.log x ≠ 0 := ne_of_gt hlp
    have hlA : (Real.log x) ^ A ≠ 0 := by positivity
    have hpow : (Real.log x) ^ (A - 1) = (Real.log x) ^ A / Real.log x := by
      rw [Real.rpow_sub hlp, Real.rpow_one]
    rw [hβ]
    simp only [hpow]
    field_simp
    ring
  -- (3) the prime mass, divided by x/log x, stays ≥ c·log 2
  have hden : ∀ᶠ x : ℕ in atTop,
      c * Real.log 2 ≤ (c * (sMinus x).siftedSum) * (Real.log x / x) := by
    have hbr : Tendsto (fun x : ℕ => 3 * (Real.log x / x) + (Nat.sqrt x : ℝ) * (Real.log x / x))
        atTop (𝓝 0) := by
      simpa using (tendsto_log_div_self.const_mul 3).add tendsto_natSqrt_log_div_self
    have hbr2 : ∀ᶠ x : ℕ in atTop,
        3 * (Real.log x / x) + (Nat.sqrt x : ℝ) * (Real.log x / x) < Real.log 2 / 2 :=
      hbr.eventually (eventually_lt_nhds (by positivity))
    filter_upwards [hbr2, eventually_ge_atTop 2] with x hbrx hx2
    have hlp : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx2)
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hx0 : (x : ℝ) ≠ 0 := ne_of_gt hxpos
    have hlx : Real.log x ≠ 0 := ne_of_gt hlp
    have hrpos : (0 : ℝ) ≤ Real.log x / x := by positivity
    rw [siftedSum_sMinus x hx2]
    have hpi := Chebyshev.pi_ge x
    have hpisx : (Nat.primeCounting (Nat.sqrt x) : ℝ) ≤ (Nat.sqrt x : ℝ) + 1 := by
      have := primeCounting_le (Nat.sqrt x); exact_mod_cast this
    have hpi_mult : Real.log 2 - Real.log ((x : ℝ) + 1) / x
        ≤ (Nat.primeCounting x : ℝ) * (Real.log x / x) := by
      have h := mul_le_mul_of_nonneg_right hpi hrpos
      rwa [show ((x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1)) / Real.log x * (Real.log x / x)
            = Real.log 2 - Real.log ((x : ℝ) + 1) / x from by field_simp] at h
    have hpisx_mult : (Nat.primeCounting (Nat.sqrt x) : ℝ) * (Real.log x / x)
        ≤ (Nat.sqrt x : ℝ) * (Real.log x / x) + Real.log x / x := by
      have h := mul_le_mul_of_nonneg_right hpisx hrpos
      rwa [add_mul, one_mul] at h
    have hlogx1 : Real.log ((x : ℝ) + 1) ≤ 2 * Real.log x := by
      have hle : (x : ℝ) + 1 ≤ (x : ℝ) ^ 2 := by
        have : (2 : ℝ) ≤ x := by exact_mod_cast hx2
        nlinarith
      calc Real.log ((x : ℝ) + 1) ≤ Real.log ((x : ℝ) ^ 2) := Real.log_le_log (by positivity) hle
        _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
    have hlogx1_div : Real.log ((x : ℝ) + 1) / x ≤ 2 * (Real.log x / x) := by
      rw [mul_div_assoc']; gcongr
    have hQ : Real.log 2 / 2 ≤ ((Nat.primeCounting x : ℝ)
        - (Nat.primeCounting (Nat.sqrt x) : ℝ)) * (Real.log x / x) := by
      have hexp : ((Nat.primeCounting x : ℝ) - (Nat.primeCounting (Nat.sqrt x) : ℝ))
          * (Real.log x / x)
          = (Nat.primeCounting x : ℝ) * (Real.log x / x)
            - (Nat.primeCounting (Nat.sqrt x) : ℝ) * (Real.log x / x) := by ring
      rw [hexp]
      linarith [hpi_mult, hpisx_mult, hlogx1_div, hbrx]
    calc c * Real.log 2 = 2 * c * (Real.log 2 / 2) := by ring
      _ ≤ 2 * c * (((Nat.primeCounting x : ℝ) - (Nat.primeCounting (Nat.sqrt x) : ℝ))
            * (Real.log x / x)) := by
          apply mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = c * (2 * ((Nat.primeCounting x : ℝ) - (Nat.primeCounting (Nat.sqrt x) : ℝ)))
            * (Real.log x / x) := by ring
  -- (4) combine: the ceiling rate drops below c·log 2, contradicting hden through hev
  have hlog2pos : (0 : ℝ) < c * Real.log 2 := by positivity
  have h1 : ∀ᶠ x : ℕ in atTop, (2 + 2 * β x) * (Real.log x / x) < c * Real.log 2 :=
    hnum.eventually (eventually_lt_nhds hlog2pos)
  have hkill : ∀ᶠ x : ℕ in atTop, 2 + 2 * β x < c * (sMinus x).siftedSum := by
    filter_upwards [h1, hden, eventually_ge_atTop 2] with x hx1 hxden hx2
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hlp : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx2)
    have hrpos : (0 : ℝ) ≤ Real.log x / x := by positivity
    have hlt : (2 + 2 * β x) * (Real.log x / x)
        < (c * (sMinus x).siftedSum) * (Real.log x / x) := lt_of_lt_of_le hx1 hxden
    exact lt_of_mul_lt_mul_right hlt hrpos
  have hfalse : ∀ᶠ x : ℕ in atTop, False := by
    filter_upwards [hev, hceil, hkill] with x h1 h2 h3
    linarith [h1, h2, h3]
  rcases hfalse.exists with ⟨x, hx⟩
  exact hx

end Salt.TwinBar
