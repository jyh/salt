/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.MomentAtom
import Salt.Twelve.MarkedPrime

/-!
# W2-1 (P3.a) — the budget-moment assembly (explicit-gaps sieve, card W2-1)

Analytic assembly on the landed one-dimensional atoms.  Two deliverables:

* `beta_sum` — the exact rational Beta identity
  `∑_{j≤b} C(b,j)·(−1)^j/(c+j+1) = c!·b!/(c+b+1)!` (induction on `b`,
  Pascal + the recurrence `f(c,b+1) = f(c,b) − f(c+1,b)`).
* `budget_moment` — the normalized `φ`-moment with the budget factor
  `β = c!·b!/(c+b+1)!`, error ABSOLUTE in `z` (uses `z ≤ R`), obtained by
  binomial-expanding the budget weight and feeding each slice to `moment_atom`.
-/

open Finset

namespace Salt.Twelve

/-! ## The Beta identity `beta_sum` (pure ℚ, exact) -/

/-- **Exact rational Beta identity.**
`∑_{j=0}^{b} C(b,j)·(−1)^j/(c+j+1) = c!·b!/(c+b+1)!`.  Proved by induction on
`b`, generalizing `c`, via the recurrence `f(c,b+1) = f(c,b) − f(c+1,b)`
(Pascal + reindexing). -/
theorem beta_sum (c b : ℕ) :
    (∑ j ∈ Finset.range (b + 1), (b.choose j : ℚ) * (-1) ^ j / (c + j + 1))
      = (c.factorial * b.factorial : ℚ) / (c + b + 1).factorial := by
  induction b generalizing c with
  | zero =>
      rw [Finset.sum_range_one]
      have h1 : (c.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos c).ne'
      have h2 : (c : ℚ) + 1 ≠ 0 := by positivity
      simp only [Nat.choose_self, Nat.cast_one, pow_zero, mul_one, Nat.cast_zero, add_zero,
        Nat.factorial_zero, Nat.factorial_succ]
      push_cast
      field_simp
  | succ b ih =>
      -- The recurrence `f(c,b+1) = f(c,b) − f(c+1,b)`.
      have key :
          (∑ j ∈ Finset.range (b + 1 + 1), ((b + 1).choose j : ℚ) * (-1) ^ j / (↑c + ↑j + 1))
            = (∑ j ∈ Finset.range (b + 1), (b.choose j : ℚ) * (-1) ^ j / (↑c + ↑j + 1))
              - (∑ j ∈ Finset.range (b + 1),
                  (b.choose j : ℚ) * (-1) ^ j / (((c + 1 : ℕ) : ℚ) + ↑j + 1)) := by
        -- `A := ∑ C(b,j)·(−1)^{j+1}/(c+j+2)`,  `B := ∑ C(b,j+1)·(−1)^{j+1}/(c+j+2)`
        -- LHS = 1/(c+1) + A + B ; S1 = 1/(c+1) + B ; S2 = −A.
        have hS2 :
            (∑ j ∈ Finset.range (b + 1),
                (b.choose j : ℚ) * (-1) ^ j / (((c + 1 : ℕ) : ℚ) + ↑j + 1))
              = - ∑ j ∈ Finset.range (b + 1),
                  (b.choose j : ℚ) * (-1) ^ (j + 1) / (↑c + ↑j + 2) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [pow_succ]
          have hd : (((c + 1 : ℕ) : ℚ) + (↑j : ℚ) + 1) = ↑c + ↑j + 2 := by push_cast; ring
          rw [hd]
          ring
        have hS1 :
            (∑ j ∈ Finset.range (b + 1), (b.choose j : ℚ) * (-1) ^ j / (↑c + ↑j + 1))
              = 1 / ((c : ℚ) + 1)
                + ∑ j ∈ Finset.range b,
                    (b.choose (j + 1) : ℚ) * (-1) ^ (j + 1) / (↑c + ↑j + 2) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, Nat.cast_zero,
            add_zero]
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          push_cast
          ring
        have hLHS :
            (∑ j ∈ Finset.range (b + 1 + 1), ((b + 1).choose j : ℚ) * (-1) ^ j / (↑c + ↑j + 1))
              = 1 / ((c : ℚ) + 1)
                + ((∑ j ∈ Finset.range (b + 1),
                      (b.choose j : ℚ) * (-1) ^ (j + 1) / (↑c + ↑j + 2))
                  + (∑ j ∈ Finset.range (b + 1),
                      (b.choose (j + 1) : ℚ) * (-1) ^ (j + 1) / (↑c + ↑j + 2))) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, Nat.cast_zero,
            add_zero]
          rw [add_comm, ← Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [Nat.choose_succ_succ]
          push_cast
          ring
        -- `B = B'`: the top term of `B` vanishes (`C(b,b+1) = 0`).
        have hB :
            (∑ j ∈ Finset.range (b + 1),
                (b.choose (j + 1) : ℚ) * (-1) ^ (j + 1) / (↑c + ↑j + 2))
              = ∑ j ∈ Finset.range b,
                  (b.choose (j + 1) : ℚ) * (-1) ^ (j + 1) / (↑c + ↑j + 2) := by
          rw [Finset.sum_range_succ]
          rw [Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_div, add_zero]
        rw [hLHS, hS1, hS2, hB]
        ring
      rw [key, ih c, ih (c + 1)]
      -- Factorial algebra.
      have heq1 : (c + 1) + b + 1 = (c + b + 1) + 1 := by omega
      have heq2 : c + (b + 1) + 1 = (c + b + 1) + 1 := by omega
      rw [heq1, heq2, Nat.factorial_succ (c + b + 1), Nat.factorial_succ c, Nat.factorial_succ b]
      have hfac : ((c + b + 1).factorial : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos (c + b + 1)).ne'
      have hden : ((c : ℚ) + b + 2) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-! ## The budget-moment `budget_moment` (Crux 3) -/

/-- **W2-1 (P3.a) — the φ-moment with a normalized budget factor.**
Binomially expand `((log z − log r)/log R)^b`, feed each slice to `moment_atom`
(at `a = c+k`), collapse the leading coefficients with `beta_sum`.  The main
term is exactly `(φW'/W')·log R·β·(log z/log R)^{c+b+1}` with
`β = c!·b!/(c+b+1)!`, and the error is ABSOLUTE in `z` (constant, not scaled by
`log z`) — this uses `z ≤ R` crucially. -/
theorem budget_moment (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (c b : ℕ) :
    ∃ Catom : ℝ, 0 ≤ Catom ∧ ∀ z R : ℕ, 2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      |(∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
            (Real.log r / Real.log R) ^ c * ((Real.log z - Real.log r) / Real.log R) ^ b
              / (Nat.totient r : ℝ))
        - (Nat.totient W' / W' : ℝ) * Real.log R
            * ((c.factorial * b.factorial : ℝ) / (c + b + 1).factorial)
            * (Real.log z / Real.log R) ^ (c + b + 1)|
      ≤ Catom * 4 ^ (b + c) := by
  classical
  -- Per-slice atom constants `Cf k` for `a = c + k`, `k ∈ {0,…,b}`.
  set Cf : ℕ → ℝ := fun k => (moment_atom W' hW' hpos (c + k) hUpper).choose with hCfdef
  have hCf0 : ∀ k, 0 ≤ Cf k := fun k => (moment_atom W' hW' hpos (c + k) hUpper).choose_spec.1
  set Catom : ℝ := ∑ k ∈ Finset.range (b + 1), Cf k with hCatomdef
  have hCatom0 : 0 ≤ Catom := Finset.sum_nonneg (fun i _ => hCf0 i)
  refine ⟨Catom, hCatom0, ?_⟩
  intro z R hz hzR hR
  -- Basic log facts.
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hz0 : (0 : ℝ) < (z : ℝ) := by linarith
  have hLpos : (0 : ℝ) < Real.log (R : ℝ) := lt_of_lt_of_le zero_lt_one hR
  have hZnn : (0 : ℝ) ≤ Real.log (z : ℝ) := Real.log_nonneg hz1
  have hZL : Real.log (z : ℝ) ≤ Real.log (R : ℝ) :=
    Real.log_le_log hz0 (by exact_mod_cast hzR)
  set Z : ℝ := Real.log (z : ℝ) with hZdef
  set L : ℝ := Real.log (R : ℝ) with hLdef
  set M : ℝ := (Nat.totient W' : ℝ) / (W' : ℝ) with hMdef
  set A : ℕ → ℝ := fun a => ∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
      Real.log (r : ℝ) ^ a / (Nat.totient r : ℝ) with hAdef
  set P : ℕ → ℝ := fun k => M * Z ^ (c + k + 1) / (↑(c + k) + 1) with hPdef
  set Ck : ℕ → ℝ := fun k => (-1) ^ k * ((b.choose k : ℝ) * Z ^ (b - k) / L ^ (c + b)) with hCkdef
  -- The per-slice moment estimate.
  have hAspec : ∀ k, |A (c + k) - P k| ≤ Cf k * (1 + Z) ^ (c + k) := by
    intro k
    exact (moment_atom W' hW' hpos (c + k) hUpper).choose_spec.2 z hz
  -- Step 1: per-`r` binomial expansion.
  have hterm : ∀ r : ℕ,
      (Real.log (r : ℝ) / L) ^ c * ((Z - Real.log (r : ℝ)) / L) ^ b / (Nat.totient r : ℝ)
        = ∑ k ∈ Finset.range (b + 1),
            Ck k * (Real.log (r : ℝ) ^ (c + k) / (Nat.totient r : ℝ)) := by
    intro r
    rw [div_pow, div_pow, show Z - Real.log (r : ℝ) = -(Real.log (r : ℝ)) + Z from by ring,
      add_pow, Finset.sum_div, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hCkdef]
    rw [neg_pow]
    ring
  -- Step 2: swap and factor into the atoms.
  have hTeq :
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log (r : ℝ) / L) ^ c * ((Z - Real.log (r : ℝ)) / L) ^ b / (Nat.totient r : ℝ))
        = ∑ k ∈ Finset.range (b + 1), Ck k * A (c + k) := by
    rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.mul_sum]
  -- Step 3: the main term collapses to the budget factor `β` via `beta_sum`.
  have hbeta : (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * (-1) ^ k / ((c : ℝ) + k + 1))
      = (c.factorial * b.factorial : ℝ) / (c + b + 1).factorial := by
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) (beta_sum c b)
    push_cast at hcast
    exact hcast
  have hmain : (∑ k ∈ Finset.range (b + 1), Ck k * P k)
      = M * L * ((c.factorial * b.factorial : ℝ) / (c + b + 1).factorial)
          * (Z / L) ^ (c + b + 1) := by
    have hfac : (∑ k ∈ Finset.range (b + 1), Ck k * P k)
        = M * Z ^ (c + b + 1) / L ^ (c + b)
            * ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * (-1) ^ k / ((c : ℝ) + k + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkb : k ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [hCkdef, hPdef]
      have hZk : Z ^ (b - k) * Z ^ (c + k + 1) = Z ^ (c + b + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [← hZk]
      push_cast
      ring
    rw [hfac, hbeta, div_pow]
    have hLne : L ≠ 0 := ne_of_gt hLpos
    have hfacR : ((c + b + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos (c + b + 1)).ne'
    field_simp
    ring
  -- Step 4: rewrite the goal to the error sum.
  rw [hTeq, ← hmain, ← Finset.sum_sub_distrib]
  -- Per-slice error bound.
  have herr : ∀ k ∈ Finset.range (b + 1),
      |Ck k * A (c + k) - Ck k * P k| ≤ Catom * (b.choose k : ℝ) * 2 ^ (c + b) := by
    intro k hk
    have hkb : k ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hnn : (0 : ℝ) ≤ (b.choose k : ℝ) * Z ^ (b - k) / L ^ (c + b) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hZnn _)) (pow_nonneg hLpos.le _)
    have hCkabs : |Ck k| = (b.choose k : ℝ) * Z ^ (b - k) / L ^ (c + b) := by
      simp only [hCkdef, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact abs_of_nonneg hnn
    -- geometric term bound (uses `z ≤ R`): `Z^{b-k}(1+Z)^{c+k}/L^{c+b} ≤ 2^{c+b}`
    have hpk : Z ^ (b - k) * (1 + Z) ^ (c + k) / L ^ (c + b) ≤ 2 ^ (c + b) := by
      have hsplit : L ^ (c + b) = L ^ (b - k) * L ^ (c + k) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit, mul_div_mul_comm, ← div_pow, ← div_pow]
      have h1 : (Z / L) ^ (b - k) ≤ 1 :=
        pow_le_one₀ (div_nonneg hZnn hLpos.le) ((div_le_one hLpos).mpr hZL)
      have h1Znn : (0 : ℝ) ≤ (1 + Z) / L :=
        div_nonneg (by linarith [hZnn]) hLpos.le
      have h2 : ((1 + Z) / L) ^ (c + k) ≤ 2 ^ (c + b) := by
        calc ((1 + Z) / L) ^ (c + k) ≤ (2 : ℝ) ^ (c + k) := by
              apply pow_le_pow_left₀ h1Znn
              rw [div_le_iff₀ hLpos]; linarith
          _ ≤ 2 ^ (c + b) := pow_le_pow_right₀ (by norm_num) (by omega)
      calc (Z / L) ^ (b - k) * ((1 + Z) / L) ^ (c + k)
          ≤ 1 * ((1 + Z) / L) ^ (c + k) :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg h1Znn _)
        _ = ((1 + Z) / L) ^ (c + k) := one_mul _
        _ ≤ 2 ^ (c + b) := h2
    have hCfle : Cf k ≤ Catom := Finset.single_le_sum (fun i _ => hCf0 i) hk
    have hbc0 : (0 : ℝ) ≤ (b.choose k : ℝ) := Nat.cast_nonneg _
    calc |Ck k * A (c + k) - Ck k * P k|
        = |Ck k| * |A (c + k) - P k| := by rw [← mul_sub, abs_mul]
      _ = (b.choose k : ℝ) * Z ^ (b - k) / L ^ (c + b) * |A (c + k) - P k| := by rw [hCkabs]
      _ ≤ (b.choose k : ℝ) * Z ^ (b - k) / L ^ (c + b) * (Cf k * (1 + Z) ^ (c + k)) :=
            mul_le_mul_of_nonneg_left (hAspec k) hnn
      _ = (b.choose k : ℝ) * Cf k * (Z ^ (b - k) * (1 + Z) ^ (c + k) / L ^ (c + b)) := by ring
      _ ≤ (b.choose k : ℝ) * Cf k * 2 ^ (c + b) :=
            mul_le_mul_of_nonneg_left hpk (mul_nonneg hbc0 (hCf0 k))
      _ ≤ (b.choose k : ℝ) * Catom * 2 ^ (c + b) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hCfle hbc0) (by positivity)
      _ = Catom * (b.choose k : ℝ) * 2 ^ (c + b) := by ring
  -- Sum the per-slice bounds.
  have hchoose : (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)) = (2 : ℝ) ^ b := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
  calc |∑ k ∈ Finset.range (b + 1), (Ck k * A (c + k) - Ck k * P k)|
      ≤ ∑ k ∈ Finset.range (b + 1), |Ck k * A (c + k) - Ck k * P k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (b + 1), Catom * (b.choose k : ℝ) * 2 ^ (c + b) :=
        Finset.sum_le_sum herr
    _ = Catom * 2 ^ (c + b) * ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ = Catom * 2 ^ (c + b) * 2 ^ b := by rw [hchoose]
    _ ≤ Catom * 4 ^ (b + c) := by
        have h4 : (4 : ℝ) ^ (b + c) = 2 ^ (2 * (b + c)) := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        have h2 : (2 : ℝ) ^ (c + b) * 2 ^ b = 2 ^ (c + b + b) := by rw [← pow_add]
        rw [mul_assoc, h2, h4]
        apply mul_le_mul_of_nonneg_left _ hCatom0
        exact pow_le_pow_right₀ (by norm_num) (by omega)

/-! ## PORT-BLOCKER — `budget_moment_g` (the g-sandwich, Crux 2)

The `g`-weighted two-sided analogue of `budget_moment`, with `Nat.totient r`
replaced by `Salt.Maynard.gMult r = ∏_{p ∣ r} (p − 2)` in the denominators and
an added primes-exceed-`D` hypothesis
`hD : ∀ p, p.Prime → ¬ p ∣ W' → D ≤ p` for some `D ≥ 2`.  Intended statement
shape (NOT frozen; the `D`-dependence of the correction constant is a design
choice):

    theorem budget_moment_g (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
        (hUpper : PhiUpperAtom W') (D : ℕ) (hD2 : 2 ≤ D)
        (hD : ∀ p, p.Prime → ¬ p ∣ W' → D ≤ p) (c b : ℕ) :
        ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ z R : ℕ, 2 ≤ z → z ≤ R → 1 ≤ Real.log R →
          |(∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
                (Real.log r / Real.log R) ^ c
                  * ((Real.log z - Real.log r) / Real.log R) ^ b
                  / (Salt.Maynard.gMult r : ℝ))
            - (Nat.totient W' / W' : ℝ) * Real.log R
                * ((c.factorial * b.factorial : ℝ) / (c + b + 1).factorial)
                * (Real.log z / Real.log R) ^ (c + b + 1)|
          ≤ Cg * 4 ^ (b + c)   -- error absorbs an extra `O(1/D)` correction

Route (as in the card):

* LOWER (free): `gMult r ≤ φ(r)` termwise (per prime `p − 2 ≤ p − 1`), so
  `1/gMult r ≥ 1/φ(r)`, giving `moment_g ≥ moment_φ`.  The landed comparison
  `Salt.Maynard.gMult_le_totient` supplies the per-`r` inequality (it needs
  every prime factor `≥ 3`, which follows from `hD` once `D ≥ 3`; for `D = 2`
  the even-`r` terms have `gMult r = 0` and drop out, so the coprimality
  restriction to `W'` — a primorial through `D` in the intended use — is
  load-bearing, not cosmetic).

* UPPER (the work): `1/gMult r = (1/φ(r))·∏_{p ∣ r} (1 + 1/(p−2))`.  Expand
  `∏_{p ∣ r} (1 + 1/(p−2)) = ∑_{S ⊆ r.primeFactors} ∏_{p ∈ S} 1/(p−2)`
  (`Finset.prod_add` with `f p = 1/(p−2)`, `g p = 1`), split off `S = ∅` (the
  `moment_φ` main term) and bound the `S ≠ ∅` tail.  For each nonempty `S` with
  `s = ∏_{p ∈ S} p`, one reindexes `r = s · t` (`φ` and `gMult` multiplicative
  on the coprime factorization, `Nat.totient_mul`) and sums geometrically:
  `∑_{p > D} 1/((p−1)(p−2)) ≤ 2/D`, hence
  `∑_{S ≠ ∅} ∏_{p ∈ S} 1/(p−2) ≤ exp(2/D) − 1 ≤ 4/D` for `D ≥ 2`, so
  `moment_g − moment_φ ≤ (4·c_up/D)·log z`, absorbed into `Cg`.

WHY BLOCKED HERE (the missing atom): the per-subset reindex needs, for each
`S ⊆ r.primeFactors` with `|S| ≥ 2`, the sub-sum of the moment atom over `r`
divisible by the COMPOSITE `s = ∏_{p ∈ S} p` — a multi-prime marked sum.  The
landed engine `marked_prime_phi` (card W2-2) is SINGLE-prime only
(`p ∣ r`), and its `g`-analogue `marked_prime_g` is itself PORT-BLOCKERed in
`Salt/Twelve/MarkedPrime.lean`.  A composite/multi-prime marked-sum atom (or an
inductive reindex over `s = ∏ S` with `φ`/`gMult` multiplicativity threaded
through the whole squarefree `s`, plus the geometric tail
`∑_{q > D} 1/((q−1)(q−2)) ≤ 2/D` as a convergent Euler-tail estimate) is a
prerequisite that does not exist in `Salt/`.  Building it is a wave-2 spine
concern (mirroring `Salt/Maynard/EulerTailL.lean`'s tail machinery), not a
clean assembly on the currently landed atoms.  The `φ`-version `budget_moment`
above is the must-have and lands unconditionally; `budget_moment_g` follows
once the composite marked-sum atom is available. -/

end Salt.Twelve
