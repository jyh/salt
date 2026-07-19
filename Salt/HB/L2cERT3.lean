/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cER

/-!
# HB-L2c — the `E_R` T3′ family budget (node HB-L2c-M-T3, the mirror campaign)

Single writer of the **`E_R` T3-analogue family budget** `ER_T3'_bound` — the `J2`
`PretenseSum` row of the right-overshoot family analysis (freeze §S4 `E_R` mirror; target
shape verbatim from `Salt.HB.L2cER` §5 NOTES; house amendments of catch #245 folded in:
the inline junk-block guard and the `Zz`-sift-floor correction).

The T3′ family collects the window elements `n` with

* `n` **prime** (the `E_R` left weight is the clean `Λ(n) = log n ≤ L'`),
* `(n+2)₊ =: U` **prime** (the `χ=+1` all-plus part of the shifted partner),
* `w := (n+2)₋ ≥ z` a prime power (the single `χ=−1` block), and
* `w` **not a junk block** (`ERT3'JunkBlock`): small-base (`≤ Zz`) proper prime powers
  above the `z^{1/4}` routing line are excluded — they defeat the `Zz`-sift and belong
  to the junk row `ER_wJunk_bound` (house amendment 1).

**The route** (why this closes with no weighted fibration, unlike `E_L`'s T3): the
`n`-side is a SINGLE prime, so both weight factors are crude-capped by constants —
`Λ(n) ≤ L'` and `(Λ̃−Λ)(n+2) ≤ Λ̃(n+2) ≤ e^{(log2)z₀}·L'` — and the family sub-sum
reduces to `e^{(log2)z₀}·L'²·|T3′|`.  The count `|T3′|` is fibred over the moduli
`d₂ := U` (`d₁ := 1`) and priced by `l2c_pair_count_clean` at the sieve floor
`Zz = ⌊z^{1/16}⌋` (house amendment 3: both sifted cofactors — the prime `n > x ≥ z` and
the guarded block `w` — are provably coprime to `primorial (Zz z)`).  The count's
`1/(log Zz)²` saving converts `L'²` into `z₀²`-grade constants, `Σ_U 1/U ≤ PS/(log z)`
supplies the `PretenseSum` factor, and the `Aexp = 5` budget absorbs
`z₀³·e^{(log2)z₀} ≤ e^{5z₀}`.  Frozen conclusion, with the explicit absolute constant
`Cmain = 524288 = 2^19`:

`ER_T3' χ z x ≤ 524288·(x / Lwin x)·exp(5·z₀ z x)·PretenseSum χ (2x+2)`  (the `J2` row).

Single-writer file (`L2cERT3.lean`); imports the frozen surfaces `Salt.HB.L2cER` /
`Salt.HB.L2cCore`; touches no other file (`Salt.HB.All` is Wave 3's manifest).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §0 — the T3′ family predicate, its junk-block guard, and the family sub-sum -/

/-- **The T3′ junk-block guard** (house amendment 1, catch #245).  `w` is a *junk block*
    when it is a small-base proper prime power above the `z^{1/4}` routing line:
    `w = p^e` with `p ≤ Zz z` prime, `e ≥ 2`, and `z^{1/4} < w`.  Junk blocks defeat the
    `Zz`-sift (their base prime is inside the sieve) and are owned by the junk row
    `ER_wJunk_bound`, not the `J2` budget.  Family-prefixed local predicate (the
    single-writer law extends to names; W3 reconciles via iff-lemmas). -/
def ERT3'JunkBlock (z w : ℕ) : Prop :=
  ∃ p e : ℕ, p.Prime ∧ p ≤ Zz z ∧ 2 ≤ e ∧ w = p ^ e ∧ (z : ℝ) ^ ((1 : ℝ) / 4) < (w : ℝ)

/-- **The `E_R` T3′ family predicate** (freeze §S4, roles swapped; L2cER §5 NOTES):
    `n` prime, the shifted partner `n+2` single-block with prime all-plus part
    `U := (n+2)₊` and `χ=−1` block `w := (n+2)₋ ≥ z`, guarded against junk blocks. -/
def IsERT3' (χ : DirichletCharacter ℂ q) (z n : ℕ) : Prop :=
  n.Prime ∧ (nPlus χ (n + 2)).Prime ∧ IsPrimePow (nMinus χ (n + 2)) ∧
    z ≤ nMinus χ (n + 2) ∧ ¬ ERT3'JunkBlock z (nMinus χ (n + 2))

open Classical in
/-- **The `E_R` T3′ family sub-sum.**  The slice of
    `E_R = Σ_{n∈W} Λ(n)·(Λ̃−Λ)(n+2)` on the T3′ support — the object this file prices
    to the frozen `J2` row. -/
noncomputable def ER_T3' (χ : DirichletCharacter ℂ q) (z x : ℕ) : ℝ :=
  ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsERT3' χ z n),
    Λ n * (LamTilde χ (n + 2) - Λ (n + 2))

/-! ## §1 — scale lemmas for the `Zz` sieve floor

The legality and endgame arithmetic need four honest scale facts at `z ≥ 100^16`:
`Zz⁸ ≤ √z`, `log Zz ≤ log z`, `log Zz ≥ (log z)/32`, and `(log z)² ≤ 8·√z`. -/

/-- `z ≤ x` from the master hypothesis `z³ ≤ x`. -/
lemma ERT3'_z_le_x {z x : ℕ} (hz1 : 1 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) : z ≤ x := by
  have h1 : (1 : ℝ) ≤ z := by exact_mod_cast hz1
  have h2 : (z : ℝ) ≤ (z : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0:ℝ) ≤ (z:ℝ)))
      (by linarith : (0:ℝ) ≤ (z:ℝ) + 1)]
  exact_mod_cast h2.trans hzx

/-- The sieve floor sits strictly below the roughness floor: `Zz z < z`. -/
lemma ERT3'_Zz_lt_z {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : Zz z < z := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz1R : (1 : ℝ) < z := by exact_mod_cast (by omega : 1 < z)
  have hfl : ((Zz z : ℕ) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := by
    rw [Zz]; exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hlt : (z : ℝ) ^ ((1 : ℝ) / 16) < (z : ℝ) := by
    calc (z : ℝ) ^ ((1 : ℝ) / 16) < (z : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt hz1R (by norm_num)
      _ = (z : ℝ) := Real.rpow_one _
  exact_mod_cast hfl.trans_lt hlt

/-- `Zz⁸ ≤ z^{1/2}` — the sieve-floor eighth power stays under `√z`. -/
lemma ERT3'_Zz_pow8_le (z : ℕ) :
    ((Zz z : ℕ) : ℝ) ^ 8 ≤ (z : ℝ) ^ ((1 : ℝ) / 2) := by
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have hfl : ((Zz z : ℕ) : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 16) := by
    rw [Zz]; exact Nat.floor_le (Real.rpow_nonneg hz0 _)
  calc ((Zz z : ℕ) : ℝ) ^ 8 ≤ ((z : ℝ) ^ ((1 : ℝ) / 16)) ^ 8 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hfl 8
    _ = (z : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 16)) 8, ← Real.rpow_mul hz0]
        norm_num

/-- `log Zz ≤ log z`. -/
lemma ERT3'_log_Zz_le {z : ℕ} (hz100 : 100 ^ 16 ≤ z) : Real.log (Zz z) ≤ Real.log z := by
  have hZ100 : 100 ≤ Zz z := Zz_ge_100 hz100
  have hlt := ERT3'_Zz_lt_z hz100
  exact Real.log_le_log (by exact_mod_cast (by omega : 0 < Zz z))
    (by exact_mod_cast hlt.le)

/-- **The floor-log lower bound** `log Zz ≥ (log z)/32`: from `z^{1/16} < 2·Zz` and
    `log 2 ≤ (log z)/32` (as `z ≥ 2^32`). -/
lemma ERT3'_log_Zz_ge {z : ℕ} (hz100 : 100 ^ 16 ≤ z) :
    Real.log z / 32 ≤ Real.log (Zz z) := by
  have hZ100 : 100 ≤ Zz z := Zz_ge_100 hz100
  have hz0R : (0 : ℝ) < z := by
    have h1 : 1 ≤ z := le_trans (by norm_num) hz100
    exact_mod_cast (by omega : 0 < z)
  have hZzR : (1 : ℝ) ≤ (Zz z : ℝ) := by exact_mod_cast (by omega : 1 ≤ Zz z)
  have hfl : (z : ℝ) ^ ((1 : ℝ) / 16) < 2 * (Zz z : ℝ) := by
    have h1 : (z : ℝ) ^ ((1 : ℝ) / 16) < (Zz z : ℝ) + 1 := by
      rw [Zz]; exact Nat.lt_floor_add_one _
    linarith
  have hlog1 : 1 / 16 * Real.log z ≤ Real.log (2 * (Zz z : ℝ)) := by
    rw [← Real.log_rpow hz0R]
    exact Real.log_le_log (Real.rpow_pos_of_pos hz0R _) hfl.le
  have hlog2 : Real.log (2 * (Zz z : ℝ)) = Real.log 2 + Real.log (Zz z) :=
    Real.log_mul (by norm_num) (by linarith)
  have h232 : (2 : ℝ) ^ (32 : ℕ) ≤ (z : ℝ) := by
    have hn : (2 : ℕ) ^ 32 ≤ z := le_trans (by norm_num) hz100
    exact_mod_cast hn
  have hlog3 : Real.log 2 ≤ Real.log z / 32 := by
    have h := Real.log_le_log (by positivity) h232
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  rw [hlog2] at hlog1
  linarith

/-- **The legality scale bound** `(log z)² ≤ 8·z^{1/2}` at `z ≥ 100^16` (via
    `log z ≤ 8·z^{1/8}` and `8 ≤ z^{1/4}`). -/
lemma ERT3'_logsq_le {z : ℕ} (hz100 : 100 ^ 16 ≤ z) :
    Real.log z ^ 2 ≤ 8 * (z : ℝ) ^ ((1 : ℝ) / 2) := by
  have hz0R : (0 : ℝ) < z := by
    have h1 : 1 ≤ z := le_trans (by norm_num) hz100
    exact_mod_cast (by omega : 0 < z)
  have hz1R : (1 : ℝ) ≤ z := by
    have h1 : 1 ≤ z := le_trans (by norm_num) hz100
    exact_mod_cast h1
  have hlz : 0 ≤ Real.log z := Real.log_nonneg hz1R
  have hkey : Real.log z ≤ 8 * (z : ℝ) ^ ((1 : ℝ) / 8) := by
    have hself : Real.log ((z : ℝ) ^ ((1 : ℝ) / 8)) ≤ (z : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.log_le_self (Real.rpow_nonneg hz0R.le _)
    rw [Real.log_rpow hz0R] at hself
    linarith
  have hsq : Real.log z ^ 2 ≤ (8 * (z : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 :=
    pow_le_pow_left₀ hlz hkey 2
  have hr2 : ((z : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 = (z : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 8)) 2, ← Real.rpow_mul hz0R.le]
    norm_num
  have h84 : (8 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by
    have h100 : (100 : ℝ) ^ (16 : ℕ) ≤ (z : ℝ) := by exact_mod_cast hz100
    have hmono : ((100 : ℝ) ^ (16 : ℕ)) ^ ((1 : ℝ) / 4) ≤ (z : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) h100 (by norm_num)
    calc (8 : ℝ) ≤ (100 : ℝ) ^ (4 : ℕ) := by norm_num
      _ = ((100 : ℝ) ^ (16 : ℕ)) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast (100 : ℝ) 16,
            ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 100), ← Real.rpow_natCast (100 : ℝ) 4]
          norm_num
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := hmono
  have hquarter : (z : ℝ) ^ ((1 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 4)
      = (z : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hz0R]; norm_num
  calc Real.log z ^ 2 ≤ (8 * (z : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 := hsq
    _ = 64 * ((z : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 := by ring
    _ = 64 * (z : ℝ) ^ ((1 : ℝ) / 4) := by rw [hr2]
    _ ≤ 8 * ((z : ℝ) ^ ((1 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 4)) := by
        nlinarith [h84, sq_nonneg ((z : ℝ) ^ ((1 : ℝ) / 4) - 8)]
    _ = 8 * (z : ℝ) ^ ((1 : ℝ) / 2) := by rw [hquarter]

/-! ## §2 — sift-floor soundness: both cofactors are coprime to `primorial (Zz z)`

House amendment 3 (catch #245): the sifted cofactors here are only guaranteed `≥ z`
(the block `w`) resp. `> x` (the prime `n`), so the sift runs at `Zz = ⌊z^{1/16}⌋ < z`,
never at `Zf`.  Soundness is *proven*, not assumed: a prime above `Zz` is coprime to
`primorial (Zz z)`, and the junk-block guard forces the block's base prime above `Zz`. -/

/-- A prime strictly above `Z` is coprime to `primorial Z`. -/
lemma ERT3'_coprime_primorial {Z p : ℕ} (hp : p.Prime) (hZp : Z < p) :
    Nat.Coprime (primorial Z) p :=
  (hp.coprime_iff_not_dvd.mpr fun hd => absurd (hp.dvd_primorial_iff.mp hd)
    (by omega)).symm

/-- **Sift-floor soundness for the block.**  A non-junk prime-power block `w ≥ z` has its
    base prime above `Zz` (either `w` is itself a prime `≥ z > Zz`, or `e ≥ 2` and the
    junk guard forces the base above `Zz`), hence `w` is coprime to `primorial (Zz z)`. -/
lemma ERT3'_block_coprime {z w : ℕ} (hz100 : 100 ^ 16 ≤ z) (hpp : IsPrimePow w)
    (hzw : z ≤ w) (hguard : ¬ ERT3'JunkBlock z w) :
    Nat.Coprime (primorial (Zz z)) w := by
  obtain ⟨r, e, hr, he, hre⟩ := hpp
  have hrN : r.Prime := Nat.prime_iff.mpr hr
  have hZr : Zz z < r := by
    rcases Nat.lt_or_ge (Zz z) r with hgt | hle
    · exact hgt
    exfalso
    rcases (by omega : e = 1 ∨ 2 ≤ e) with he1 | he2
    · -- `w = r ≤ Zz < z` contradicts `z ≤ w`
      have hwr : w = r := by rw [← hre, he1, pow_one]
      have hZzlt := ERT3'_Zz_lt_z hz100
      omega
    · -- `w` would be a junk block, contradicting the guard
      refine hguard ⟨r, e, hrN, hle, he2, hre.symm, ?_⟩
      have hz1R : (1 : ℝ) < z := by
        have h2 : 2 ≤ z := le_trans (by norm_num) hz100
        exact_mod_cast (by omega : 1 < z)
      calc (z : ℝ) ^ ((1 : ℝ) / 4) < (z : ℝ) ^ (1 : ℝ) :=
            Real.rpow_lt_rpow_of_exponent_lt hz1R (by norm_num)
        _ = (z : ℝ) := Real.rpow_one _
        _ ≤ (w : ℝ) := by exact_mod_cast hzw
  have hcop := (ERT3'_coprime_primorial hrN hZr).pow_right e
  rwa [hre] at hcop

/-! ## §3 — the crude per-term cap and the `U`-modulus facts -/

/-- **The crude per-term cap** `Λ(n)·(Λ̃−Λ)(n+2) ≤ e^{(log2)z₀}·L'²` on any window
    element (the T3′ mirror of the `ER_squarefull_junk` term cap: the left factor is
    `≤ L'`, the right difference is `≤ Λ̃(n+2) ≤ e^{(log2)z₀}·L'`). -/
lemma ERT3'_term_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hz2 : 2 ≤ z) (hn : n ∈ l2cWindow χ z x) :
    Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2 := by
  have hΛn_le : Λ n ≤ Lwin x := l2cWindow_vonMangoldt_cap χ hn
  have hcap := l2cWindow_lamTilde_np2_cap χ hsq hz2 hn
  calc Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
      ≤ Λ n * LamTilde χ (n + 2) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ vonMangoldt_nonneg) vonMangoldt_nonneg
    _ ≤ Lwin x * (Real.exp (Real.log 2 * z0 z x) * Lwin x) :=
        mul_le_mul hΛn_le hcap (LamTilde_nonneg χ hsq (n + 2)) (Lwin_nonneg x)
    _ = Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2 := by ring

/-- **The `U`-modulus facts** on a T3′ window element: `U := (n+2)₊` is a `χ=+1` prime
    `≥ z` (window roughness), it splits `n+2 = U·w`, and `U·z ≤ 2x+2` (the block `w ≥ z`
    caps the modulus — the freeze's `d₂ = U ≤ (2x+2)/z` law). -/
lemma ERT3'_U_facts (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x n : ℕ}
    (hnw : n ∈ l2cWindow χ z x) (hfam : IsERT3' χ z n) :
    chiRe χ (nPlus χ (n + 2)) = 1 ∧ z ≤ nPlus χ (n + 2) ∧
      n + 2 = nPlus χ (n + 2) * nMinus χ (n + 2) ∧ nPlus χ (n + 2) * z ≤ 2 * x + 2 := by
  obtain ⟨hnp, hUp, hwpp, hwz, hguard⟩ := hfam
  have hmem := (l2cWindow_mem_iff χ z x n).mp hnw
  have hcop2 : Nat.Coprime (n + 2) q := l2cWindow_np2_coprime_q χ hnw
  have hsplit : n + 2 = nPlus χ (n + 2) * nMinus χ (n + 2) :=
    eq_nPlus_mul_nMinus χ hsq (by omega) hcop2
  have hchi : chiRe χ (nPlus χ (n + 2)) = 1 :=
    nPlus_sign (Nat.mem_primeFactors.mpr ⟨hUp, dvd_rfl, hUp.pos.ne'⟩)
  have hUdvd : nPlus χ (n + 2) ∣ n + 2 := ⟨nMinus χ (n + 2), hsplit⟩
  have hUz : z ≤ nPlus χ (n + 2) := by
    refine l2cWindow_roughness χ z x hnw hUp (hUdvd.mul_left n) ?_
    rw [hchi]; norm_num
  refine ⟨hchi, hUz, hsplit, ?_⟩
  calc nPlus χ (n + 2) * z ≤ nPlus χ (n + 2) * nMinus χ (n + 2) :=
        Nat.mul_le_mul_left _ hwz
    _ = n + 2 := hsplit.symm
    _ ≤ 2 * x + 2 := by omega

/-! ## §4 — the fiber inclusion into the sifted pair-count set -/

open Classical in
/-- **The fiber inclusion.**  The T3′ fiber at modulus `U` sits inside the `Zz`-sifted
    pair-count set at `(d₁, d₂) = (1, U)`: the cofactors are `n/1 = n` (a prime
    `> x ≥ z > Zz`) and `(n+2)/U = w` (the guarded block), both coprime to
    `primorial (Zz z)` by §2. -/
lemma ERT3'_fiber_subset (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) (U : ℕ) :
    ((l2cWindow χ z x).filter (fun n => IsERT3' χ z n)).filter
        (fun n => nPlus χ (n + 2) = U)
      ⊆ (baseSet x 1 U).filter
          (fun n => Nat.Coprime (primorial (Zz z)) (n / 1 * ((n + 2) / U))) := by
  intro n hn
  simp only [Finset.mem_filter] at hn
  obtain ⟨⟨hnw, hfam⟩, hfU⟩ := hn
  obtain ⟨-, -, hsplit, -⟩ := ERT3'_U_facts χ hsq hnw hfam
  obtain ⟨hnp, hUp, hwpp, hwz, hguard⟩ := hfam
  have hmem := (l2cWindow_mem_iff χ z x n).mp hnw
  have hU0 : 0 < U := hfU ▸ nPlus_pos χ (n + 2)
  rw [hfU] at hsplit
  have hdiv : (n + 2) / U = nMinus χ (n + 2) :=
    Nat.div_eq_of_eq_mul_right hU0 hsplit
  have hzx' : z ≤ x := ERT3'_z_le_x (le_trans (by norm_num) hz100) hzx
  have hZn : Zz z < n := by
    have h1 := ERT3'_Zz_lt_z hz100
    omega
  have hcopn : Nat.Coprime (primorial (Zz z)) n := ERT3'_coprime_primorial hnp hZn
  have hcopw : Nat.Coprime (primorial (Zz z)) (nMinus χ (n + 2)) :=
    ERT3'_block_coprime hz100 hwpp hwz hguard
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · simp only [baseSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hmem.1.1, hmem.1.2⟩, one_dvd n, ⟨nMinus χ (n + 2), hsplit⟩⟩
  · rw [Nat.div_one, hdiv]
    exact hcopn.mul_right hcopw

/-! ## §5 — the per-fiber count and the fibred count assembly -/

open Classical in
/-- **The per-fiber count.**  At a prime modulus `U ≥ z` with `U·z ≤ 2x+2`, the T3′
    fiber obeys `≤ 512·x/(log Zz)²·(1/U)`: `l2c_pair_count_clean` at `(d₁,d₂) = (1,U)`
    with sieve floor `Zz` (legality `U·Zz⁸·(log Zz)² ≤ 8·U·z ≤ 32x` by §1) and the prime
    totient ratio `(U/φ(U))² ≤ 4`. -/
lemma ERT3'_fiber_card_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) {U : ℕ} (hUp : U.Prime)
    (hUz : z ≤ U) (hUx : U * z ≤ 2 * x + 2) :
    ((((l2cWindow χ z x).filter (fun n => IsERT3' χ z n)).filter
        (fun n => nPlus χ (n + 2) = U)).card : ℝ)
      ≤ 512 * (x : ℝ) / Real.log (Zz z) ^ 2 * ((1 : ℝ) / U) := by
  have h3z : 3 ≤ z := le_trans (by norm_num) hz100
  have hz0R : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hx1 : (1 : ℝ) ≤ x := by
    have h1 : (1 : ℝ) ≤ (z : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ z))
    linarith [hzx]
  have hUzR : (U : ℝ) * z ≤ 2 * x + 2 := by exact_mod_cast hUx
  have hU2 : U ≠ 2 := by omega
  have hlogZz0 : 0 ≤ Real.log (Zz z) := by
    have h100 : 100 ≤ Zz z := Zz_ge_100 hz100
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Zz z))
  have hlogZzsq : Real.log (Zz z) ^ 2 ≤ 8 * (z : ℝ) ^ ((1 : ℝ) / 2) :=
    le_trans (pow_le_pow_left₀ hlogZz0 (ERT3'_log_Zz_le hz100) 2) (ERT3'_logsq_le hz100)
  have hs : (z : ℝ) ^ ((1 : ℝ) / 2) * (z : ℝ) ^ ((1 : ℝ) / 2) = (z : ℝ) := by
    rw [← Real.rpow_add hz0R]; norm_num
  have hleg : ((1 : ℕ) : ℝ) * (U : ℝ) * ((Zz z : ℕ) : ℝ) ^ 8 * Real.log (Zz z) ^ 2
      ≤ 32 * (x : ℝ) := by
    rw [Nat.cast_one, one_mul]
    calc (U : ℝ) * ((Zz z : ℕ) : ℝ) ^ 8 * Real.log (Zz z) ^ 2
        ≤ (U : ℝ) * (z : ℝ) ^ ((1 : ℝ) / 2) * (8 * (z : ℝ) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (ERT3'_Zz_pow8_le z) (Nat.cast_nonneg U))
            hlogZzsq (sq_nonneg _) (by positivity)
      _ = 8 * ((z : ℝ) ^ ((1 : ℝ) / 2) * (z : ℝ) ^ ((1 : ℝ) / 2)) * U := by ring
      _ = 8 * ((U : ℝ) * z) := by rw [hs]; ring
      _ ≤ 8 * (2 * (x : ℝ) + 2) := by
          have h8 := mul_le_mul_of_nonneg_left hUzR (by norm_num : (0 : ℝ) ≤ 8)
          linarith
      _ ≤ 32 * (x : ℝ) := by linarith
  have hcount := l2c_pair_count_clean (x := x) (Zz_ge_100 hz100) one_pos hUp.pos odd_one
    (hUp.odd_of_ne_two hU2) (Nat.coprime_one_left U) hleg
  have hcard : ((((l2cWindow χ z x).filter (fun n => IsERT3' χ z n)).filter
      (fun n => nPlus χ (n + 2) = U)).card : ℝ)
      ≤ (((baseSet x 1 U).filter
          (fun n => Nat.Coprime (primorial (Zz z)) (n / 1 * ((n + 2) / U)))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (ERT3'_fiber_subset χ hsq hz100 hzx U)
  refine le_trans (le_trans hcard hcount) ?_
  simp only [Nat.cast_one, one_mul]
  rw [Nat.totient_prime hUp]
  have hU2R : (2 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hUp.two_le
  have hcast : ((U - 1 : ℕ) : ℝ) = (U : ℝ) - 1 := by
    rw [Nat.cast_sub hUp.one_le, Nat.cast_one]
  rw [hcast]
  have hratio : (U : ℝ) / ((U : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (U : ℝ) - 1)]
    linarith
  have hrat0 : 0 ≤ (U : ℝ) / ((U : ℝ) - 1) :=
    div_nonneg (by linarith) (by linarith)
  have hsq4 : ((U : ℝ) / ((U : ℝ) - 1)) ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ hrat0 hratio 2
    norm_num at h
    exact h
  have hxU : (0 : ℝ) ≤ (x : ℝ) / U := div_nonneg (Nat.cast_nonneg x) (Nat.cast_nonneg U)
  have hinv : (0 : ℝ) ≤ (Real.log (Zz z) ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  calc 128 * ((U : ℝ) / ((U : ℝ) - 1)) ^ 2 * ((x : ℝ) / U) / Real.log (Zz z) ^ 2
      = 128 * ((U : ℝ) / ((U : ℝ) - 1)) ^ 2
          * ((x : ℝ) / U * (Real.log (Zz z) ^ 2)⁻¹) := by ring
    _ ≤ 128 * 4 * ((x : ℝ) / U * (Real.log (Zz z) ^ 2)⁻¹) := by
        have hK : (0 : ℝ) ≤ (x : ℝ) / U * (Real.log (Zz z) ^ 2)⁻¹ := mul_nonneg hxU hinv
        have h128 : 128 * ((U : ℝ) / ((U : ℝ) - 1)) ^ 2 ≤ 128 * 4 := by linarith
        exact mul_le_mul_of_nonneg_right h128 hK
    _ = 512 * (x : ℝ) / Real.log (Zz z) ^ 2 * ((1 : ℝ) / U) := by ring

open Classical in
/-- **The fibred count.**  `|T3′| ≤ 512·x/(log Zz)²·(PS/(log z))`: fiber over the prime
    modulus `U = (n+2)₊`, price each fiber by `ERT3'_fiber_card_le`, and sum `1/U` over
    the distinct `χ=+1` primes `U ∈ [z, 2x+2]` via `sum_inv_plusprime_le_pretense`. -/
lemma ERT3'_card_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    (((l2cWindow χ z x).filter (fun n => IsERT3' χ z n)).card : ℝ)
      ≤ 512 * (x : ℝ) / Real.log (Zz z) ^ 2
          * (PretenseSum χ (2 * x + 2) / Real.log z) := by
  have hz1 : 1 < z := by
    have h2 : 2 ≤ z := le_trans (by norm_num) hz100
    omega
  set F := (l2cWindow χ z x).filter (fun n => IsERT3' χ z n) with hF
  set T := F.image (fun n => nPlus χ (n + 2)) with hT
  have hUfact : ∀ U ∈ T, U.Prime ∧ chiRe χ U = 1 ∧ z ≤ U ∧ U * z ≤ 2 * x + 2 := by
    intro U hU
    rw [hT, Finset.mem_image] at hU
    obtain ⟨n, hnF, hfU⟩ := hU
    rw [hF, Finset.mem_filter] at hnF
    obtain ⟨hnw, hfam⟩ := hnF
    obtain ⟨hchi, hUz, -, hUx⟩ := ERT3'_U_facts χ hsq hnw hfam
    exact hfU ▸ ⟨hfam.2.1, hchi, hUz, hUx⟩
  have hmaps : Set.MapsTo (fun n => nPlus χ (n + 2)) ↑F ↑T := by
    intro n hn
    exact Finset.mem_coe.mpr (hT ▸ Finset.mem_image_of_mem _ (Finset.mem_coe.mp hn))
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  calc (F.card : ℝ)
      = ∑ U ∈ T, ((F.filter (fun n => nPlus χ (n + 2) = U)).card : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ ∑ U ∈ T, 512 * (x : ℝ) / Real.log (Zz z) ^ 2 * ((1 : ℝ) / U) := by
        refine Finset.sum_le_sum fun U hU => ?_
        obtain ⟨hUp, -, hUz, hUx⟩ := hUfact U hU
        rw [hF]
        exact ERT3'_fiber_card_le χ hsq hz100 hzx hUp hUz hUx
    _ = 512 * (x : ℝ) / Real.log (Zz z) ^ 2 * ∑ U ∈ T, ((1 : ℝ) / U) := by
        rw [Finset.mul_sum]
    _ ≤ 512 * (x : ℝ) / Real.log (Zz z) ^ 2
          * (PretenseSum χ (2 * x + 2) / Real.log z) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans ?_ (sum_inv_plusprime_le_pretense χ z (2 * x + 2) hz1)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => by positivity
        intro U hU
        obtain ⟨hUp, hchi, hUz, hUx⟩ := hUfact U hU
        have hUle : U ≤ 2 * x + 2 := by
          calc U = U * 1 := (mul_one U).symm
            _ ≤ U * z := Nat.mul_le_mul_left U (by omega)
            _ ≤ 2 * x + 2 := hUx
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hUp, hchi, hUz⟩

/-! ## §6 — the endgame: the `Aexp = 5` budget and the frozen `J2` bound -/

/-- `PretenseSum χ N ≥ 0` (each term `log p / p ≥ 0`).  Family-prefixed copy (the
    single-writer law extends to names; W3 reconciles duplicates). -/
lemma ERT3'_PS_nonneg (χ : DirichletCharacter ℂ q) (N : ℕ) : 0 ≤ PretenseSum χ N := by
  rw [PretenseSum]
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)) (Nat.cast_nonneg p)

/-- **The `Aexp = 5` budget arithmetic** `z₀³·e^{(log2)z₀} ≤ e^{5z₀}` (from `z₀ ≤ e^{z₀}`
    cubed and `3 + log 2 ≤ 5`). -/
lemma ERT3'_z0cube_exp_le {z x : ℕ} (hz2 : 2 ≤ z) :
    z0 z x ^ 3 * Real.exp (Real.log 2 * z0 z x) ≤ Real.exp (5 * z0 z x) := by
  have hz0 : 0 ≤ z0 z x := z0_nonneg hz2
  have h1 : z0 z x ≤ Real.exp (z0 z x) := by
    have h := Real.add_one_le_exp (z0 z x)
    linarith
  have h3 : z0 z x ^ 3 ≤ Real.exp (3 * z0 z x) := by
    have hpow : Real.exp (z0 z x) ^ 3 = Real.exp (3 * z0 z x) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [← hpow]
    exact pow_le_pow_left₀ hz0 h1 3
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_two_lt_d9
    linarith
  calc z0 z x ^ 3 * Real.exp (Real.log 2 * z0 z x)
      ≤ Real.exp (3 * z0 z x) * Real.exp (Real.log 2 * z0 z x) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = Real.exp (3 * z0 z x + Real.log 2 * z0 z x) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (5 * z0 z x) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - Real.log 2) hz0]

open Classical in
/-- **THE T3′ FAMILY BUDGET (the frozen `J2` row).**  Under the master hypothesis packet,
    the `E_R` T3′ family sub-sum obeys

    `ER_T3' χ z x ≤ Cmain·(x / Lwin x)·exp(5·z₀ z x)·PretenseSum χ (2x+2)`

    with the explicit absolute constant `Cmain = 524288 = 2^19` (no dependence on `χ`,
    `z`, `x`).  Route: crude per-term cap `e^{(log2)z₀}·L'²` (§3), the `Zz`-sifted fibred
    count `≤ 512·x/(log Zz)²·(PS/log z)` (§5), the floor-log conversion
    `(log Zz)² ≥ (log z)²/1024` (§1), and the `Aexp = 5` budget `z₀³·e^{(log2)z₀} ≤ e^{5z₀}`. -/
theorem ER_T3'_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz100 : 100 ^ 16 ≤ z) (_hz8 : Lwin x ^ 8 ≤ z) (hzx : (z : ℝ) ^ 3 ≤ x) :
    ER_T3' χ z x
      ≤ 524288 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by
  have hz2 : 2 ≤ z := le_trans (by norm_num) hz100
  have hz1R : (1 : ℝ) < z := by exact_mod_cast (by omega : 1 < z)
  have hlogz : 0 < Real.log z := Real.log_pos hz1R
  have hx1 : (1 : ℝ) ≤ x := by
    have h1 : (1 : ℝ) ≤ (z : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    linarith [hzx]
  have hLwin : 0 < Lwin x := by
    rw [Lwin]
    refine Real.log_pos ?_
    linarith
  have hPS : 0 ≤ PretenseSum χ (2 * x + 2) := ERT3'_PS_nonneg χ _
  have hE0 : (0 : ℝ) < Real.exp (Real.log 2 * z0 z x) := Real.exp_pos _
  -- Step 1: the crude per-term cap collapses the sum to a count
  have h1 : ER_T3' χ z x
      ≤ (((l2cWindow χ z x).filter (fun n => IsERT3' χ z n)).card : ℝ)
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2) := by
    rw [ER_T3']
    calc ∑ n ∈ (l2cWindow χ z x).filter (fun n => IsERT3' χ z n),
          Λ n * (LamTilde χ (n + 2) - Λ (n + 2))
        ≤ ∑ _n ∈ (l2cWindow χ z x).filter (fun n => IsERT3' χ z n),
            Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2 :=
          Finset.sum_le_sum fun n hn =>
            ERT3'_term_le χ hsq hz2 (Finset.mem_of_mem_filter n hn)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 2: the fibred count
  have h2 := ERT3'_card_le χ hsq hz100 hzx
  have h3 : ER_T3' χ z x
      ≤ 512 * (x : ℝ) / Real.log (Zz z) ^ 2 * (PretenseSum χ (2 * x + 2) / Real.log z)
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2) :=
    le_trans h1 (mul_le_mul_of_nonneg_right h2
      (mul_nonneg hE0.le (sq_nonneg (Lwin x))))
  -- Step 3: the floor-log conversion `(log Zz)² ≥ (log z)²/1024`
  have hLZsq : Real.log z ^ 2 / 1024 ≤ Real.log (Zz z) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) (ERT3'_log_Zz_ge hz100) 2
    calc Real.log z ^ 2 / 1024 = (Real.log z / 32) ^ 2 := by ring
      _ ≤ Real.log (Zz z) ^ 2 := h
  have hA : 512 * (x : ℝ) / Real.log (Zz z) ^ 2 ≤ 524288 * (x : ℝ) / Real.log z ^ 2 := by
    calc 512 * (x : ℝ) / Real.log (Zz z) ^ 2
        ≤ 512 * (x : ℝ) / (Real.log z ^ 2 / 1024) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hLZsq
      _ = 524288 * (x : ℝ) / Real.log z ^ 2 := by ring
  have h4 : ER_T3' χ z x
      ≤ 524288 * (x : ℝ) / Real.log z ^ 2 * (PretenseSum χ (2 * x + 2) / Real.log z)
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2) := by
    refine le_trans h3 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA
      (div_nonneg hPS hlogz.le)) (mul_nonneg hE0.le (sq_nonneg (Lwin x))))
  -- Step 4: rewrite in `z₀` form and close with the `Aexp = 5` budget
  have halg : 524288 * (x : ℝ) / Real.log z ^ 2 * (PretenseSum χ (2 * x + 2) / Real.log z)
        * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2)
      = 524288 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * (z0 z x ^ 3 * Real.exp (Real.log 2 * z0 z x)) := by
    rw [z0]
    field_simp
  have hfront : 0 ≤ 524288 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg x) hLwin.le)) hPS
  calc ER_T3' χ z x
      ≤ 524288 * (x : ℝ) / Real.log z ^ 2 * (PretenseSum χ (2 * x + 2) / Real.log z)
          * (Real.exp (Real.log 2 * z0 z x) * Lwin x ^ 2) := h4
    _ = 524288 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * (z0 z x ^ 3 * Real.exp (Real.log 2 * z0 z x)) := halg
    _ ≤ 524288 * ((x : ℝ) / Lwin x) * PretenseSum χ (2 * x + 2)
          * Real.exp (5 * z0 z x) :=
        mul_le_mul_of_nonneg_left (ERT3'_z0cube_exp_le hz2) hfront
    _ = 524288 * ((x : ℝ) / Lwin x) * Real.exp (5 * z0 z x)
          * PretenseSum χ (2 * x + 2) := by ring

end Salt.HB
