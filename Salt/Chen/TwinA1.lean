/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.WindowedStep
import Salt.Chen.Hyp4
import Salt.BV.DispersionClose
import Salt.BV.SWChar

/-!
# C2a — A₁ at the twin sequence

Design: `docs/blueprints/chen.md`, the C2a row.  Assembles the lower linear-sieve bound for
the Chen `A₁` carrier

  `A₁ = Σ_{x/2 ≤ n ≤ x−2} Λ(n)·1_{gcd(n+2, P(w₀,z)) = 1}`

at the twin-shifted sequence, feeding the windowed keystone `bjs_theorem6_windowed_lower`
(via `hlevel_w_lower`) into `linear_sieve_lower_rosser_assembled_final`.

## The `BoundingSieve` instance (`twinA1Sieve`)

Mirrors `Salt/Brun/Sieve.lean`'s `TwinSieve`, but for the *shifted single* `n + 2` weighted
by `Λ(n)`:

* `support = (Icc (x/2) (x−2)).image (· + 2)` — the shifted window values `n + 2`;
* `weights m = Λ(m − 2)` (so the element `m = n + 2` carries weight `Λ(n)`);
* `totalMass = Σ_{x/2 ≤ n ≤ x−2} Λ(n)` — the **exact** window Λ-mass (C5 evaluates it; the
  PNT-error is NOT folded in here per the C2a spec);
* `nu = nuChen`, the dimension-1 sifting density `ν(p) = 1/(p−1) = 1/φ(p)` (the `{−2 mod p}`
  residue on Λ-weighted integers), multiplicative because `1/φ` is;
* `prodPrimes = P`, the ℚ-window sifting modulus (the primes of `[w₀, z)`; caller supplies the
  odd/`≥ w₀` facts — the even-`d` glue obligation of the blueprint **dissolves** since every
  `p ∣ P` is `≥ w₀ ≥ 3`, hence odd).

`multSum d` is exactly the window Λ-mass at the residue `n ≡ −2 (mod d)`, and
`rem d = multSum d − ν(d)·totalMass` is the AP-remainder defined by the sieve equation; the
Rosser remainder `rosserRemainder (twinA1Sieve …) (Q·D)` is the (39) L¹ sum over `d ∣ P`,
`d < QD`, consumed at the threaded level `QD` (the catch-#22 constant `Q = Qval ε` paid in).

## The frozen glue obligations (blueprint C2a row)

* **even-`d` trivial branch** — DISSOLVED: `d ∣ P` with all primes `≥ w₀ ≥ 3` is odd, so the
  `g(2) = 0` / `r_d ≪ log²x` branch never arises.
* **`ν(d) = 1/φ(d)` for squarefree `d ∣ P`** — `nuChen_eq_inv_totient`; the exact match with
  the BV main term `y/φ(d)`.
* **level `QD` threaded** — `rosserRemainder … (Q·D)` with `Q = Qval ε` (asymptotically free,
  a constant, but threaded).
* the **two-endpoint window subtraction** and the **ψ_{χ₀}↔ψ main-term conversion** live in the
  (39) reduction `twinA1_abs_rem_le` (`|rem d| ≤ dispDisc (x−2) d + dispDisc (x/2−1) d + …`),
  which feeds the unconditional BV `psi_BV_of_siegelWalfisz'`.

The `fchain`-value is kept **symbolic** (`fchain (maxDepth s) (logRatio z D)`): C1b′/the value
certification supplies the numerics at C5.  The parametric τ-recursion (`hτrec`) and τ-sum
(`htau`), and the hypothesis-(4) family (`h4`), are threaded exactly as in
`StepBound2.bjs_theorem6_lower_sifted'`; C1cτ discharges the τ inputs later.
-/

open Finset ArithmeticFunction Salt.LS Salt.BV

namespace Salt.Chen

/-! ## Part A — the dimension-1 sifting density `ν(p) = 1/(p−1) = 1/φ(p)` -/

/-- The Chen linear-sieve density `ν(d) = 1/φ(d)`, the dimension-1 sifting density of the
`{−2 mod p}` residue (`ν(p) = 1/(p−1)`).  Multiplicative because `φ` is (`Nat.totient_mul`);
`ν(0) = 1/0 = 0` is the `ArithmeticFunction` zero convention. -/
noncomputable def nuChen : ArithmeticFunction ℝ :=
  ⟨fun d => 1 / (d.totient : ℝ), by simp⟩

@[simp] lemma nuChen_apply (d : ℕ) : nuChen d = 1 / (d.totient : ℝ) := rfl

/-- `ν` is multiplicative: `1/φ(mn) = 1/(φm·φn) = (1/φm)(1/φn)` for coprime `m, n`. -/
lemma nuChen_mult : nuChen.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [Nat.totient_one], ?_⟩
  intro m n hm hn hmn
  have h1 : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)).ne'
  have h2 : (n.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  simp only [nuChen_apply, Nat.totient_mul hmn]
  push_cast
  field_simp

/-- `ν(p) = 1/(p−1)` at a prime (`φ(p) = p − 1`). -/
lemma nuChen_prime {p : ℕ} (hp : p.Prime) : nuChen p = 1 / ((p : ℝ) - 1) := by
  rw [nuChen_apply, Nat.totient_prime hp]
  have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    have := hp.one_le; push_cast [Nat.cast_sub this]; ring
  rw [this]

/-- `0 < ν(p)` at a prime. -/
lemma nuChen_pos {p : ℕ} (hp : p.Prime) : 0 < nuChen p := by
  rw [nuChen_apply]
  have : 0 < (p.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  positivity

/-- `ν(p) < 1` at a prime `p ≥ 3` (`φ(p) = p − 1 ≥ 2`). -/
lemma nuChen_lt_one {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : nuChen p < 1 := by
  rw [nuChen_prime hp]
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  rw [div_lt_one (by linarith)]; linarith

/-- **`ν(d) = 1/φ(d)`** for every `d` — the exact match with the BV main term `y/φ(d)`
(stated over all `d`; the squarefree case `d ∣ P` is the consumer). -/
lemma nuChen_eq_inv_totient (d : ℕ) : nuChen d = 1 / (d.totient : ℝ) := rfl

/-! ## Part B — the twin `A₁` `BoundingSieve` -/

/-- The Chen `A₁` window `[x/2, x−2]` (the leader range where Chen's weights are valid). -/
def twinWindow (x : ℕ) : Finset ℕ := Finset.Icc (x / 2) (x - 2)

/-- **The twin `A₁` `BoundingSieve`.**  Support = the shifted window values `n + 2`, weight
`Λ(n)` at `n + 2`, `totalMass` the exact window Λ-mass, density `ν = 1/φ`, sifting modulus
`P` (all prime factors `≥ 3`, supplied by `hPodd`). -/
noncomputable def twinA1Sieve (x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) : BoundingSieve where
  support := (twinWindow x).image (· + 2)
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun m => vonMangoldt (m - 2)
  weights_nonneg := fun _ => vonMangoldt_nonneg
  totalMass := ∑ n ∈ twinWindow x, vonMangoldt n
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hP.ne_zero⟩))

section Facts

@[simp] lemma twinA1Sieve_prodPrimes (x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) : (twinA1Sieve x P hP hPodd).prodPrimes = P := rfl

@[simp] lemma twinA1Sieve_nu (x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) : (twinA1Sieve x P hP hPodd).nu = nuChen := rfl

@[simp] lemma twinA1Sieve_totalMass (x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (twinA1Sieve x P hP hPodd).totalMass = ∑ n ∈ twinWindow x, vonMangoldt n := rfl

/-- **`multSum d` = the window Λ-mass at the residue `n ≡ −2 (mod d)`.**  The sieve sifts the
shifted value `n + 2` by `d ∣ n + 2`. -/
lemma twinA1Sieve_multSum (x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (d : ℕ) :
    (twinA1Sieve x P hP hPodd).multSum d
      = ∑ n ∈ twinWindow x, if d ∣ (n + 2) then vonMangoldt n else 0 := by
  change (∑ m ∈ (twinWindow x).image (· + 2), if d ∣ m then vonMangoldt (m - 2) else 0) = _
  rw [Finset.sum_image (fun a _ b _ h => add_left_injective 2 h)]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Nat.add_sub_cancel]

/-- **`siftedSum` = the `A₁` carrier.**  The Λ-weighted count of `n` in the window with `n + 2`
coprime to `P`. -/
lemma twinA1Sieve_siftedSum (x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (twinA1Sieve x P hP hPodd).siftedSum
      = ∑ n ∈ twinWindow x, if Nat.Coprime P (n + 2) then vonMangoldt n else 0 := by
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ (twinWindow x).image (· + 2),
      if Nat.Coprime P m then vonMangoldt (m - 2) else 0) = _
  rw [Finset.sum_image (fun a _ b _ h => add_left_injective 2 h)]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Nat.add_sub_cancel]

/-- **`rem d`** — the AP-remainder, defined by the sieve equation
`rem d = multSum d − ν(d)·totalMass`. -/
lemma twinA1Sieve_rem (x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (d : ℕ) :
    (twinA1Sieve x P hP hPodd).rem d
      = (∑ n ∈ twinWindow x, if d ∣ (n + 2) then vonMangoldt n else 0)
        - nuChen d * ∑ n ∈ twinWindow x, vonMangoldt n := by
  rw [BoundingSieve.rem, twinA1Sieve_multSum, twinA1Sieve_nu, twinA1Sieve_totalMass]

end Facts

/-! ## Part C — the sieve-class side conditions (`hnu`, `hguard`) -/

/-- **`hnu`** — the sieve density obeys `ν(q) ≤ 1/(q−1)` at every sifting prime.  For the Chen
sieve this is an EQUALITY (`ν(q) = 1/(q−1)`), so the sieve-class inequality is tight. -/
lemma twinA1_hnu (P : ℕ) : ∀ q ∈ P.primeFactors, nuChen q ≤ 1 / ((q : ℝ) - 1) := by
  intro q hq
  rw [nuChen_prime (Nat.prime_of_mem_primeFactors hq)]

/-- **`hguard`** — the hypothesis-(4) threshold guard `19/log q + 4/(q−1) ≤ log(1+ε)` at every
sifting prime, DERIVED from the ℚ-window construction `q ≥ w₀ = w0R ε` (`hPlow`) via
`w0R_threshold` + `thresh_mono`.  The `3 ≤ q` half is the oddness `q ≥ w₀ ≥ 3`. -/
lemma twinA1_hguard {P : ℕ} {ε : ℝ} (hε : 0 < ε) (hw0 : 3 ≤ w0R ε)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ)) :
    ∀ q ∈ P.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) := by
  intro q hq
  refine ⟨by exact_mod_cast hPodd q hq, ?_⟩
  exact thresh_mono hw0 (hPlow q hq) (w0R_threshold hε)

/-! ## Part D — the (39) BV remainder reduction (pointwise `rem` ↦ `dispDisc`)

The pointwise content of the (39) obligation, PROVEN: `|rem d|` (for odd `d ≥ 3`, i.e. every
`d ∣ P` other than `1`) is bounded by the two BV endpoint discrepancies `dispDisc (x−2) d`,
`dispDisc (x/2−1) d` plus the ψ_{χ₀}↔ψ conversion error `ω(d)·log/φ(d)`.  This discharges two
of the blueprint's C2a glue obligations end-to-end:

* the **two-endpoint window subtraction** (`twinA1_rem_eq`: `rem d = apDisc (x−2) d −
  apDisc (x/2−1) d`, the window `[x/2, x−2] = [1, x−2] ∖ [1, x/2−1]`);
* the **ψ_{χ₀}↔ψ main-term conversion** (`apDisc_le`, via `BV.norm_psiChi_one_sub_psiTot_le`:
  the principal-character `ψ(y,χ₀)` and `ψ(y)` differ only on prime powers `p ∣ d`, an
  `ω(d)·log y` error).

The remaining step to the summed `rosserRemainder … (Q·D) ≤ x/(log x)^10` is the L¹ summation
over `d ∣ P`, `d < QD` + the unconditional BV `psi_BV_of_siegelWalfisz'` at the two endpoints
`y = x−2`, `y = x/2−1` (both `≤ x`) + the totient error sum; it is threaded as `hBV` in
`twin_A1_lower` (the `for x large` absorptions and level condition `QD ≤ √x/(log x)^B`). -/

/-- `d − 2` is a reduced residue mod `d` for odd `d ≥ 3` (`gcd(d, d−2) ∣ 2` and `d` odd). -/
theorem coprime_sub_two {d : ℕ} (hd3 : 3 ≤ d) (hodd : Odd d) : Nat.Coprime d (d - 2) := by
  have hg2 : Nat.gcd d (d - 2) ∣ 2 := by
    have h1 : Nat.gcd d (d - 2) ∣ d := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd d (d - 2) ∣ (d - 2) := Nat.gcd_dvd_right _ _
    have h3 := Nat.dvd_sub h1 h2
    rwa [show d - (d - 2) = 2 from by omega] at h3
  have hgd : Nat.gcd d (d - 2) ∣ d := Nat.gcd_dvd_left _ _
  rcases (Nat.dvd_prime Nat.prime_two).mp hg2 with h1 | h2
  · exact h1
  · exfalso
    rw [h2] at hgd
    obtain ⟨k, hk⟩ := hgd
    obtain ⟨j, hj⟩ := hodd
    omega

/-- The AP-discrepancy of the `{−2 mod d}` residue against the totient main term `ψ(y)/φ(d)`. -/
noncomputable def apDisc (y d : ℕ) : ℝ := psiAP y d (d - 2) - psiTot y / (d.totient : ℝ)

/-- **`apDisc` ≤ `dispDisc` + conversion error.**  The cumulative discrepancy against the
totient main term is bounded by the BV maximal discrepancy `dispDisc y d` (which uses the
`ψ(y,χ₀)/φ(d)` main term) plus the ψ_{χ₀}↔ψ conversion `ω(d)·log y/φ(d)`. -/
theorem apDisc_le (y d : ℕ) (hd3 : 3 ≤ d) (hodd : Odd d) (hy : 1 ≤ y) :
    |apDisc y d| ≤ dispDisc y d + (d.primeFactors.card : ℝ) * Real.log y / (d.totient : ℝ) := by
  haveI : NeZero d := ⟨by omega⟩
  have hcop : Nat.Coprime d (d - 2) := coprime_sub_two hd3 hodd
  have hne : ((range d).filter (Nat.Coprime d)).Nonempty := reduced_nonempty (by omega)
  have hmem : (d - 2) ∈ (range d).filter (Nat.Coprime d) := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hcop⟩
  have hle : ‖(psiAP y d (d - 2) : ℂ) - psiChi y (1 : DirichletCharacter ℂ d) / (d.totient : ℂ)‖
      ≤ dispDisc y d := by
    rw [dispDisc, dif_pos hne]
    exact Finset.le_sup'
      (fun a => ‖(psiAP y d a : ℂ) - psiChi y (1 : DirichletCharacter ℂ d) / (d.totient : ℂ)‖) hmem
  have hconv : ‖psiChi y (1 : DirichletCharacter ℂ d) - (psiTot y : ℂ)‖
      ≤ (d.primeFactors.card : ℝ) * Real.log y := norm_psiChi_one_sub_psiTot_le (by omega)
  have hreal : |apDisc y d|
      = ‖(psiAP y d (d - 2) : ℂ) - (psiTot y : ℂ) / (d.totient : ℂ)‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    congr 1
    rw [apDisc]; push_cast; ring
  rw [hreal]
  have hsplit : (psiAP y d (d - 2) : ℂ) - (psiTot y : ℂ) / (d.totient : ℂ)
      = ((psiAP y d (d - 2) : ℂ) - psiChi y (1 : DirichletCharacter ℂ d) / (d.totient : ℂ))
        + (psiChi y (1 : DirichletCharacter ℂ d) - (psiTot y : ℂ)) / (d.totient : ℂ) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hb2 : ‖(psiChi y (1 : DirichletCharacter ℂ d) - (psiTot y : ℂ)) / (d.totient : ℂ)‖
      ≤ (d.primeFactors.card : ℝ) * Real.log y / (d.totient : ℝ) := by
    rw [norm_div, Complex.norm_natCast]; gcongr
  linarith [hle, hb2]

/-- Residue equivalence: `d ∣ n + 2 ↔ n ≡ −2 (mod d)` (as `n % d = (d − 2) % d`), for `d ≥ 3`. -/
theorem dvd_add_two_iff {d : ℕ} (hd3 : 3 ≤ d) (n : ℕ) :
    (d ∣ (n + 2)) ↔ (n % d = (d - 2) % d) := by
  have hd0 : 0 < d := by omega
  have hrhs : (d - 2) % d = d - 2 := Nat.mod_eq_of_lt (by omega)
  rw [hrhs, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_eq_of_lt (show (2 : ℕ) < d by omega)]
  have hm : n % d < d := Nat.mod_lt n hd0
  set m := n % d with hmdef
  constructor
  · intro h
    have hdvd : d ∣ (m + 2) := Nat.dvd_of_mod_eq_zero h
    have hle : d ≤ m + 2 := Nat.le_of_dvd (by omega) hdvd
    rcases (by omega : m + 2 = d ∨ m + 2 = d + 1) with he | he
    · omega
    · exfalso; rw [he] at hdvd
      have hd1 : d ∣ 1 := (Nat.dvd_add_right (dvd_refl d)).mp hdvd
      have := Nat.le_of_dvd one_pos hd1; omega
  · intro h
    have hmd : m + 2 = d := by omega
    rw [hmd, Nat.mod_self]

/-- The cumulative window AP-sum equals `psiAP` at the shifted residue (`d ≥ 3`). -/
theorem apSum_eq_psiAP {d : ℕ} (hd3 : 3 ≤ d) (y : ℕ) :
    (∑ n ∈ Finset.Icc 1 y, if d ∣ (n + 2) then vonMangoldt n else 0) = psiAP y d (d - 2) := by
  rw [psiAP, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro n _
  exact dvd_add_two_iff hd3 n

theorem Icc_one_eq_Ioc (y : ℕ) : Finset.Icc 1 y = Finset.Ioc 0 y := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

theorem Icc_eq_Ioc_pred {a : ℕ} (b : ℕ) (ha : 1 ≤ a) :
    Finset.Icc a b = Finset.Ioc (a - 1) b := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- The window-subtraction identity `Σ_{[a,b]} = Σ_{[1,b]} − Σ_{[1,a−1]}` (`1 ≤ a`, `a−1 ≤ b`). -/
theorem sum_Icc_window (g : ℕ → ℝ) (a b : ℕ) (ha : 1 ≤ a) (hab : a - 1 ≤ b) :
    ∑ n ∈ Finset.Icc a b, g n
      = (∑ n ∈ Finset.Icc 1 b, g n) - ∑ n ∈ Finset.Icc 1 (a - 1), g n := by
  have hcons := Finset.sum_Ioc_consecutive g (Nat.zero_le (a - 1)) hab
  rw [Icc_eq_Ioc_pred b ha, Icc_one_eq_Ioc b, Icc_one_eq_Ioc (a - 1)]
  linarith [hcons]

/-- **The two-endpoint window subtraction.**  `rem d = apDisc (x−2) d − apDisc (x/2−1) d`:
the window `[x/2, x−2]` is `[1, x−2] ∖ [1, x/2−1]`, so the AP-remainder splits into the two
cumulative-endpoint discrepancies (`d ≥ 3`, `x ≥ 4`). -/
theorem twinA1_rem_eq (x P : ℕ) (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (d : ℕ) (hd3 : 3 ≤ d) (hx : 4 ≤ x) :
    (twinA1Sieve x P hP hPodd).rem d = apDisc (x - 2) d - apDisc (x / 2 - 1) d := by
  rw [twinA1Sieve_rem, twinWindow,
    sum_Icc_window (fun n => if d ∣ (n + 2) then vonMangoldt n else 0) (x / 2) (x - 2)
      (by omega) (by omega),
    sum_Icc_window (fun n => vonMangoldt n) (x / 2) (x - 2) (by omega) (by omega)]
  rw [apSum_eq_psiAP hd3 (x - 2), apSum_eq_psiAP hd3 (x / 2 - 1)]
  have hpt : ∀ y, (∑ n ∈ Finset.Icc 1 y, vonMangoldt n) = psiTot y := fun _ => rfl
  rw [hpt (x - 2), hpt (x / 2 - 1), apDisc, apDisc, nuChen_apply]
  ring

/-- **The pointwise (39) bound.**  For odd `d ≥ 3` (every `d ∣ P` other than `1`),
`|rem d| ≤ dispDisc (x−2) d + dispDisc (x/2−1) d + (ψ_{χ₀}↔ψ conversion error)`.  This is the
per-divisor input the summed (39) remainder bound (`hBV`) consumes against the unconditional
BV `psi_BV_of_siegelWalfisz'`. -/
theorem twinA1_abs_rem_le (x P : ℕ) (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (d : ℕ) (hd3 : 3 ≤ d) (hodd : Odd d) (hx : 4 ≤ x) :
    |(twinA1Sieve x P hP hPodd).rem d|
      ≤ dispDisc (x - 2) d + dispDisc (x / 2 - 1) d
        + ((d.primeFactors.card : ℝ) * Real.log ((x - 2 : ℕ) : ℝ) / (d.totient : ℝ)
          + (d.primeFactors.card : ℝ) * Real.log ((x / 2 - 1 : ℕ) : ℝ) / (d.totient : ℝ)) := by
  rw [twinA1_rem_eq x P hP hPodd d hd3 hx]
  have h1 := apDisc_le (x - 2) d hd3 hodd (by omega)
  have h2 := apDisc_le (x / 2 - 1) d hd3 hodd (by omega)
  have htri : |apDisc (x - 2) d - apDisc (x / 2 - 1) d|
      ≤ |apDisc (x - 2) d| + |apDisc (x / 2 - 1) d| := abs_sub _ _
  linarith [htri, h1, h2]

/-! ## Part E — the assembled `A₁` lower bound (`twin_A1_lower`) -/

/-- **`twin_A1_lower` — the C2a endpoint.**  The assembled lower linear-sieve bound for the
Chen `A₁` carrier, feeding the windowed keystone `hlevel_w_lower` (BJS Theorem 6 (6), per-step
comparison discharged) into `linear_sieve_lower_rosser_assembled_final`, with the (39) BV
remainder folded in.

The conclusion:
```
(window Λ-mass) · V(z) · (fchain N (logRatio z D) − ε·C₂·e²·h) − x/(log x)^10
  ≤ Σ_{x/2 ≤ n ≤ x−2} Λ(n)·1_{gcd(n+2, P) = 1}
```
where `V(z) = W (twinA1Sieve …)`, `N = maxDepth`, and the `fchain`-value is **symbolic**
(C1b′/the value certification supplies numerics at C5).

Threaded inputs (the standard `bjs_theorem6_lower_sifted'` pattern):
* `h4` — the hypothesis-(4) V-ratio family (dischargeable per sub-sieve by `h4_base`;
  see the module note on the `∀ s'` shape);
* `hτrec`, `htau` — the parametric τ-recursion / τ-sum (C1cτ discharges later);
* `hBV` — the (39) BV remainder bound `rosserRemainder (twinA1Sieve …) (Q·D) ≤ x/(log x)^10`,
  the unconditional-BV consequence (`psi_BV_of_siegelWalfisz'`; the pointwise reduction is
  `twinA1_abs_rem_le` below).  The level `Q·D = QD` is threaded (`Q = Qval ε`, a constant). -/
theorem twin_A1_lower (x z D P : ℕ) (ε K C₂ Q : ℝ) (tau : ℕ → ℝ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPz : ∀ p ∈ P.primeFactors, p < z)
    (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ))
    (hz2 : 2 ≤ z) (hzD : z ≤ D) (hD : 1 ≤ D)
    (hStop : 2 ≤ logRatio z D)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hKe : K ≤ 1 + ε)
    (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hτrec : ∀ n, cf_const n ε + ε * Real.exp 2 * ch_const n ε * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (htau : ∑ n ∈ (Finset.range (maxDepth (twinA1Sieve x P hP hPodd) + 1)).filter
        (fun n => Even n), tau n ≤ C₂)
    (hQ : 1 ≤ Q)
    (hBV : rosserRemainder (twinA1Sieve x P hP hPodd) (Q * D) ≤ (x : ℝ) / (Real.log x) ^ 10) :
    (twinA1Sieve x P hP hPodd).totalMass *
        (Salt.BrunLower.W (twinA1Sieve x P hP hPodd) *
          (fchain (maxDepth (twinA1Sieve x P hP hPodd)) (logRatio z D)
            - ε * C₂ * Real.exp 2 * hBJS (logRatio z D)))
      - (x : ℝ) / (Real.log x) ^ 10
    ≤ ∑ n ∈ twinWindow x, if Nat.Coprime P (n + 2) then vonMangoldt n else 0 := by
  set s := twinA1Sieve x P hP hPodd with hs
  -- side conditions for the concrete sieve
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < z := hPz
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := twinA1_hnu P
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    twinA1_hguard hε hw0 hPodd hPlow
  have htm : 0 ≤ s.totalMass := by
    rw [twinA1Sieve_totalMass]; exact Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
  -- the windowed per-level (hlevel) bound (per-step comparison discharged)
  have hlevel := hlevel_w_lower s z D ε K tau hD hzTop hguard hnu hε.le hKe htau1 hτ0 hτrec h4 hStop
  -- assemble to the sifted lower bound at level Q·D
  have hassembled := linear_sieve_lower_rosser_assembled_final s D z hz2 hzD hzTop htm
    (logRatio z D) ε C₂ Q hQ hε.le tau hlevel htau
  -- rewrite the sifted sum as the A₁ carrier and fold in the BV remainder
  rw [twinA1Sieve_siftedSum] at hassembled
  linarith [hassembled, hBV]

end Salt.Chen
