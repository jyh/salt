/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.Assembly
import Salt.Chen.TwinSharp
import Salt.Chen.BVSum

/-!
# A1W — the AP-restricted `A₁` instance + supplier mirror (H-AMENDMENT 2)

Design: `docs/blueprints/chen.md`, H-AMENDMENT 2 (D1–D8) with the gate corrections C1–C7;
node A1W.  The W-trick repair of catch #65 restricts the `A₁` razor carrier to the residue
class `n ≡ a (mod Q)` (`Q = Qval ε`, `a = Q − 1` at instantiation); this file supplies the
AP-restricted `BoundingSieve` instance, its remainder identification, the supplier mirrors of
`twin_A1_lower`/`twin_A1_lower_B`, the BV discharge mirror, and the Finding-6 prime-power
bridge into `A1primeSumW` (W-SURG's `hA1` slot).

## The instance (`twinA1SieveW`) — the C3-(ii) SMOOTH `totalMass` convention

* `support = ((twinWindow x).filter (n % Q = a % Q)).image (· + 2)` — the AP-restricted
  shifted window;
* `weights m = Λ(m − 2)`, `nu = nuChen`, `prodPrimes = P` — as the landed instance (D2:
  `nu` UNCHANGED, the AP density cancels in the ν-ratio);
* **`totalMass = (Σ_{n ∈ window} Λ(n)) / φ(Q)`** — the SMOOTH window mass divided by `φ(Q)`,
  per gate correction C3-(ii); NOT the AP-restricted sum.  With this convention `rem d` is
  EXACTLY the modulus-`Q·d` discrepancy (below), and `rem 1` is the mod-`Q` SW row (absorbed
  here into the same `dispDisc` family at `q = Q·1` — the `d ↦ Q·d` injection covers `d = 1`).

## The remainder identification — the class `c(d)` derivation

The sieve sifts `m = n + 2` by `d ∣ m` over the support points `n ≡ a (mod Q)`, so
`multSum d = Σ_{n ∈ window, n ≡ a (Q), d ∣ n+2} Λ(n)`.  The discrepancy carrier `psiAP`
counts `n` (the `Λ`-weights sit at `n = m − 2`), hence the CRT class is the **`n`-side**
class:

  `c(d) ≡ a (mod Q)`  and  `c(d) ≡ −2 ≡ d − 2 (mod d)`

(NOT `a + 2` — the `m`-side class `(a+2 mod Q, 0 mod d)` is what the sieve sifts, but the
ψ-ledger is indexed by `n`).  With `gcd(Q, d) = 1` (P's support ≥ w₀ > every prime of `Q`;
threaded as `hQP : Coprime Q P`) the two congruences give one class mod `Q·d`
(`Nat.chineseRemainder`), and with the smooth totalMass

  `rem d = multSum d − ν(d)·totalMass
         = [ψ_AP-window at (Q·d, c(d))] − [ψ-window]/φ(Q·d)
         = apDiscW (x−2) (Qd) c − apDiscW (x/2−1) (Qd) c`

exactly (`φ(Qd) = φ(Q)·φ(d)` by coprimality — nothing extra).  Reducedness
`gcd(c(d), Q·d) = 1`: `gcd(c, Q) = gcd(a, Q) = 1` (hypothesis `hQa`, discharged at
`a = Q − 1` by `residue_witness'`) and `gcd(c, d) = gcd(d−2, d) = 1` (`d` odd ≥ 3 via
`coprime_sub_two`; `d = 1` trivial).  In particular `c` is odd even though `Q·d` is even
(`2 ∣ Q`, `2 ∤ c` from `gcd(c, Q) = 1`).  `gcd(a+2, Q) = 1` is NOT consumed on this side.

## The BV discharge mirror (`twinA1_hBV_W`) — a fortiori through `d ↦ Q·d`

`|rem d|` is two `dispDisc` values at modulus `Q·d` plus the ψ_{χ₀}↔ψ conversion
`convTerm x (Q·d)`.  The map `d ↦ Q·d` is injective and lands the family inside
`Icc 1 ⌊√x/(log x)^B⌋₊` under the W-LEVEL row, so `dispDisc ≥ 0` gives the a-fortiori
reduction to the unconditional BV `psi_BV_of_siegelWalfisz'` at the two endpoints.

### The named GLU-2W obligations created here (documented per the node mandate)

* **W-LEVEL row**: `(Q : ℝ)·(Qlev·D) ≤ √x/(log x)^B` — one extra `Q ≤ 4^{w₀} ≤ log x`
  factor over the landed C2c row (gate correction C2: `Nat.primorial_le_four_pow` + the
  tower `x₀ ≥ exp(exp(2·w0N ε))`); absorbed by `x^{ε'}` room at the operating point.
* **W-CLOSE row**: `C·x/L^11 + C·x/L^11 + 2L·(ω(Q) + log(Qlev·D)/log 3)·((1+ε)·log z/log w₀)
  ≤ x/L^10` — the conversion sum gains the constant `ω(Q)` summand (`ω(Q·d) ≤ ω(Q) + ω(d)`;
  `φ(Qd) ≥ φ(d)` drops the `1/φ(Q)` for free); still `(log x)^3`-polylog against `x/L^10`.
* **`hQP : Coprime Q P`** — disjoint prime supports (`P`'s primes ≥ w₀R > every prime `< w0N`
  of `Q = Qval ε`); GLU-2W derives it from `hPlow`.
* **`hQa : Coprime Q a`** — free at `a = Q − 1` (`residue_witness'`, Assembly Part L).

## Finding 6 (D6) — the prime-power bridge

`twin_A1_lower_B_W`'s conclusion is the AP-restricted coprime `Λ`-sum WITHOUT the
`[n prime]` restriction that `A1primeSumW` carries; the gap is supported on non-prime prime
powers `p^k ≤ x` (`k ≥ 2`), each with `p ≤ √x`, `k ≤ log₂ x`, `Λ = log p ≤ log x` — total
mass `≤ √x·(log₂ x)·log x` (`primePowerMass_le`).  `A1primeSumW_bridge` folds it in; the
final `example` chains deliverables 3+4+5 into W-SURG's `hA1` slot shape.
-/

open Finset ArithmeticFunction Salt.LS Salt.BV

namespace Salt.Chen

/-! ## Part A — the AP-restricted `BoundingSieve` instance -/

/-- **The AP-restricted twin `A₁` `BoundingSieve`** (H-AMENDMENT 2, D2/C3).  Support = the
shifted values `n + 2` of the AP-restricted window `{n ∈ [x/2, x−2] : n ≡ a (mod Q)}`, weight
`Λ(n)` at `n + 2`, density `ν = nuChen = 1/φ` (UNCHANGED — the AP density cancels in the
ν-ratio), sifting modulus `P` (all prime factors `≥ 3` via `hPodd`), and the C3-(ii) **SMOOTH**
total mass `(Σ_{n ∈ window} Λ(n))/φ(Q)` — the plain window `Λ`-mass divided by `φ(Q)`, NOT the
AP-restricted sum.  With this convention `rem d` is exactly the `Q·d`-modulus discrepancy
(`twinA1W_rem_eq`). -/
noncomputable def twinA1SieveW (Q a x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) : BoundingSieve where
  support := ((twinWindow x).filter (fun n => n % Q = a % Q)).image (· + 2)
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun m => vonMangoldt (m - 2)
  weights_nonneg := fun _ => vonMangoldt_nonneg
  totalMass := (∑ n ∈ twinWindow x, vonMangoldt n) / (Q.totient : ℝ)
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hP.ne_zero⟩))

section FactsW

@[simp] lemma twinA1SieveW_prodPrimes (Q a x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (twinA1SieveW Q a x P hP hPodd).prodPrimes = P := rfl

@[simp] lemma twinA1SieveW_nu (Q a x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (twinA1SieveW Q a x P hP hPodd).nu = nuChen := rfl

@[simp] lemma twinA1SieveW_totalMass (Q a x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (twinA1SieveW Q a x P hP hPodd).totalMass
      = (∑ n ∈ twinWindow x, vonMangoldt n) / (Q.totient : ℝ) := rfl

/-- **`multSum d` = the window `Λ`-mass at the joint residue** `n ≡ a (mod Q)`, `d ∣ n + 2`.
The sieve sifts the shifted value `m = n + 2` by `d ∣ m` over the AP-restricted support. -/
lemma twinA1SieveW_multSum (Q a x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (d : ℕ) :
    (twinA1SieveW Q a x P hP hPodd).multSum d
      = ∑ n ∈ twinWindow x, if n % Q = a % Q ∧ d ∣ (n + 2) then vonMangoldt n else 0 := by
  change (∑ m ∈ ((twinWindow x).filter (fun n => n % Q = a % Q)).image (· + 2),
      if d ∣ m then vonMangoldt (m - 2) else 0) = _
  rw [Finset.sum_image (fun n₁ _ n₂ _ h => add_left_injective 2 h), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Nat.add_sub_cancel, ite_and]

/-- **`siftedSum` = the AP-restricted `A₁` carrier** (rfl-level identification): the
`Λ`-weighted count of `n ≡ a (mod Q)` in the window with `n + 2` coprime to `P`. -/
lemma twinA1SieveW_siftedSum (Q a x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (twinA1SieveW Q a x P hP hPodd).siftedSum
      = ∑ n ∈ twinWindow x,
          if n % Q = a % Q ∧ Nat.Coprime P (n + 2) then vonMangoldt n else 0 := by
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ ((twinWindow x).filter (fun n => n % Q = a % Q)).image (· + 2),
      if Nat.Coprime P m then vonMangoldt (m - 2) else 0) = _
  rw [Finset.sum_image (fun n₁ _ n₂ _ h => add_left_injective 2 h), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Nat.add_sub_cancel, ite_and]

/-- **`rem d`** — the sieve-equation remainder at the smooth totalMass. -/
lemma twinA1SieveW_rem (Q a x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (d : ℕ) :
    (twinA1SieveW Q a x P hP hPodd).rem d
      = (∑ n ∈ twinWindow x, if n % Q = a % Q ∧ d ∣ (n + 2) then vonMangoldt n else 0)
        - nuChen d * ((∑ n ∈ twinWindow x, vonMangoldt n) / (Q.totient : ℝ)) := by
  rw [BoundingSieve.rem, twinA1SieveW_multSum, twinA1SieveW_nu, twinA1SieveW_totalMass]

end FactsW

/-! ## Part B — the CRT class `c(d)` and the `Q·d`-discrepancy identification

The class derivation (module header): the ψ-ledger counts `n`, so the class is the `n`-side
`c ≡ a (mod Q)`, `c ≡ d − 2 (mod d)`; `Nat.chineseRemainder` fuses the pair at `gcd(Q,d)=1`.
The `d = 1` divisor is handled UNIFORMLY (class `c ≡ a (mod Q)`, modulus `Q·1 = Q` — the
mod-`Q` SW row of C3, absorbed into the same `dispDisc` family). -/

/-- `d ∣ n + 2 ↔ n ≡ d − 2 (mod d)` for every `d ≥ 1` (the landed `dvd_add_two_iff` covers
`d ≥ 3`; `d = 1, 2` are degenerate-true, giving the uniform `d ∣ P`-divisor treatment
including `d = 1`). -/
theorem dvd_add_two_iff' {d : ℕ} (hd1 : 1 ≤ d) (n : ℕ) :
    (d ∣ (n + 2)) ↔ (n % d = (d - 2) % d) := by
  rcases (by omega : d = 1 ∨ d = 2 ∨ 3 ≤ d) with rfl | rfl | hd3
  · omega
  · omega
  · exact dvd_add_two_iff hd3 n

/-- **The CRT class `c(d)`** — the fused residue `c ≡ a (mod Q)`, `c ≡ d − 2 (mod d)`
(`gcd(Q, d) = 1`).  The `n`-side class of the AP-restricted sieve at divisor `d`. -/
def crtClass (Q a d : ℕ) (h : Nat.Coprime Q d) : ℕ :=
  (Nat.chineseRemainder h a (d - 2) : ℕ)

lemma crtClass_mod_left (Q a d : ℕ) (h : Nat.Coprime Q d) :
    crtClass Q a d h % Q = a % Q :=
  (Nat.chineseRemainder h a (d - 2)).2.1

lemma crtClass_mod_right (Q a d : ℕ) (h : Nat.Coprime Q d) :
    crtClass Q a d h % d = (d - 2) % d :=
  (Nat.chineseRemainder h a (d - 2)).2.2

/-- **The joint-residue equivalence.**  Membership in the AP class mod `Q` together with
`d ∣ n + 2` is exactly membership in the single class `c` mod `Q·d` (CRT at `gcd(Q,d) = 1`). -/
theorem apW_class_iff {Q a d c : ℕ} (hd1 : 1 ≤ d) (hQd : Nat.Coprime Q d)
    (hcQ : c % Q = a % Q) (hcd : c % d = (d - 2) % d) (n : ℕ) :
    (n % Q = a % Q ∧ d ∣ (n + 2)) ↔ n % (Q * d) = c % (Q * d) := by
  have h1 : (n % Q = a % Q) ↔ (n % Q = c % Q) := by rw [hcQ]
  have h2 : (d ∣ (n + 2)) ↔ (n % d = c % d) := by rw [dvd_add_two_iff' hd1 n, hcd]
  rw [h1, h2]
  exact Nat.modEq_and_modEq_iff_modEq_mul hQd

/-- **`gcd(c(d), Q·d) = 1` — the class is reduced.**  `gcd(c, Q) = gcd(a, Q) = 1` from the
hypothesis `hQa` (at `a = Q − 1` this is `residue_witness'`), and `gcd(c, d) = gcd(d−2, d) = 1`
for odd `d ≥ 3` (`coprime_sub_two`; `d = 1` trivial).  In particular `c` is odd even though
`Q·d` is even.  Note `gcd(a+2, Q)` is NOT needed on the `n`-side (module header). -/
theorem crt_class_coprime {Q a d c : ℕ} (hd : d = 1 ∨ (3 ≤ d ∧ Odd d))
    (hQa : Nat.Coprime Q a) (hcQ : c % Q = a % Q) (hcd : c % d = (d - 2) % d) :
    Nat.Coprime (Q * d) c := by
  have hQc : Nat.Coprime Q c := by
    have h : Nat.gcd c Q = Nat.gcd a Q :=
      Nat.ModEq.gcd_eq (show c ≡ a [MOD Q] from hcQ)
    rw [Nat.Coprime, Nat.gcd_comm, h, Nat.gcd_comm]
    exact hQa
  have hdc : Nat.Coprime d c := by
    rcases hd with rfl | ⟨hd3, hodd⟩
    · exact Nat.coprime_one_left c
    · have hsub : Nat.Coprime d (d - 2) := coprime_sub_two hd3 hodd
      have h : Nat.gcd c d = Nat.gcd (d - 2) d :=
        Nat.ModEq.gcd_eq (show c ≡ (d - 2) [MOD d] from hcd)
      rw [Nat.Coprime, Nat.gcd_comm, h, Nat.gcd_comm]
      exact hsub
  exact Nat.Coprime.mul_left hQc hdc

/-- The AP-discrepancy at modulus `q`, class `c`, against the totient main term `ψ(y)/φ(q)` —
the W-mirror of `apDisc` with the class as a parameter (the landed `apDisc y d` is the special
case `q := d`, `c := d − 2`). -/
noncomputable def apDiscW (y q c : ℕ) : ℝ := psiAP y q c - psiTot y / (q.totient : ℝ)

/-- `psiAP` only sees the class mod `q`: the representative may be reduced. -/
lemma psiAP_mod_class (y q c : ℕ) : psiAP y q (c % q) = psiAP y q c := by
  simp only [psiAP]
  congr 1
  apply Finset.filter_congr
  intro n _
  rw [Nat.mod_mod_of_dvd c (dvd_refl q)]

/-- **`apDiscW` ≤ `dispDisc` + conversion error** — `apDisc_le` at a general reduced class
`c` mod `q`.  The cumulative discrepancy at `(q, c)` is bounded by the BV maximal discrepancy
`dispDisc y q` (the `ψ(y,χ₀)/φ(q)` main term, sup over reduced residues — `c % q` is one by
`hcop`) plus the ψ_{χ₀}↔ψ conversion `ω(q)·log y/φ(q)`. -/
theorem apDiscW_le (y q c : ℕ) (hq1 : 1 ≤ q) (hcop : Nat.Coprime q c) (hy : 1 ≤ y) :
    |apDiscW y q c| ≤ dispDisc y q
      + (q.primeFactors.card : ℝ) * Real.log y / (q.totient : ℝ) := by
  haveI : NeZero q := ⟨by omega⟩
  have hcop' : Nat.Coprime q (c % q) :=
    ((ZMod.coprime_mod_iff_coprime c q).mpr hcop.symm).symm
  have hne : ((range q).filter (Nat.Coprime q)).Nonempty := reduced_nonempty hq1
  have hmem : (c % q) ∈ (range q).filter (Nat.Coprime q) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt c (by omega), hcop'⟩
  have hle : ‖(psiAP y q c : ℂ) - psiChi y (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖
      ≤ dispDisc y q := by
    rw [dispDisc, dif_pos hne, ← psiAP_mod_class y q c]
    exact Finset.le_sup'
      (fun a => ‖(psiAP y q a : ℂ) - psiChi y (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖)
      hmem
  have hconv : ‖psiChi y (1 : DirichletCharacter ℂ q) - (psiTot y : ℂ)‖
      ≤ (q.primeFactors.card : ℝ) * Real.log y := norm_psiChi_one_sub_psiTot_le hy
  have hreal : |apDiscW y q c|
      = ‖(psiAP y q c : ℂ) - (psiTot y : ℂ) / (q.totient : ℂ)‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    congr 1
    rw [apDiscW]; push_cast; ring
  rw [hreal]
  have hsplit : (psiAP y q c : ℂ) - (psiTot y : ℂ) / (q.totient : ℂ)
      = ((psiAP y q c : ℂ) - psiChi y (1 : DirichletCharacter ℂ q) / (q.totient : ℂ))
        + (psiChi y (1 : DirichletCharacter ℂ q) - (psiTot y : ℂ)) / (q.totient : ℂ) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hb2 : ‖(psiChi y (1 : DirichletCharacter ℂ q) - (psiTot y : ℂ)) / (q.totient : ℂ)‖
      ≤ (q.primeFactors.card : ℝ) * Real.log y / (q.totient : ℝ) := by
    rw [norm_div, Complex.norm_natCast]; gcongr
  linarith [hle, hb2]

/-- The cumulative joint-residue window sum equals `psiAP` at `(Q·d, c)`. -/
theorem apSumW_eq_psiAP {Q a d c : ℕ} (hd1 : 1 ≤ d) (hQd : Nat.Coprime Q d)
    (hcQ : c % Q = a % Q) (hcd : c % d = (d - 2) % d) (y : ℕ) :
    (∑ n ∈ Finset.Icc 1 y, if n % Q = a % Q ∧ d ∣ (n + 2) then vonMangoldt n else 0)
      = psiAP y (Q * d) c := by
  rw [psiAP, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro n _
  exact apW_class_iff hd1 hQd hcQ hcd n

/-- **The W remainder identification** (`twinA1_rem_eq` mirrored at `(Q·d, c(d))`).  With the
C3-(ii) smooth `totalMass`, `rem d` is EXACTLY the two-endpoint difference of the modulus-`Q·d`
discrepancies at the class `c` — the gate-verified identity, nothing extra: `ν(d)·totalMass =
(1/φ(d))·ψ-window/φ(Q) = ψ-window/φ(Q·d)` by `φ(Qd) = φ(Q)φ(d)` (`gcd(Q,d) = 1`). -/
theorem twinA1W_rem_eq (Q a x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) {d c : ℕ}
    (hQ1 : 1 ≤ Q) (hd1 : 1 ≤ d) (hQd : Nat.Coprime Q d) (hx : 4 ≤ x)
    (hcQ : c % Q = a % Q) (hcd : c % d = (d - 2) % d) :
    (twinA1SieveW Q a x P hP hPodd).rem d
      = apDiscW (x - 2) (Q * d) c - apDiscW (x / 2 - 1) (Q * d) c := by
  rw [twinA1SieveW_rem, twinWindow,
    sum_Icc_window (fun n => if n % Q = a % Q ∧ d ∣ (n + 2) then vonMangoldt n else 0)
      (x / 2) (x - 2) (by omega) (by omega),
    sum_Icc_window (fun n => vonMangoldt n) (x / 2) (x - 2) (by omega) (by omega)]
  rw [apSumW_eq_psiAP hd1 hQd hcQ hcd (x - 2), apSumW_eq_psiAP hd1 hQd hcQ hcd (x / 2 - 1)]
  have hpt : ∀ y, (∑ n ∈ Finset.Icc 1 y, vonMangoldt n) = psiTot y := fun _ => rfl
  rw [hpt (x - 2), hpt (x / 2 - 1), apDiscW, apDiscW, nuChen_apply]
  have hφ : ((Q * d).totient : ℝ) = (Q.totient : ℝ) * (d.totient : ℝ) := by
    rw [Nat.totient_mul hQd]; push_cast; ring
  have hQt : (Q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < Q)).ne'
  have hdt : (d.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < d)).ne'
  rw [hφ]
  field_simp
  ring

/-- **The pointwise W (39) bound** (`twinA1_abs_rem_le` mirrored at `(Q·d, c(d))`): for a
reduced class `c` of the divisor `d`, `|rem d| ≤ dispDisc(x−2)(Qd) + dispDisc(x/2−1)(Qd) +
convTerm x (Qd)` — the per-divisor input for the summed BV discharge. -/
theorem twinA1W_abs_rem_le (Q a x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) {d c : ℕ}
    (hQ1 : 1 ≤ Q) (hd1 : 1 ≤ d) (hQd : Nat.Coprime Q d) (hx : 4 ≤ x)
    (hcQ : c % Q = a % Q) (hcd : c % d = (d - 2) % d)
    (hccop : Nat.Coprime (Q * d) c) :
    |(twinA1SieveW Q a x P hP hPodd).rem d|
      ≤ dispDisc (x - 2) (Q * d) + dispDisc (x / 2 - 1) (Q * d) + convTerm x (Q * d) := by
  have hQd1 : 1 ≤ Q * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rw [twinA1W_rem_eq Q a x P hP hPodd hQ1 hd1 hQd hx hcQ hcd]
  have h1 := apDiscW_le (x - 2) (Q * d) c hQd1 hccop (by omega)
  have h2 := apDiscW_le (x / 2 - 1) (Q * d) c hQd1 hccop (by omega)
  have htri : |apDiscW (x - 2) (Q * d) c - apDiscW (x / 2 - 1) (Q * d) c|
      ≤ |apDiscW (x - 2) (Q * d) c| + |apDiscW (x / 2 - 1) (Q * d) c| := abs_sub _ _
  unfold convTerm
  linarith [htri, h1, h2]

/-! ## Part C — the supplier mirrors (`twin_A1_lower_W`, `twin_A1_lower_B_W`)

The generic keystones (`hlevel_w_lower`/`hlevel_wpc_lower` and
`linear_sieve_lower_rosser_assembled_final`) are support-agnostic (gate surface 4); only the
instance facts re-prove — `siftedSum` (rfl-level, Part A), `htm` (the smooth mass is `≥ 0`),
and `hguard`/`hnu` which delegate to the landed `twinA1_hguard`/`twinA1_hnu` VERBATIM
(both are statements about `P.primeFactors` only, and `prodPrimes = P` definitionally). -/

/-- **`twin_A1_lower_W` — the AP-restricted C2a endpoint** (H-AMENDMENT 2 supplier mirror).
`twin_A1_lower` at `twinA1SieveW`: the assembled lower linear-sieve bound for the AP-restricted
`A₁` carrier, with the H4C-CONDITIONED `h4` slot (catch #66: sieve-class rows + the flat-cell
window `1 ≤ logRatio ≤ 3`) threaded verbatim, concluding the AP-restricted coprime `Λ`-sum
lower bound.  `hBV` = the W remainder row, supplied by `twinA1_hBV_W`. -/
theorem twin_A1_lower_W (Qm a x z D P : ℕ) (ε K C₂ Qlev : ℝ) (tau : ℕ → ℝ)
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
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (htau : ∑ n ∈ (Finset.range (maxDepth (twinA1SieveW Qm a x P hP hPodd) + 1)).filter
        (fun n => Even n), tau n ≤ C₂)
    (hQlev : 1 ≤ Qlev)
    (hBV : rosserRemainder (twinA1SieveW Qm a x P hP hPodd) (Qlev * D)
        ≤ (x : ℝ) / (Real.log x) ^ 10) :
    (twinA1SieveW Qm a x P hP hPodd).totalMass *
        (Salt.BrunLower.W (twinA1SieveW Qm a x P hP hPodd) *
          (fchain (maxDepth (twinA1SieveW Qm a x P hP hPodd)) (logRatio z D)
            - ε * C₂ * Real.exp 2 * hBJS (logRatio z D)))
      - (x : ℝ) / (Real.log x) ^ 10
    ≤ ∑ n ∈ twinWindow x,
        if n % Qm = a % Qm ∧ Nat.Coprime P (n + 2) then vonMangoldt n else 0 := by
  set s := twinA1SieveW Qm a x P hP hPodd with hs
  -- side conditions for the concrete sieve (instance facts only)
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < z := hPz
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := twinA1_hnu P
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    twinA1_hguard hε hw0 hPodd hPlow
  have htm : 0 ≤ s.totalMass := by
    rw [twinA1SieveW_totalMass]
    exact div_nonneg (Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg) (Nat.cast_nonneg _)
  -- the windowed per-level (hlevel) bound — generic keystone, verbatim
  have hlevel := hlevel_w_lower s z D ε K tau hD hzTop hguard hnu hε.le hKe htau1 hτ0 hτrec
    h4 hStop
  -- assemble to the sifted lower bound at level Qlev·D — generic keystone, verbatim
  have hassembled := linear_sieve_lower_rosser_assembled_final s D z hz2 hzD hzTop htm
    (logRatio z D) ε C₂ Qlev hQlev hε.le tau hlevel htau
  -- rewrite the sifted sum as the AP-restricted A₁ carrier and fold in the BV remainder
  rw [twinA1SieveW_siftedSum] at hassembled
  linarith [hassembled, hBV]

/-- **`twin_A1_lower_B_W` — the sharp (cB) AP-restricted A₁ lower bound** (the
`twin_A1_lower_B` mirror).  Numeric τ-layer discharged at the FREEZE-V2 boundary-padded
coefficients; single per-step slot `hstepWPC` + contraction gate `ε < 1/249`; the H4C
conditioned `h4`.  Slack constant `CsharpB ε`. -/
theorem twin_A1_lower_B_W (Qm a x z D P : ℕ) (ε K Qlev : ℝ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPz : ∀ p ∈ P.primeFactors, p < z)
    (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ))
    (hz2 : 2 ≤ z) (hzD : z ≤ D) (hD : 1 ≤ D)
    (hStop : 2 ≤ logRatio z D)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hKe : K ≤ 1 + ε)
    (hε49B : ε < 1 / 249)
    (hstepWPC : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε))
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hQlev : 1 ≤ Qlev)
    (hBV : rosserRemainder (twinA1SieveW Qm a x P hP hPodd) (Qlev * D)
        ≤ (x : ℝ) / (Real.log x) ^ 10) :
    (twinA1SieveW Qm a x P hP hPodd).totalMass *
        (Salt.BrunLower.W (twinA1SieveW Qm a x P hP hPodd) *
          (fchain (maxDepth (twinA1SieveW Qm a x P hP hPodd)) (logRatio z D)
            - ε * CsharpB ε * Real.exp 2 * hBJS (logRatio z D)))
      - (x : ℝ) / (Real.log x) ^ 10
    ≤ ∑ n ∈ twinWindow x,
        if n % Qm = a % Qm ∧ Nat.Coprime P (n + 2) then vonMangoldt n else 0 := by
  set s := twinA1SieveW Qm a x P hP hPodd with hs
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < z := hPz
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := twinA1_hnu P
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    twinA1_hguard hε hw0 hPodd hPlow
  have htm : 0 ≤ s.totalMass := by
    rw [twinA1SieveW_totalMass]
    exact div_nonneg (Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg) (Nat.cast_nonneg _)
  -- THE PORT: the CONDITIONED windowed per-level bound at the B-coefficients (as in
  -- `twin_A1_lower_B`; only remaining per-step obligation is `hstepWPC`)
  have hlevel := hlevel_wpc_lower s z D ε K (fun n => cfSharpB n ε) (fun _ => chSharpB ε)
    (tauSharpB ε) hD hzTop hguard hnu hε.le hKe (tauSharpB_one ε) (tauSharpB_nonneg hε.le)
    hstepWPC (fun n => tauSharpB_hτrec n) h4 hStop
  have hassembled := linear_sieve_lower_rosser_assembled_final s D z hz2 hzD hzTop htm
    (logRatio z D) ε (CsharpB ε) Qlev hQlev hε.le (tauSharpB ε) hlevel
    (tauSharpB_sum_even_le hε.le hε49B (maxDepth s + 1))
  rw [twinA1SieveW_siftedSum] at hassembled
  linarith [hassembled, hBV]

/-! ## Part D — the BV discharge mirror (`twinA1_hBV_W`)

The a-fortiori route (D3, gate surface 6): each `|rem d|` sits at modulus `Q·d`; the injection
`d ↦ Q·d` places the whole family inside the BV index range `Icc 1 ⌊√x/(log x)^B⌋₊` under the
W-LEVEL row, and `dispDisc ≥ 0` pays for the over-count.  The conversion sum re-proves with
`ω(Q·d) ≤ ω(Q) + ω(d)` and `φ(Q·d) ≥ φ(d)`. -/

/-- **The W split.**  The Rosser remainder of the AP-restricted sieve is bounded termwise —
via `twinA1W_abs_rem_le` at the CRT class `crtClass Q a d` (UNIFORM in `d ∣ P`, including
`d = 1` = the mod-`Q` SW row) — by the two endpoint `dispDisc` sums at moduli `Q·d` plus the
conversion sum. -/
lemma rosserRemainderW_le_split (Q a x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (hQ1 : 1 ≤ Q)
    (hQa : Nat.Coprime Q a) (hQP : Nat.Coprime Q P) (hx : 4 ≤ x) (bound : ℝ) :
    rosserRemainder (twinA1SieveW Q a x P hP hPodd) bound
      ≤ (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc (x - 2) (Q * d) else 0)
        + (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc (x / 2 - 1) (Q * d) else 0)
        + (∑ d ∈ P.divisors, if (d : ℝ) < bound then convTerm x (Q * d) else 0) := by
  rw [rosserRemainder]
  simp only [twinA1SieveW_prodPrimes]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hQd : Nat.Coprime Q d :=
    Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hd) hQP
  by_cases hlt : (d : ℝ) < bound
  · simp only [if_pos hlt]
    have hcQ := crtClass_mod_left Q a d hQd
    have hcd := crtClass_mod_right Q a d hQd
    have hccop : Nat.Coprime (Q * d) (crtClass Q a d hQd) :=
      crt_class_coprime (divisor_cases hP hPodd hd) hQa hcQ hcd
    exact twinA1W_abs_rem_le Q a x P hP hPodd hQ1 hdpos hQd hx hcQ hcd hccop
  · simp only [if_neg hlt]
    have h1 := dispDisc_nonneg (x - 2) (Q * d)
    have h2 := dispDisc_nonneg (x / 2 - 1) (Q * d)
    have h3 := convTerm_nonneg x (Q * d)
    linarith

/-- **The a-fortiori BV subset sum** (the injection `d ↦ Q·d`).  When `Q·bound ≤ M`, the
level-restricted divisor sum of `dispDisc y (Q·d)` is `≤` the full BV sum over `Icc 1 ⌊M⌋₊`:
`d ↦ Q·d` is injective, the image lies in the range (`Q·d ≤ Q·bound ≤ M`), and
`dispDisc ≥ 0` pays for the over-count. -/
lemma dispDiscW_filtered_le_Icc {P : ℕ} (Q y : ℕ) (hQ1 : 1 ≤ Q) {bound M : ℝ}
    (hlevel : (Q : ℝ) * bound ≤ M) :
    (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc y (Q * d) else 0)
      ≤ ∑ q ∈ Finset.Icc 1 ⌊M⌋₊, dispDisc y q := by
  rw [← Finset.sum_filter]
  have hQpos : 0 < Q := by omega
  have hinj : ∀ d₁ ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < bound),
      ∀ d₂ ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < bound), Q * d₁ = Q * d₂ → d₁ = d₂ :=
    fun d₁ _ d₂ _ h => Nat.eq_of_mul_eq_mul_left hQpos h
  calc ∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < bound), dispDisc y (Q * d)
      = ∑ q ∈ (P.divisors.filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
          dispDisc y q := (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊M⌋₊, dispDisc y q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rw [Finset.mem_image] at hq
          obtain ⟨d, hd, rfl⟩ := hq
          rw [Finset.mem_filter] at hd
          obtain ⟨hdmem, hdlt⟩ := hd
          have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
          rw [Finset.mem_Icc]
          refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
          apply Nat.le_floor
          have hcast : ((Q * d : ℕ) : ℝ) = (Q : ℝ) * (d : ℝ) := by push_cast; ring
          rw [hcast]
          calc (Q : ℝ) * (d : ℝ)
              ≤ (Q : ℝ) * bound :=
                mul_le_mul_of_nonneg_left (le_of_lt hdlt) (by positivity)
            _ ≤ M := hlevel
        · intro q _ _
          exact dispDisc_nonneg y q

/-- **The W conversion sum bound.**  `Σ_{d∣P, d<bound} convTerm x (Q·d)
≤ 2·log x·(ω(Q) + log bound/log 3)·Σ_{d∣P} 1/φ(d)`.  Per divisor: `ω(Q·d) ≤ ω(Q) + ω(d)`
(union of prime supports) with `ω(d) ≤ log bound/log 3` as landed, and `φ(Q·d) = φ(Q)·φ(d)
≥ φ(d)` (the `1/φ(Q)` is given away — it is a constant win, not needed). -/
lemma convSumW_le {x P : ℕ} (Q : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (hQ1 : 1 ≤ Q) (hQP : Nat.Coprime Q P)
    (hx : 4 ≤ x) {bound : ℝ} (hb1 : 1 ≤ bound) :
    (∑ d ∈ P.divisors, if (d : ℝ) < bound then convTerm x (Q * d) else 0)
      ≤ 2 * Real.log x * ((Q.primeFactors.card : ℝ) + Real.log bound / Real.log 3)
          * (∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)) := by
  have hlogx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogb : 0 ≤ Real.log bound := Real.log_nonneg hb1
  have hlogb3 : 0 ≤ Real.log bound / Real.log 3 := by positivity
  have hωQ : (0 : ℝ) ≤ (Q.primeFactors.card : ℝ) := by positivity
  have hWb : 0 ≤ (Q.primeFactors.card : ℝ) + Real.log bound / Real.log 3 := by linarith
  have hfac0 : 0 ≤ 2 * Real.log x
      * ((Q.primeFactors.card : ℝ) + Real.log bound / Real.log 3) := by
    have h2lx : 0 ≤ 2 * Real.log x := by positivity
    exact mul_nonneg h2lx hWb
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdvd : d ∣ P := Nat.dvd_of_mem_divisors hd
  have hdsq : Squarefree d := hP.squarefree_of_dvd hdvd
  have hd3 : ∀ p ∈ d.primeFactors, 3 ≤ p := fun p hp =>
    hPodd p (Nat.primeFactors_mono hdvd hP.ne_zero hp)
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hQd : Nat.Coprime Q d := Nat.Coprime.coprime_dvd_right hdvd hQP
  have hφd : (0 : ℝ) < (d.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hdpos
  have hφQd : (0 : ℝ) < ((Q * d).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos (by omega) hdpos)
  by_cases hlt : (d : ℝ) < bound
  · rw [if_pos hlt]
    -- ω(Q·d) ≤ ω(Q) + ω(d) ≤ ω(Q) + log bound / log 3
    have homega_d : (d.primeFactors.card : ℝ) ≤ Real.log bound / Real.log 3 := by
      calc (d.primeFactors.card : ℝ)
          ≤ Real.log d / Real.log 3 := omega_le_log_div hdsq hd3
        _ ≤ Real.log bound / Real.log 3 :=
            (div_le_div_iff_of_pos_right hlog3).mpr
              (Real.log_le_log (by exact_mod_cast hdpos) (le_of_lt hlt))
    have homega : ((Q * d).primeFactors.card : ℝ)
        ≤ (Q.primeFactors.card : ℝ) + Real.log bound / Real.log 3 := by
      have hsplit : (Q * d).primeFactors.card ≤ Q.primeFactors.card + d.primeFactors.card := by
        rw [Nat.primeFactors_mul (by omega : Q ≠ 0) (by omega : d ≠ 0)]
        exact Finset.card_union_le _ _
      have hcast : ((Q * d).primeFactors.card : ℝ)
          ≤ (Q.primeFactors.card : ℝ) + (d.primeFactors.card : ℝ) := by
        exact_mod_cast hsplit
      linarith [homega_d]
    have hL2 : 0 ≤ Real.log ((x - 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hL3 : 0 ≤ Real.log ((x / 2 - 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hlx2 : Real.log ((x - 2 : ℕ) : ℝ) ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < x - 2))
        (by exact_mod_cast (by omega : x - 2 ≤ x))
    have hlx3 : Real.log ((x / 2 - 1 : ℕ) : ℝ) ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < x / 2 - 1))
        (by exact_mod_cast (by omega : x / 2 - 1 ≤ x))
    have hnum : ((Q * d).primeFactors.card : ℝ) * Real.log ((x - 2 : ℕ) : ℝ)
          + ((Q * d).primeFactors.card : ℝ) * Real.log ((x / 2 - 1 : ℕ) : ℝ)
        ≤ 2 * Real.log x * ((Q.primeFactors.card : ℝ) + Real.log bound / Real.log 3) := by
      have hm1 := mul_le_mul homega hlx2 hL2 hWb
      have hm2 := mul_le_mul homega hlx3 hL3 hWb
      nlinarith [hm1, hm2]
    -- φ(d) ≤ φ(Q·d)
    have hφle : (d.totient : ℝ) ≤ ((Q * d).totient : ℝ) := by
      have hle : d.totient ≤ (Q * d).totient := by
        rw [Nat.totient_mul hQd]
        exact Nat.le_mul_of_pos_left _ (Nat.totient_pos.mpr (by omega))
      exact_mod_cast hle
    calc convTerm x (Q * d)
        = (((Q * d).primeFactors.card : ℝ) * Real.log ((x - 2 : ℕ) : ℝ)
            + ((Q * d).primeFactors.card : ℝ) * Real.log ((x / 2 - 1 : ℕ) : ℝ))
            / ((Q * d).totient : ℝ) := by
          unfold convTerm; ring
      _ ≤ (2 * Real.log x * ((Q.primeFactors.card : ℝ) + Real.log bound / Real.log 3))
            / ((Q * d).totient : ℝ) :=
          (div_le_div_iff_of_pos_right hφQd).mpr hnum
      _ ≤ (2 * Real.log x * ((Q.primeFactors.card : ℝ) + Real.log bound / Real.log 3))
            / (d.totient : ℝ) :=
          div_le_div_of_nonneg_left hfac0 hφd hφle
      _ = 2 * Real.log x * ((Q.primeFactors.card : ℝ) + Real.log bound / Real.log 3)
            * (1 / (d.totient : ℝ)) := by ring
  · rw [if_neg hlt]
    exact mul_nonneg hfac0 (by positivity)

/-- **A1W — the W BV discharge** (`twinA1_hBV` mirrored through the `d ↦ Q·d` a-fortiori).
Instantiating the unconditional BV keystone `psi_BV_of_siegelWalfisz'` at saving `11`, the
Rosser remainder of the AP-restricted `A₁` sieve is `≤ x/(log x)^10`, given the two NAMED
GLU-2W rows (module header):

* the **W-LEVEL row** `(Q : ℝ)·(Qlev·D) ≤ √x/(log x)^B` — the landed C2c level row with one
  extra `Q ≤ 4^{w₀} ≤ log x` factor (gate C2 tower);
* the **W-CLOSE row** `C·x/L¹¹ + C·x/L¹¹ + 2L·(ω(Q) + log(Qlev·D)/log 3)·((1+ε)·log z/log w₀)
  ≤ x/L¹⁰` — the landed close row with the constant `ω(Q)` summand in the conversion factor.

Both hold at the frozen operating point for `x ≥ x₀(B, C)` (GLU-2W discharges them after
destructuring this existential, exactly as the landed GLU does for `twinA1_hBV`). -/
theorem twinA1_hBV_W (Qm a x z D P : ℕ) (ε Qlev : ℝ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPz : ∀ p ∈ P.primeFactors, p < z)
    (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ))
    (hx : 4 ≤ x) (hε : 0 < ε) (hw0 : 3 ≤ w0R ε)
    (hwz : w0R ε ≤ (z : ℝ)) (hQm1 : 1 ≤ Qm) (hQmP : Nat.Coprime Qm P)
    (hQma : Nat.Coprime Qm a) (hQlev : 1 ≤ Qlev) (hD : 1 ≤ D) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ( (Qm : ℝ) * (Qlev * D) ≤ Real.sqrt (x : ℝ) / (Real.log x) ^ B →
        C * (x : ℝ) / (Real.log x) ^ (11 : ℝ) + C * (x : ℝ) / (Real.log x) ^ (11 : ℝ)
          + 2 * Real.log x
              * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * D) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
          ≤ (x : ℝ) / (Real.log x) ^ 10 →
        rosserRemainder (twinA1SieveW Qm a x P hP hPodd) (Qlev * D)
          ≤ (x : ℝ) / (Real.log x) ^ 10 ) := by
  obtain ⟨B, C, hB, hC, hbv⟩ :=
    psi_BV_of_siegelWalfisz' Salt.SW.siegelWalfisz_holds 11 (by norm_num)
  refine ⟨B, C, hB, hC, fun hlevel hclose => ?_⟩
  have hx2 : 2 ≤ x := by omega
  -- the split into two Q·d-modulus BV sums + the conversion sum
  have hsplit := rosserRemainderW_le_split Qm a x P hP hPodd hQm1 hQma hQmP hx
    (Qlev * (D : ℝ))
  -- the two dispDisc endpoint sums: image under d ↦ Qm·d ⊆ BV index set, then the BV bound
  have hbv1 := hbv x (x - 2) hx2 (by omega : x - 2 ≤ x)
  have hbv2 := hbv x (x / 2 - 1) hx2 (by omega : x / 2 - 1 ≤ x)
  have hS1 : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then dispDisc (x - 2) (Qm * d) else 0)
      ≤ C * x / (Real.log x) ^ (11 : ℝ) :=
    le_trans (dispDiscW_filtered_le_Icc Qm (x - 2) hQm1 hlevel) hbv1
  have hS2 : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then dispDisc (x / 2 - 1) (Qm * d) else 0)
      ≤ C * x / (Real.log x) ^ (11 : ℝ) :=
    le_trans (dispDiscW_filtered_le_Icc Qm (x / 2 - 1) hQm1 hlevel) hbv2
  -- the `∑ 1/φ(d)` bound via the V-ratio product (C1d, at the W instance — `nu` is defeq)
  have hb1 : (1 : ℝ) ≤ Qlev * (D : ℝ) := by
    have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    nlinarith [hQlev, hD1]
  have hMbound : ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      ≤ (1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε) := by
    have hvr := vratio_prod_le (twinA1SieveW Qm a x P hP hPodd) P.primeFactors hε.le hw0 hwz
      (w0R_threshold hε) (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hPlow p hp,
        by exact_mod_cast hPz p hp, twinA1_hnu P p hp⟩)
    exact le_trans (sum_inv_totient_le_Winv hP hPodd) hvr
  -- the conversion sum
  have hlogQD : 0 ≤ Real.log (Qlev * (D : ℝ)) := Real.log_nonneg hb1
  have hconvfac : 0 ≤ 2 * Real.log x
      * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3) := by
    have h0 : 0 ≤ Real.log x := Real.log_natCast_nonneg x
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hq : 0 ≤ Real.log (Qlev * (D : ℝ)) / Real.log 3 := div_nonneg hlogQD h3.le
    have hω : (0 : ℝ) ≤ (Qm.primeFactors.card : ℝ) := by positivity
    have hsum : 0 ≤ (Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3 := by
      linarith
    exact mul_nonneg (by positivity) hsum
  have hConv : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then convTerm x (Qm * d) else 0)
      ≤ 2 * Real.log x
          * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3)
          * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε)) :=
    le_trans (convSumW_le Qm hP hPodd hQm1 hQmP hx hb1)
      (mul_le_mul_of_nonneg_left hMbound hconvfac)
  -- assemble
  linarith [hsplit, hS1, hS2, hConv, hclose]

/-! ## Part E — the Finding-6 prime-power bridge (D6)

`twin_A1_lower_(B_)W` lower-bounds the AP-restricted coprime `Λ`-sum; `A1primeSumW` carries
the additional `[n prime]` restriction (`keepW`).  The gap is the window `Λ`-mass on
non-prime prime powers, `≤ √x·(log₂ x)·log x`. -/

/-- Every non-prime prime power `n = p^k` in the window decomposes with `p = minFac n ≤ √x`
and `k = v_p(n) ∈ [2, log₂ x]`, and is reconstructed by `(minFac n)^{v_p(n)} = n` — the
injection underlying the prime-power count. -/
lemma primePow_decomp {x n : ℕ} (hx : 4 ≤ x) (hn : n ∈ twinWindow x) (hnp : ¬ n.Prime)
    (hpp : IsPrimePow n) :
    n.minFac ∈ Finset.Icc 2 (Nat.sqrt x) ∧
      n.factorization n.minFac ∈ Finset.Icc 2 (Nat.log 2 x) ∧
      n.minFac ^ n.factorization n.minFac = n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  have hmf : (p ^ k).minFac = p := hp.pow_minFac (by omega)
  have hfac : (p ^ k).factorization p = k := Nat.factorization_pow_self hp
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · exfalso
      have hk1 : k = 1 := by omega
      subst hk1
      rw [pow_one] at hnp
      exact hnp hp
    · exact hge
  rw [twinWindow, Finset.mem_Icc] at hn
  have hnx : p ^ k ≤ x := by omega
  have hpsq : p ≤ Nat.sqrt x := by
    rw [Nat.le_sqrt']
    calc p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
      _ ≤ x := hnx
  have hklog : k ≤ Nat.log 2 x := by
    have h2k : 2 ^ k ≤ x := le_trans (Nat.pow_le_pow_left hp.two_le k) hnx
    exact (Nat.le_log_iff_pow_le one_lt_two (by omega : x ≠ 0)).mpr h2k
  rw [hmf, hfac]
  exact ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpsq⟩, Finset.mem_Icc.mpr ⟨hk2, hklog⟩, rfl⟩

/-- **Finding 6 — the window prime-power mass.**  The `Λ`-mass of non-prime window points is
`≤ √x·(log₂ x)·log x`: `Λ` is supported on prime powers, a non-prime one is `p^k` with
`p ≤ √x`, `2 ≤ k ≤ log₂ x` (an injective address into `[2,√x] × [2,log₂x]`), and each
carries `Λ = log p ≤ log x`. -/
theorem primePowerMass_le {x : ℕ} (hx : 4 ≤ x) :
    ∑ n ∈ twinWindow x, (if ¬ n.Prime then vonMangoldt n else 0)
      ≤ Real.sqrt x * (Nat.log 2 x : ℝ) * Real.log x := by
  classical
  set T := (twinWindow x).filter (fun n => ¬ n.Prime ∧ IsPrimePow n) with hT
  have hlogx0 : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  -- the sum concentrates on T (Λ vanishes off prime powers)
  have hsum_eq : ∑ n ∈ twinWindow x, (if ¬ n.Prime then vonMangoldt n else 0)
      = ∑ n ∈ T, vonMangoldt n := by
    rw [← Finset.sum_filter]
    have hstep : ((twinWindow x).filter (fun n => ¬ n.Prime)).filter
        (fun n => IsPrimePow n) = T := by
      rw [hT, Finset.filter_filter]
    rw [← hstep]
    exact (Finset.sum_filter_of_ne (fun n _ h => vonMangoldt_ne_zero_iff.mp h)).symm
  -- termwise Λ ≤ log x
  have hterm : ∀ n ∈ T, vonMangoldt n ≤ Real.log x := by
    intro n hn
    rw [hT, Finset.mem_filter] at hn
    obtain ⟨hnw, -, hpp⟩ := hn
    rw [twinWindow, Finset.mem_Icc] at hnw
    have h2n : 2 ≤ n := hpp.two_le
    have hnx : n ≤ x := by omega
    exact le_trans vonMangoldt_le_log
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnx))
  -- the count: inject into [2, √x] × [2, log₂ x]
  have hcard_nat : T.card
      ≤ (Finset.Icc 2 (Nat.sqrt x) ×ˢ Finset.Icc 2 (Nat.log 2 x)).card := by
    apply Finset.card_le_card_of_injOn (fun n => (n.minFac, n.factorization n.minFac))
    · intro n hn
      simp only [Finset.mem_coe] at hn ⊢
      rw [Finset.mem_filter] at hn
      obtain ⟨hnw, hnp, hpp⟩ := hn
      obtain ⟨hp1, hp2, -⟩ := primePow_decomp hx hnw hnp hpp
      exact Finset.mem_product.mpr ⟨hp1, hp2⟩
    · intro n₁ h₁ n₂ h₂ heq
      simp only [Finset.mem_coe] at h₁ h₂
      rw [Finset.mem_filter] at h₁ h₂
      obtain ⟨hnw₁, hnp₁, hpp₁⟩ := h₁
      obtain ⟨hnw₂, hnp₂, hpp₂⟩ := h₂
      obtain ⟨-, -, hrec₁⟩ := primePow_decomp hx hnw₁ hnp₁ hpp₁
      obtain ⟨-, -, hrec₂⟩ := primePow_decomp hx hnw₂ hnp₂ hpp₂
      have hfst : n₁.minFac = n₂.minFac := congrArg Prod.fst heq
      have hsnd : n₁.factorization n₁.minFac = n₂.factorization n₂.minFac :=
        congrArg Prod.snd heq
      rw [← hrec₁, ← hrec₂, hsnd, hfst]
  have hcard2 : T.card ≤ Nat.sqrt x * Nat.log 2 x := by
    refine le_trans hcard_nat ?_
    rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hcardR : (T.card : ℝ) ≤ Real.sqrt x * (Nat.log 2 x : ℝ) := by
    calc (T.card : ℝ) ≤ (Nat.sqrt x : ℝ) * (Nat.log 2 x : ℝ) := by exact_mod_cast hcard2
      _ ≤ Real.sqrt x * (Nat.log 2 x : ℝ) :=
          mul_le_mul_of_nonneg_right Real.nat_sqrt_le_real_sqrt (by positivity)
  -- assemble
  calc ∑ n ∈ twinWindow x, (if ¬ n.Prime then vonMangoldt n else 0)
      = ∑ n ∈ T, vonMangoldt n := hsum_eq
    _ ≤ T.card • Real.log x := Finset.sum_le_card_nsmul T _ _ hterm
    _ = (T.card : ℝ) * Real.log x := by rw [nsmul_eq_mul]
    _ ≤ Real.sqrt x * (Nat.log 2 x : ℝ) * Real.log x :=
        mul_le_mul_of_nonneg_right hcardR hlogx0

/-- **The Finding-6 bridge into W-SURG's `hA1` carrier.**  The supplier's AP-restricted
coprime `Λ`-sum, minus the prime-power mass `√x·(log₂ x)·log x`, lower-bounds `A1primeSumW`
(whose `keepW` carries the `[n prime]` restriction): on prime window points the two agree,
and the discrepancy is supported on non-prime prime powers. -/
theorem A1primeSumW_bridge (Q a x P : ℕ) (hx : 4 ≤ x) :
    (∑ n ∈ twinWindow x, if n % Q = a % Q ∧ Nat.Coprime P (n + 2) then vonMangoldt n else 0)
      - Real.sqrt x * (Nat.log 2 x : ℝ) * Real.log x
    ≤ A1primeSumW Q a x P := by
  have hpt : ∀ n ∈ twinWindow x,
      (if n % Q = a % Q ∧ Nat.Coprime P (n + 2) then vonMangoldt n else 0)
        - vonMangoldt n * keepW Q a P n
      ≤ (if ¬ n.Prime then vonMangoldt n else 0) := by
    intro n _
    have hite0 : 0 ≤ (if ¬ n.Prime then vonMangoldt n else 0) := by
      split_ifs <;> simp [vonMangoldt_nonneg]
    by_cases hk : n % Q = a % Q ∧ Nat.Coprime P (n + 2)
    · rw [if_pos hk]
      by_cases hp : n.Prime
      · have hkeep : keepW Q a P n = 1 := keepW_eq_one_iff.mpr ⟨hp, hk.2, hk.1⟩
        rw [hkeep, mul_one, sub_self]
        exact hite0
      · have hkeep : keepW Q a P n = 0 := by
          unfold keepW
          rw [if_neg (by rintro ⟨hp', -, -⟩; exact hp hp')]
        rw [hkeep, mul_zero, sub_zero, if_pos hp]
    · rw [if_neg hk]
      have h0 : 0 ≤ vonMangoldt n * keepW Q a P n :=
        mul_nonneg vonMangoldt_nonneg (keepW_nonneg Q a P n)
      linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib] at hsum
  have hmass := primePowerMass_le hx
  have hA1 : ∑ n ∈ twinWindow x, vonMangoldt n * keepW Q a P n = A1primeSumW Q a x P := rfl
  rw [hA1] at hsum
  linarith [hsum, hmass]

/-! ## Part F — the `hA1`-slot chain (deliverables 3 + 4 + 5 composed)

The `example` below #checks the full chain into W-SURG's `hA1` slot shape
(`mainA1 ≤ A1primeSumW Q a x P` at a CONCRETE `mainA1`):

* deliverable 4 (`twinA1_hBV_W`) discharges the `hBV` row, given the two named GLU-2W rows
  (taken here in the honest `∀ B C ≥ 0` form — GLU-2W picks `x₀ = x₀(B, C)` AFTER
  destructuring the existential, exactly the Finding-4 pattern);
* deliverable 3 (`twin_A1_lower_B_W`) lower-bounds the AP-restricted coprime `Λ`-sum;
* deliverable 5 (`A1primeSumW_bridge`) folds in the Finding-6 prime-power mass.

The concrete `mainA1` is
`totalMassW·(W·(fchain − ε·CsharpB·e²·hBJS)) − x/L¹⁰ − √x·(log₂x)·log x`. -/

-- the slot shape this example instantiates (W-SURG, Assembly Part K):
--   `hA1 : mainA1 ≤ A1primeSumW Q a x P`
-- #check @Salt.Chen.chen_of_hypotheses_W  -- the H_W consumer (Assembly)
-- #check @Salt.Chen.twin_A1_lower_B_W     -- deliverable 3 (this file)
-- #check @Salt.Chen.twinA1_hBV_W          -- deliverable 4 (this file)
-- #check @Salt.Chen.A1primeSumW_bridge    -- deliverable 5 (this file)

example (Qm a x z D P : ℕ) (ε K Qlev : ℝ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPz : ∀ p ∈ P.primeFactors, p < z)
    (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ))
    (hz2 : 2 ≤ z) (hzD : z ≤ D) (hD : 1 ≤ D)
    (hStop : 2 ≤ logRatio z D)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hKe : K ≤ 1 + ε)
    (hε49B : ε < 1 / 249)
    (hstepWPC : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε))
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hx : 4 ≤ x) (hwz : w0R ε ≤ (z : ℝ))
    (hQm1 : 1 ≤ Qm) (hQmP : Nat.Coprime Qm P) (hQma : Nat.Coprime Qm a)
    (hQlev : 1 ≤ Qlev)
    -- the two named GLU-2W rows, in the honest ∀-form (x₀ is chosen after B, C emerge):
    (hrows : ∀ B C : ℝ, 0 ≤ B → 0 ≤ C →
      ((Qm : ℝ) * (Qlev * D) ≤ Real.sqrt (x : ℝ) / (Real.log x) ^ B ∧
        C * (x : ℝ) / (Real.log x) ^ (11 : ℝ) + C * (x : ℝ) / (Real.log x) ^ (11 : ℝ)
          + 2 * Real.log x
              * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * D) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
          ≤ (x : ℝ) / (Real.log x) ^ 10)) :
    -- W-SURG's hA1 slot shape at the concrete mainA1:
    (twinA1SieveW Qm a x P hP hPodd).totalMass *
        (Salt.BrunLower.W (twinA1SieveW Qm a x P hP hPodd) *
          (fchain (maxDepth (twinA1SieveW Qm a x P hP hPodd)) (logRatio z D)
            - ε * CsharpB ε * Real.exp 2 * hBJS (logRatio z D)))
      - (x : ℝ) / (Real.log x) ^ 10
      - Real.sqrt x * (Nat.log 2 x : ℝ) * Real.log x
    ≤ A1primeSumW Qm a x P := by
  -- deliverable 4: the BV row
  obtain ⟨B, C, hB, hC, himp⟩ := twinA1_hBV_W Qm a x z D P ε Qlev hP hPodd hPz hPlow
    hx hε hw0 hwz hQm1 hQmP hQma hQlev hD
  obtain ⟨hrow1, hrow2⟩ := hrows B C hB hC
  have hBV := himp hrow1 hrow2
  -- deliverable 3: the supplier lower bound at the AP-restricted coprime Λ-sum
  have hsup := twin_A1_lower_B_W Qm a x z D P ε K Qlev hP hPodd hPz hPlow hz2 hzD hD
    hStop hε hw0 hKe hε49B hstepWPC h4 hQlev hBV
  -- deliverable 5: the Finding-6 prime-power bridge
  have hbridge := A1primeSumW_bridge Qm a x P hx
  linarith [hsup, hbridge]

end Salt.Chen
