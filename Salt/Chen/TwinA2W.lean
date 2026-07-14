/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.TwinA1W

/-!
# A2W′ — the per-prime `A₂` W-instances + the aggregation inputs (H-AMENDMENT 2, C5)

Design: `docs/blueprints/chen.md`, H-AMENDMENT 2 (D1–D8) with the gate corrections C1–C7;
node A2W′ (C5: per-prime instance CONSTRUCTION — the per-prime sub-sieves were never built at
any modulus — plus the two aggregation inputs `hcoef` and `hBVagg` for `twin_A2_upper`).
Pattern source: `Salt/Chen/TwinA1W.lean` (the smooth `totalMass` convention, the
`crtClass`/`apDiscW` machinery, the dispersion injection, the conditioned-`h4` slot).

## The instance (`twinA2SieveW`) — the totalMass convention derivation

The per-prime `A₂` sequence is the A₁ W-instance's sequence further restricted to `p ∣ n+2`
(`p` a prime of the A₂ window `[z, y]`; `p ∉ P` — the sifting primes all lie below `z ≤ p`).
The sieve sifts `d ∣ n + 2` (`d ∣ P`), so `multSum d` is the window `Λ`-mass of the joint
condition `n ≡ a (Q) ∧ p ∣ n+2 ∧ d ∣ n+2`.  At pairwise-coprime `Q, p, d` the CRT mass
heuristic is `ψ-window/(φ(Q)·φ(p)·φ(d))`, so ν-consistency (`nu = nuChen`, `ν(d) = 1/φ(d)`
UNCHANGED) forces the **smooth totalMass**

  `totalMass = (Σ_{n ∈ window} Λ(n)) / (φ(Q)·(p − 1))`

— the C3-(ii) smooth convention at the extra `φ(p) = p − 1` factor, written with the REAL
`(p : ℝ) − 1` so it composes literally with `twin_A2_upper`'s `1/(p−1)` density slot.  With
this convention

  `rem d = multSum d − ν(d)·totalMass = [ψ_AP-window at (Q·p·d, c)] − [ψ-window]/φ(Q·p·d)`

EXACTLY (`twinA2W_rem_eq`): the fused divisor is `p·d` (`gcd(p, d) = 1` — disjoint prime
supports), the CRT class is the `n`-side `c = crtClass Q a (p·d)` (`c ≡ a (Q)`,
`c ≡ p·d − 2 (p·d)`), and `φ(Q·p·d) = φ(Q)·(p−1)·φ(d)` by pairwise coprimality — nothing
extra.  So `rem d` IS the modulus-`(Q·p·d)`-discrepancy-shaped object the gate demanded, and
NO dispersion row is spent on the mass identification: `hcoef` (Part E) is definitional.

## The carrier identification (`omegaPrimeSumW_decomp`) — the A₂ range is `Icc z y`

The landed carrier is `omegaPrimeSumW = Σ_n Λ·keepW·ω_{≤y}(n+2)` with
`omegaLe y m = #{q ∈ primeFactors m : q ≤ y}` — the prime filter is `q ≤ y` (CLOSED at `y`;
the blueprint prose's `[z, y)` is realised downstream by the grid certs, which take any
`yR > y`).  At a kept point the split sifting bridge (`factors_ge_z_of_sift_W`, inputs
`hQfull`/`hPfull'`/`hQa2`) forces every prime factor of `n+2` up to `z`, so the counted
primes are exactly the `p ∈ [z, y]` with `p ∣ n+2`, and Fubini gives

  `omegaPrimeSumW Q a x P y = Σ_{p ∈ (Icc z y).filter Prime} A2pW Q a x P p`,

`A2pW = Σ_n Λ·keepW·1_{p ∣ n+2}` the `p`-restricted keepW `Λ`-sum (the `A2p p` slot).
`A2pW p ≤ siftedSum (twinA2SieveW … p)` (`A2pW_le_siftedSumW`) — dropping keepW's
`[n prime]` restriction is free for an UPPER carrier (`Λ ≥ 0`).

## The supplier application, `hcoef`, and `hBVagg`

* `twin_A2_per_prime_W` = `twin_A2_per_prime_B` at `twinA2SieveW` (instance facts only:
  `htm` from `1 ≤ p`, `hzTop = hPz`, `hguard = twinA1_hguard`, `hnu = twinA1_hnu` — sifting
  primes are `P`'s, all `< z ≤ p`, consistent).  The H4C-conditioned `h4` slot and the
  FREEZE-V2 `hstepWPC` slot are threaded verbatim.
* `twinA2W_hcoef`: `totalMass_p·W_p = Λmass_W·V·(1/(p−1))` — an EQUALITY at the smooth
  conventions, with `Λmass_W = totalMass (twinA1SieveW) = ψ-window/φ(Q)` (the A₁ smooth
  mass) and `V = W(twinA1SieveW) = W(twinA2SieveW)` (same `prodPrimes = P`, same
  `nu = nuChen`, so the `W`-values agree by `rfl` — `twinA2SieveW_W_eq`).  This matches
  `twin_A2_upper`'s `hcoef` slot at the razor scale `X_W^Q = Λmass_W·V`; no residual
  dispersion row.
* `twinA2_hBVagg_W`: the aggregated remainder `Σ_{p ∈ Icc z y prime} rosserRemainder
  (twinA2SieveW … p) (Qlev·⌈Dtot/p⌉) ≤ x/(log x)^10`, by the A1W dispersion-injection
  pattern at `q = Q·(p·d)`: `(p, d) ↦ Q·(p·d)` is injective — `p ≥ z` while `d ∣ P` has all
  primes `< z` (DISJOINT prime supports), so `Q·p·d` determines `(p, d)` by factorization
  (proven in `dispDiscW2_double_le_Icc`) — and the ceiling algebra
  `p·⌈Dtot/p⌉ ≤ Dtot + p ≤ Dtot + y` collapses the per-prime cuts into ONE level row.

### The named GLU-2W obligations created here (the node mandate)

* **W2-LEVEL row**: `(Q : ℝ)·(Qlev·(Dtot + y)) ≤ √x/(log x)^B` — the A1W W-LEVEL row with
  `D ↦ Dtot + y` (the `+ y` is the `⌈Dtot/p⌉`-ceiling cost, absorbed at the operating point
  where `y ≤ Dtot`; `Q ≤ 4^{w₀} ≤ log x` per gate C2).
* **W2-CLOSE row**: `C·x/L¹¹ + C·x/L¹¹ + 2L·(ω(Q) + log(Qlev·(Dtot+y))/log 3)
  ·((1+ε)·log z/log w₀)·(Σ_{p ∈ Icc z y prime} 1/(p−1)) ≤ x/L¹⁰` — the A1W W-CLOSE row with
  ONE extra factor, the aggregated A₂ density mass `Σ_p 1/(p−1)` (GLU-2W bounds it by the
  fixed-window Mertens length — the same `log(log y/log z) + 19/log z + 2` machinery as
  `A2grid_le_envelope`); still polylog against `x/L¹⁰`.
* **`hQmPr : ∀ p ∈ (Icc z y).filter Prime, Coprime Q p`** — `Q`'s primes are `< w₀ ≤ z`;
  GLU-2W derives it from the `Qval` support (the companion of A1W's `hQP`).
* **Per-prime operating rows** `2 ≤ ⌈Dtot/p⌉` and `1 ≤ logRatio z ⌈Dtot/p⌉` on the A₂
  window — the landed C2b/C5 operating-point facts (`s_p ∈ [1, 8/3]`), discharged by GLU-2W
  at the frozen exponents (`z = x^{1/8}`, `y = x^{1/3}`, `Dtot = QD`).

`hQa : Coprime Q a` and `hQP : Coprime Q P` are consumed exactly as in A1W (free at
`a = Q − 1` via `residue_witness'` / derived from `hPlow` respectively).

The final `example` (Part G) composes deliverables 2–5 through `twin_A2_upper` into the
`hA2` slot shape `omegaPrimeSumW Q a x P y ≤ mainA2` at the concrete
`mainA2 = X_W^Q·(A2grid + aggSlack) + x/L¹⁰` — exactly GLU-1's `hrawA2`
(`GlueNormalized.normalized_package`) with `R2 := x/L¹⁰`.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.LS Salt.BV

namespace Salt.Chen

/-! ## Part A — the per-prime W-instance (deliverable 1) -/

/-- **The per-prime AP-restricted twin `A₂` `BoundingSieve`** (H-AMENDMENT 2, C5).  Support =
the shifted values `n + 2` of the doubly-restricted window `{n ∈ [x/2, x−2] : n ≡ a (mod Q),
p ∣ n+2}`, weight `Λ(n)` at `n + 2`, density `ν = nuChen` (UNCHANGED — the AP and `p`-fiber
densities cancel in the ν-ratio), sifting modulus `P` (`p ∉ P`: the sifting primes are
`< z ≤ p`), and the **smooth totalMass** `(Σ_{n ∈ window} Λ(n))/(φ(Q)·(p − 1))` — the module
header's convention, making `rem d` exactly the `(Q·p·d)`-modulus discrepancy
(`twinA2W_rem_eq`). -/
noncomputable def twinA2SieveW (Q a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) : BoundingSieve where
  support := ((twinWindow x).filter (fun n => n % Q = a % Q ∧ p ∣ (n + 2))).image (· + 2)
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun m => vonMangoldt (m - 2)
  weights_nonneg := fun _ => vonMangoldt_nonneg
  totalMass := (∑ n ∈ twinWindow x, vonMangoldt n) / ((Q.totient : ℝ) * ((p : ℝ) - 1))
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _q hq _ => nuChen_pos hq
  nu_lt_one_of_prime := fun q hq hqd =>
    nuChen_lt_one hq (hPodd q (Nat.mem_primeFactors.mpr ⟨hq, hqd, hP.ne_zero⟩))

section FactsW2

@[simp] lemma twinA2SieveW_prodPrimes (Q a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    (twinA2SieveW Q a x P p hP hPodd).prodPrimes = P := rfl

@[simp] lemma twinA2SieveW_nu (Q a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    (twinA2SieveW Q a x P p hP hPodd).nu = nuChen := rfl

@[simp] lemma twinA2SieveW_totalMass (Q a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    (twinA2SieveW Q a x P p hP hPodd).totalMass
      = (∑ n ∈ twinWindow x, vonMangoldt n) / ((Q.totient : ℝ) * ((p : ℝ) - 1)) := rfl

/-- The `W`-value transparency: the per-prime instance carries the SAME sifting data
(`prodPrimes = P`, `nu = nuChen`) as the A₁ W-instance, so the density products agree
definitionally.  This is what makes `hcoef` (Part E) a pure mass identity. -/
lemma twinA2SieveW_W_eq (Q a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    Salt.BrunLower.W (twinA2SieveW Q a x P p hP hPodd)
      = Salt.BrunLower.W (twinA1SieveW Q a x P hP hPodd) := rfl

/-- **`multSum d` = the window `Λ`-mass at the triple condition** `n ≡ a (mod Q)`,
`p ∣ n + 2`, `d ∣ n + 2`. -/
lemma twinA2SieveW_multSum (Q a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) (d : ℕ) :
    (twinA2SieveW Q a x P p hP hPodd).multSum d
      = ∑ n ∈ twinWindow x,
          if (n % Q = a % Q ∧ p ∣ (n + 2)) ∧ d ∣ (n + 2) then vonMangoldt n else 0 := by
  change (∑ m ∈ ((twinWindow x).filter (fun n => n % Q = a % Q ∧ p ∣ (n + 2))).image (· + 2),
      if d ∣ m then vonMangoldt (m - 2) else 0) = _
  rw [Finset.sum_image (fun n₁ _ n₂ _ h => add_left_injective 2 h), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Nat.add_sub_cancel, ite_and]

/-- **`siftedSum` = the per-prime AP-restricted `A₂` carrier** (rfl-level identification):
the `Λ`-weighted count of `n ≡ a (mod Q)` in the window with `p ∣ n+2` and `n + 2` coprime
to `P`. -/
lemma twinA2SieveW_siftedSum (Q a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    (twinA2SieveW Q a x P p hP hPodd).siftedSum
      = ∑ n ∈ twinWindow x,
          if (n % Q = a % Q ∧ p ∣ (n + 2)) ∧ Nat.Coprime P (n + 2)
          then vonMangoldt n else 0 := by
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ ((twinWindow x).filter (fun n => n % Q = a % Q ∧ p ∣ (n + 2))).image (· + 2),
      if Nat.Coprime P m then vonMangoldt (m - 2) else 0) = _
  rw [Finset.sum_image (fun n₁ _ n₂ _ h => add_left_injective 2 h), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Nat.add_sub_cancel, ite_and]

/-- **`rem d`** — the sieve-equation remainder at the smooth per-prime totalMass. -/
lemma twinA2SieveW_rem (Q a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) (d : ℕ) :
    (twinA2SieveW Q a x P p hP hPodd).rem d
      = (∑ n ∈ twinWindow x,
          if (n % Q = a % Q ∧ p ∣ (n + 2)) ∧ d ∣ (n + 2) then vonMangoldt n else 0)
        - nuChen d * ((∑ n ∈ twinWindow x, vonMangoldt n)
            / ((Q.totient : ℝ) * ((p : ℝ) - 1))) := by
  rw [BoundingSieve.rem, twinA2SieveW_multSum, twinA2SieveW_nu, twinA2SieveW_totalMass]

end FactsW2

/-! ## Part B — the `(Q·p·d)`-discrepancy identification

The support restriction and the sifting divisor fuse: `p ∣ n+2 ∧ d ∣ n+2 ↔ p·d ∣ n+2` at
`gcd(p, d) = 1` (disjoint prime supports: `p ≥ z`, `d ∣ P` with primes `< z`).  The A1W
machinery (`crtClass`, `apSumW_eq_psiAP`, `apDiscW_le`) then applies VERBATIM at the fused
divisor `p·d`. -/

/-- The condition fusion: at `gcd(p, d) = 1` the triple condition is the joint AP-class
condition at the single divisor `p·d`. -/
lemma twinA2W_cond_iff {Q a p d : ℕ} (hpd : Nat.Coprime p d) (n : ℕ) :
    ((n % Q = a % Q ∧ p ∣ (n + 2)) ∧ d ∣ (n + 2))
      ↔ (n % Q = a % Q ∧ (p * d) ∣ (n + 2)) := by
  constructor
  · rintro ⟨⟨hm, hpdvd⟩, hddvd⟩
    exact ⟨hm, hpd.mul_dvd_of_dvd_of_dvd hpdvd hddvd⟩
  · rintro ⟨hm, hpddvd⟩
    exact ⟨⟨hm, (dvd_mul_right p d).trans hpddvd⟩, (dvd_mul_left d p).trans hpddvd⟩

/-- **The per-prime W remainder identification** (`twinA1W_rem_eq` at the fused divisor
`p·d`).  With the smooth totalMass, `rem d` is EXACTLY the two-endpoint difference of the
modulus-`(Q·p·d)` discrepancies at the class `c` — the mass identity `ν(d)·totalMass =
(1/φ(d))·ψ-window/(φ(Q)(p−1)) = ψ-window/φ(Q·p·d)` uses `φ(Q·p·d) = φ(Q)·(p−1)·φ(d)`
(pairwise coprime; `φ(p) = p−1` at `p` prime). -/
theorem twinA2W_rem_eq (Q a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) {d c : ℕ}
    (hQ1 : 1 ≤ Q) (hpp : p.Prime) (hd1 : 1 ≤ d) (hpd : Nat.Coprime p d)
    (hQpd : Nat.Coprime Q (p * d)) (hx : 4 ≤ x)
    (hcQ : c % Q = a % Q) (hcd : c % (p * d) = (p * d - 2) % (p * d)) :
    (twinA2SieveW Q a x P p hP hPodd).rem d
      = apDiscW (x - 2) (Q * (p * d)) c - apDiscW (x / 2 - 1) (Q * (p * d)) c := by
  have hppos : 0 < p := hpp.pos
  have hpd1 : 1 ≤ p * d :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rw [twinA2SieveW_rem]
  -- fuse the support condition into the single divisor p·d
  have hfuse : (∑ n ∈ twinWindow x,
        if (n % Q = a % Q ∧ p ∣ (n + 2)) ∧ d ∣ (n + 2) then vonMangoldt n else 0)
      = ∑ n ∈ twinWindow x,
        if n % Q = a % Q ∧ (p * d) ∣ (n + 2) then vonMangoldt n else 0 :=
    Finset.sum_congr rfl (fun n _ => if_congr (twinA2W_cond_iff hpd n) rfl rfl)
  rw [hfuse, twinWindow,
    sum_Icc_window (fun n => if n % Q = a % Q ∧ (p * d) ∣ (n + 2) then vonMangoldt n else 0)
      (x / 2) (x - 2) (by omega) (by omega),
    sum_Icc_window (fun n => vonMangoldt n) (x / 2) (x - 2) (by omega) (by omega)]
  rw [apSumW_eq_psiAP hpd1 hQpd hcQ hcd (x - 2), apSumW_eq_psiAP hpd1 hQpd hcQ hcd (x / 2 - 1)]
  have hpt : ∀ y, (∑ n ∈ Finset.Icc 1 y, vonMangoldt n) = psiTot y := fun _ => rfl
  rw [hpt (x - 2), hpt (x / 2 - 1), apDiscW, apDiscW, nuChen_apply]
  -- the totient algebra: φ(Q·p·d) = φ(Q)·(p−1)·φ(d)
  have hφ : ((Q * (p * d)).totient : ℝ)
      = (Q.totient : ℝ) * (((p : ℝ) - 1) * (d.totient : ℝ)) := by
    rw [Nat.totient_mul hQpd, Nat.totient_mul hpd, Nat.totient_prime hpp]
    push_cast [Nat.cast_sub hpp.one_lt.le]
    ring
  have hQt : (Q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < Q)).ne'
  have hp1ne : ((p : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    linarith
  have hdt : (d.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < d)).ne'
  rw [hφ]
  field_simp
  ring

/-- **The pointwise per-prime (39) bound**: for a reduced class `c` of the fused divisor
`p·d`, `|rem d| ≤ dispDisc(x−2)(Q·p·d) + dispDisc(x/2−1)(Q·p·d) + convTerm x (Q·p·d)` — the
per-divisor input for the aggregated BV discharge. -/
theorem twinA2W_abs_rem_le (Q a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) {d c : ℕ}
    (hQ1 : 1 ≤ Q) (hpp : p.Prime) (hd1 : 1 ≤ d) (hpd : Nat.Coprime p d)
    (hQpd : Nat.Coprime Q (p * d)) (hx : 4 ≤ x)
    (hcQ : c % Q = a % Q) (hcd : c % (p * d) = (p * d - 2) % (p * d))
    (hccop : Nat.Coprime (Q * (p * d)) c) :
    |(twinA2SieveW Q a x P p hP hPodd).rem d|
      ≤ dispDisc (x - 2) (Q * (p * d)) + dispDisc (x / 2 - 1) (Q * (p * d))
        + convTerm x (Q * (p * d)) := by
  have hppos : 0 < p := hpp.pos
  have hQpd1 : 1 ≤ Q * (p * d) := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by omega) (by omega)))
  rw [twinA2W_rem_eq Q a x P p hP hPodd hQ1 hpp hd1 hpd hQpd hx hcQ hcd]
  have h1 := apDiscW_le (x - 2) (Q * (p * d)) c hQpd1 hccop (by omega)
  have h2 := apDiscW_le (x / 2 - 1) (Q * (p * d)) c hQpd1 hccop (by omega)
  have htri : |apDiscW (x - 2) (Q * (p * d)) c - apDiscW (x / 2 - 1) (Q * (p * d)) c|
      ≤ |apDiscW (x - 2) (Q * (p * d)) c| + |apDiscW (x / 2 - 1) (Q * (p * d)) c| :=
    abs_sub _ _
  unfold convTerm
  linarith [htri, h1, h2]

/-! ## Part C — the carrier identification (deliverable 2)

`omegaPrimeSumW = Σ_{p ∈ Icc z y prime} A2pW p`: the Fubini/filter-algebra identity, with
the split sifting bridge paying the lower endpoint `z` (module header: the A₂ range is the
CLOSED `Icc z y`, per the landed `omegaLe`'s `q ≤ y` filter). -/

/-- **The `p`-restricted keepW `Λ`-sum** — the per-prime slice of `omegaPrimeSumW`, and the
`A2p p` slot of `twin_A2_upper`.  Dominated by the per-prime instance's `siftedSum`
(`A2pW_le_siftedSumW`). -/
noncomputable def A2pW (Q a x P p : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepW Q a P n * (if p ∣ (n + 2) then 1 else 0)

/-- **The carrier identification.**  Under the split sifting trio (`hQfull`/`hPfull'`/
`hQa2`), the W-restricted aggregated A₂ carrier decomposes EXACTLY into the per-prime slices
over the A₂ window `Icc z y`: at a kept point every prime factor of `n+2` is `≥ z`
(`factors_ge_z_of_sift_W`), so `omegaLe y (n+2)` counts exactly the primes `p ∈ [z, y]` with
`p ∣ n+2`; Fubini swaps the two sums.  A pure filter-algebra identity — no scale is touched
(the razor compares everything at the same `X_W^Q`). -/
theorem omegaPrimeSumW_decomp {Q a x P y z w' : ℕ}
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2)) :
    omegaPrimeSumW Q a x P y
      = ∑ p ∈ (Finset.Icc z y).filter Nat.Prime, A2pW Q a x P p := by
  unfold omegaPrimeSumW A2pW
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hk : Nat.Prime n ∧ Nat.Coprime P (n + 2) ∧ n % Q = a % Q
  · -- kept point: the split bridge forces the prime factors of n+2 up to z
    have hbr := factors_ge_z_of_sift_W hQfull hPfull' hQa2 hk.2.1 hk.2.2
    rw [← Finset.mul_sum]
    congr 1
    -- ω_{≤y}(n+2) = #{p prime ∈ [z, y] : p ∣ n+2}
    have hset : (n + 2).primeFactors.filter (· ≤ y)
        = ((Finset.Icc z y).filter Nat.Prime).filter (· ∣ (n + 2)) := by
      ext q
      simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hqp, hqd, hne⟩, hqy⟩
        exact ⟨⟨⟨hbr q (Nat.mem_primeFactors.mpr ⟨hqp, hqd, hne⟩), hqy⟩, hqp⟩, hqd⟩
      · rintro ⟨⟨⟨_hzq, hqy⟩, hqp⟩, hqd⟩
        exact ⟨⟨hqp, hqd, by omega⟩, hqy⟩
    rw [Finset.sum_boole, omegaLe, hset]
  · -- discarded point: both sides vanish
    have hkeep0 : keepW Q a P n = 0 := by unfold keepW; rw [if_neg hk]
    simp [hkeep0]

/-- **The prime-restriction drop.**  `A2pW p ≤ siftedSum (twinA2SieveW … p)`: the sieve's
sifted sum carries the same conditions WITHOUT keepW's `[n prime]` restriction; dropping it
is free for an upper-bound carrier (`Λ ≥ 0`). -/
lemma A2pW_le_siftedSumW (Q a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    A2pW Q a x P p ≤ (twinA2SieveW Q a x P p hP hPodd).siftedSum := by
  rw [twinA2SieveW_siftedSum]
  unfold A2pW
  apply Finset.sum_le_sum
  intro n _
  by_cases hk : Nat.Prime n ∧ Nat.Coprime P (n + 2) ∧ n % Q = a % Q
  · have hkeep1 : keepW Q a P n = 1 := keepW_eq_one_iff.mpr hk
    rw [hkeep1, mul_one]
    by_cases hpdvd : p ∣ (n + 2)
    · rw [if_pos hpdvd, mul_one, if_pos ⟨⟨hk.2.2, hpdvd⟩, hk.2.1⟩]
    · rw [if_neg hpdvd, mul_zero]
      split_ifs <;> simp [vonMangoldt_nonneg]
  · have hkeep0 : keepW Q a P n = 0 := by unfold keepW; rw [if_neg hk]
    rw [hkeep0, mul_zero, zero_mul]
    split_ifs <;> simp [vonMangoldt_nonneg]

/-! ## Part D — the per-prime supplier application (deliverable 3) -/

/-- **`twin_A2_per_prime_W`** — `twin_A2_per_prime_B` applied at the per-prime W-instance,
with the instance facts discharged (`htm` from `1 ≤ p`; `hzTop`/`hguard`/`hnu` from the
landed `hPz`/`twinA1_hguard`/`twinA1_hnu` — `prodPrimes = P` and `nu = nuChen`
definitionally; the sifting primes are all `< z ≤ p`, so the `p`-fiber restriction never
touches the sieve).  The H4C-conditioned `h4` slot and the FREEZE-V2 `hstepWPC` slot are
threaded verbatim.  Conclusion: the C5 per-prime shape `siftedSum ≤ M_p·(Fchain (maxDepth)
(logRatio z Dlev) + slack) + rosserRemainder (Qlev·Dlev)`. -/
theorem twin_A2_per_prime_W (Qm a x P p z Dlev : ℕ) (ε K Qlev : ℝ)
    (hP : Squarefree P) (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q)
    (hPz : ∀ q ∈ P.primeFactors, q < z)
    (hPlow : ∀ q ∈ P.primeFactors, w0R ε ≤ (q : ℝ))
    (hp1 : 1 ≤ p) (hD2 : 2 ≤ Dlev) (hQlev : 1 ≤ Qlev)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hKe : K ≤ 1 + ε) (h249 : ε < 1 / 249)
    (hstepWPC : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε))
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio z Dlev) :
    (twinA2SieveW Qm a x P p hP hPodd).siftedSum
      ≤ ((twinA2SieveW Qm a x P p hP hPodd).totalMass
            * Salt.BrunLower.W (twinA2SieveW Qm a x P p hP hPodd))
          * (Fchain (maxDepth (twinA2SieveW Qm a x P p hP hPodd)) (logRatio z Dlev)
              + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio z Dlev))
        + rosserRemainder (twinA2SieveW Qm a x P p hP hPodd) (Qlev * Dlev) := by
  set s := twinA2SieveW Qm a x P p hP hPodd with hs
  have htm : 0 ≤ s.totalMass := by
    rw [hs, twinA2SieveW_totalMass]
    apply div_nonneg (Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg)
    apply mul_nonneg (Nat.cast_nonneg _)
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    linarith
  exact twin_A2_per_prime_B s z Dlev ε K Qlev hD2 htm hQlev hPz
    (twinA1_hguard hε hw0 hPodd hPlow) (twinA1_hnu P) hε.le h249 hKe hstepWPC h4 hStop

/-! ## Part E — `hcoef` (deliverable 4)

At the smooth conventions this is DEFINITIONAL — no dispersion row: `totalMass_p =
Λmass_W·(1/(p−1))` is division algebra, and the `W`-values agree by `rfl`
(`twinA2SieveW_W_eq`).  No GLU-2W obligation is created by this deliverable. -/

/-- **`twinA2W_hcoef` — the density coefficient factorisation** (`twin_A2_upper`'s `hcoef`
slot, at the razor scale `X_W^Q = Λmass_W·V`).  An equality:
`totalMass_p·W_p = (Λmass_W·V)·(1/(p−1))` with `Λmass_W = totalMass (twinA1SieveW)` (the A₁
smooth mass `ψ-window/φ(Q)`) and `V = W(twinA1SieveW)`.  Holds unconditionally — at `p ≤ 1`
both sides carry the same division-by-zero convention. -/
theorem twinA2W_hcoef (Qm a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    (twinA2SieveW Qm a x P p hP hPodd).totalMass
        * Salt.BrunLower.W (twinA2SieveW Qm a x P p hP hPodd)
      ≤ ((twinA1SieveW Qm a x P hP hPodd).totalMass
          * Salt.BrunLower.W (twinA1SieveW Qm a x P hP hPodd)) * (1 / ((p : ℝ) - 1)) := by
  apply le_of_eq
  rw [twinA2SieveW_W_eq, twinA2SieveW_totalMass, twinA1SieveW_totalMass]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ## Part F — the aggregated BV discharge (deliverable 5)

The A1W dispersion-injection pattern extended to `q = Q·(p·d)`.  The pair `(p, d)` is
recovered from `Q·(p·d)` by factorization — `p ≥ z` while `d ∣ P` has all primes `< z`
(disjoint prime supports) — so the map is injective and `dispDisc ≥ 0` pays the over-count.
The ceiling algebra `p·⌈Dtot/p⌉ ≤ Dtot + p ≤ Dtot + y` collapses the per-prime Rosser cuts
`d < Qlev·⌈Dtot/p⌉` into the single W2-LEVEL row (module header). -/

/-- **The per-prime split.**  The Rosser remainder of the per-prime W-instance is bounded
termwise — via `twinA2W_abs_rem_le` at the CRT class `crtClass Q a (p·d)` (UNIFORM in
`d ∣ P`, including `d = 1`) — by the two endpoint `dispDisc` sums at the moduli `Q·(p·d)`
plus the conversion sum. -/
lemma rosserRemainderW2_le_split (Qm a x P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) (hQ1 : 1 ≤ Qm)
    (hQa : Nat.Coprime Qm a) (hQP : Nat.Coprime Qm P) (hQp : Nat.Coprime Qm p)
    (hpp : p.Prime) (hp3 : 3 ≤ p) (hpP : Nat.Coprime p P) (hx : 4 ≤ x) (bound : ℝ) :
    rosserRemainder (twinA2SieveW Qm a x P p hP hPodd) bound
      ≤ (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc (x - 2) (Qm * (p * d)) else 0)
        + (∑ d ∈ P.divisors,
            if (d : ℝ) < bound then dispDisc (x / 2 - 1) (Qm * (p * d)) else 0)
        + (∑ d ∈ P.divisors, if (d : ℝ) < bound then convTerm x (Qm * (p * d)) else 0) := by
  rw [rosserRemainder]
  simp only [twinA2SieveW_prodPrimes]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hQd : Nat.Coprime Qm d :=
    Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hd) hQP
  have hpd : Nat.Coprime p d :=
    Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hd) hpP
  have hQpd : Nat.Coprime Qm (p * d) := Nat.Coprime.mul_right hQp hQd
  by_cases hlt : (d : ℝ) < bound
  · simp only [if_pos hlt]
    have hcQ := crtClass_mod_left Qm a (p * d) hQpd
    have hcd := crtClass_mod_right Qm a (p * d) hQpd
    -- p·d is ≥ 3 and odd (p an odd prime; d odd or 1 by `divisor_cases`)
    have hodd_d : Odd d := by
      rcases divisor_cases hP hPodd hd with rfl | ⟨-, h⟩
      · exact odd_one
      · exact h
    have hodd_p : Odd p := hpp.odd_of_ne_two (by omega)
    have hpd3 : 3 ≤ p * d := le_trans hp3 (Nat.le_mul_of_pos_right p hdpos)
    have hccop : Nat.Coprime (Qm * (p * d)) (crtClass Qm a (p * d) hQpd) :=
      crt_class_coprime (Or.inr ⟨hpd3, hodd_p.mul hodd_d⟩) hQa hcQ hcd
    exact twinA2W_abs_rem_le Qm a x P p hP hPodd hQ1 hpp hdpos hpd hQpd hx hcQ hcd hccop
  · simp only [if_neg hlt]
    have h1 := dispDisc_nonneg (x - 2) (Qm * (p * d))
    have h2 := dispDisc_nonneg (x / 2 - 1) (Qm * (p * d))
    have h3 := convTerm_nonneg x (Qm * (p * d))
    linarith

/-- **The a-fortiori BV double-subset sum** (the injection `(p, d) ↦ Q·(p·d)`).  When every
in-cut pair's modulus lies below `M`, the double sum of `dispDisc y' (Q·(p·d))` is `≤` the
full BV sum over `Icc 1 ⌊M⌋₊`: the map is injective on the cut set — from `Q·(p₁·d₁) =
Q·(p₂·d₂)` cancel `Q`, then `p₁ ∣ p₂·d₂` with `p₁ ∤ d₂` (`d₂ ∣ P` has primes `< z ≤ p₁`)
forces `p₁ = p₂` by primality, hence `d₁ = d₂` — the image lies in the range, and
`dispDisc ≥ 0` pays the over-count. -/
lemma dispDiscW2_double_le_Icc {P z y : ℕ} (Qm y' : ℕ) (hQ1 : 1 ≤ Qm) (hP0 : P ≠ 0)
    (hPz : ∀ q ∈ P.primeFactors, q < z)
    {boundf : ℕ → ℝ} {M : ℝ}
    (hlev : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, ∀ d ∈ P.divisors,
        (d : ℝ) < boundf p → ((Qm * (p * d) : ℕ) : ℝ) ≤ M) :
    (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
        if (d : ℝ) < boundf p then dispDisc y' (Qm * (p * d)) else 0)
      ≤ ∑ q ∈ Finset.Icc 1 ⌊M⌋₊, dispDisc y' q := by
  classical
  set S := (((Finset.Icc z y).filter Nat.Prime) ×ˢ P.divisors).filter
    (fun pd => ((pd.2 : ℕ) : ℝ) < boundf pd.1) with hSdef
  -- membership data for pairs in the cut set
  have hmemS : ∀ pd ∈ S, pd.1.Prime ∧ z ≤ pd.1 ∧ pd.1 ≤ y ∧ pd.2 ∈ P.divisors
      ∧ ((pd.2 : ℕ) : ℝ) < boundf pd.1 := by
    intro pd hpd
    rw [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_filter,
      Finset.mem_Icc] at hpd
    exact ⟨hpd.1.1.2, hpd.1.1.1.1, hpd.1.1.1.2, hpd.1.2, hpd.2⟩
  -- injectivity of (p, d) ↦ Qm·(p·d): disjoint prime supports
  have hinj : ∀ pd₁ ∈ S, ∀ pd₂ ∈ S,
      Qm * (pd₁.1 * pd₁.2) = Qm * (pd₂.1 * pd₂.2) → pd₁ = pd₂ := by
    intro pd₁ h₁ pd₂ h₂ heq
    obtain ⟨hpp₁, hzp₁, -, hd₁, -⟩ := hmemS pd₁ h₁
    obtain ⟨hpp₂, -, -, hd₂, -⟩ := hmemS pd₂ h₂
    have hd₂pos : 0 < pd₂.2 := Nat.pos_of_mem_divisors hd₂
    have hmul : pd₁.1 * pd₁.2 = pd₂.1 * pd₂.2 :=
      Nat.eq_of_mul_eq_mul_left (by omega : 0 < Qm) heq
    have hdvd : pd₁.1 ∣ pd₂.1 * pd₂.2 := hmul ▸ dvd_mul_right pd₁.1 pd₁.2
    have hp12 : pd₁.1 = pd₂.1 := by
      rcases (Nat.Prime.dvd_mul hpp₁).mp hdvd with hp | hd
      · exact (Nat.prime_dvd_prime_iff_eq hpp₁ hpp₂).mp hp
      · exfalso
        have hmem : pd₁.1 ∈ P.primeFactors :=
          Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd₂) hP0
            (Nat.mem_primeFactors.mpr ⟨hpp₁, hd, hd₂pos.ne'⟩)
        have := hPz pd₁.1 hmem
        omega
    have hd12 : pd₁.2 = pd₂.2 := by
      rw [hp12] at hmul
      exact Nat.eq_of_mul_eq_mul_left hpp₂.pos hmul
    exact Prod.ext hp12 hd12
  calc (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
        if (d : ℝ) < boundf p then dispDisc y' (Qm * (p * d)) else 0)
      = ∑ pd ∈ ((Finset.Icc z y).filter Nat.Prime) ×ˢ P.divisors,
          if ((pd.2 : ℕ) : ℝ) < boundf pd.1 then dispDisc y' (Qm * (pd.1 * pd.2)) else 0 :=
        (Finset.sum_product' (s := (Finset.Icc z y).filter Nat.Prime) (t := P.divisors)
          (f := fun p d => if (d : ℝ) < boundf p then dispDisc y' (Qm * (p * d)) else 0)).symm
    _ = ∑ pd ∈ S, dispDisc y' (Qm * (pd.1 * pd.2)) := (Finset.sum_filter _ _).symm
    _ = ∑ q ∈ S.image (fun pd => Qm * (pd.1 * pd.2)), dispDisc y' q :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊M⌋₊, dispDisc y' q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rw [Finset.mem_image] at hq
          obtain ⟨pd, hpd, rfl⟩ := hq
          obtain ⟨hpp, hzp, hpy, hd, hlt⟩ := hmemS pd hpd
          have hdpos : 0 < pd.2 := Nat.pos_of_mem_divisors hd
          have hppos : 0 < pd.1 := hpp.pos
          rw [Finset.mem_Icc]
          refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
            (Nat.mul_ne_zero (by omega) (by omega))), ?_⟩
          apply Nat.le_floor
          exact hlev pd.1
            (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hzp, hpy⟩, hpp⟩) pd.2 hd hlt
        · intro q _ _
          exact dispDisc_nonneg y' q

/-- **The aggregated conversion sum.**  `Σ_{p ∈ Icc z y prime} Σ_{d ∣ P, d < boundf p}
convTerm x (Q·(p·d)) ≤ 2·log x·(ω(Q) + log BND/log 3)·(Σ_d 1/φ(d))·(Σ_p 1/(p−1))`.
Per pair: `ω(Q·p·d) ≤ ω(Q) + ω(p·d)` (union of prime supports) with `ω(p·d) ≤ log(p·d)/log 3
≤ log BND/log 3` (`p·d` squarefree with prime factors `≥ 3`; `p·d ≤ BND` from the cut), and
`φ(Q·p·d) ≥ φ(p·d) = (p−1)·φ(d)` (`φ` is divisibility-monotone; `1/φ(Q)` given away as in
A1W).  The aggregated A₂ density mass `Σ_p 1/(p−1)` is KEPT — it is the same factor as the
A₂ grid mass, Mertens-bounded at GLU-2W. -/
lemma convSumW2_le {x P z y : ℕ} (Qm : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) (hQ1 : 1 ≤ Qm)
    (hPz : ∀ q ∈ P.primeFactors, q < z) (hz3 : 3 ≤ z)
    (hx : 4 ≤ x) {boundf : ℕ → ℝ} {BND : ℝ} (hBND1 : 1 ≤ BND)
    (hpdB : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, ∀ d ∈ P.divisors,
        (d : ℝ) < boundf p → (p : ℝ) * (d : ℝ) ≤ BND) :
    (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
        if (d : ℝ) < boundf p then convTerm x (Qm * (p * d)) else 0)
      ≤ 2 * Real.log x * ((Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3)
          * (∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d))
          * (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1)) := by
  classical
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogB : 0 ≤ Real.log BND := Real.log_nonneg hBND1
  have hωQ : (0 : ℝ) ≤ (Qm.primeFactors.card : ℝ) := by positivity
  have hWb : 0 ≤ (Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3 := by
    have : 0 ≤ Real.log BND / Real.log 3 := by positivity
    linarith
  have hfac0 : 0 ≤ 2 * Real.log x
      * ((Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3) := by
    have h0 : 0 ≤ Real.log x := Real.log_natCast_nonneg x
    exact mul_nonneg (by positivity) hWb
  -- the per-p inner bound (the A1W `convSumW_le` block at the fused divisor p·d)
  have hper : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime,
      (∑ d ∈ P.divisors, if (d : ℝ) < boundf p then convTerm x (Qm * (p * d)) else 0)
        ≤ 2 * Real.log x * ((Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3)
            * (∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)) * (1 / ((p : ℝ) - 1)) := by
    intro p hpR
    have hpR' := hpR
    rw [Finset.mem_filter, Finset.mem_Icc] at hpR'
    obtain ⟨⟨hzp, hpy⟩, hpp⟩ := hpR'
    have hp3 : 3 ≤ p := by omega
    have hppos : 0 < p := by omega
    have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hp1pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hp1inv0 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by positivity
    conv_rhs => rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d hd
    have hdvd : d ∣ P := Nat.dvd_of_mem_divisors hd
    have hdsq : Squarefree d := hP.squarefree_of_dvd hdvd
    have hd3 : ∀ q ∈ d.primeFactors, 3 ≤ q := fun q hq =>
      hPodd q (Nat.primeFactors_mono hdvd hP.ne_zero hq)
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hφd : (0 : ℝ) < (d.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hdpos
    by_cases hlt : (d : ℝ) < boundf p
    · rw [if_pos hlt]
      have hpdpos : 0 < p * d := Nat.mul_pos hppos hdpos
      -- p ∤ d (d's primes < z ≤ p), hence gcd(p, d) = 1 and p·d squarefree
      have hpd : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hpp).mpr (fun hpdvd =>
        absurd (hPz p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.trans hdvd, hP.ne_zero⟩))
          (by omega))
      have hpdsq : Squarefree (p * d) := (Nat.squarefree_mul hpd).mpr ⟨hpp.squarefree, hdsq⟩
      have hpd3 : ∀ q ∈ (p * d).primeFactors, 3 ≤ q := by
        intro q hq
        rw [Nat.primeFactors_mul hppos.ne' hdpos.ne', Finset.mem_union] at hq
        rcases hq with hq | hq
        · rw [hpp.primeFactors, Finset.mem_singleton] at hq
          omega
        · exact hd3 q hq
      -- ω(Qm·(p·d)) ≤ ω(Qm) + log BND / log 3
      have homega_pd : ((p * d).primeFactors.card : ℝ) ≤ Real.log BND / Real.log 3 := by
        calc ((p * d).primeFactors.card : ℝ)
            ≤ Real.log (p * d : ℕ) / Real.log 3 := omega_le_log_div hpdsq hpd3
          _ ≤ Real.log BND / Real.log 3 := by
              apply (div_le_div_iff_of_pos_right hlog3).mpr
              apply Real.log_le_log (by exact_mod_cast hpdpos)
              calc ((p * d : ℕ) : ℝ) = (p : ℝ) * (d : ℝ) := by push_cast; ring
                _ ≤ BND := hpdB p hpR d hd hlt
      have homega : ((Qm * (p * d)).primeFactors.card : ℝ)
          ≤ (Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3 := by
        have hsplit : (Qm * (p * d)).primeFactors.card
            ≤ Qm.primeFactors.card + (p * d).primeFactors.card := by
          rw [Nat.primeFactors_mul (by omega : Qm ≠ 0) hpdpos.ne']
          exact Finset.card_union_le _ _
        have hcast : ((Qm * (p * d)).primeFactors.card : ℝ)
            ≤ (Qm.primeFactors.card : ℝ) + ((p * d).primeFactors.card : ℝ) := by
          exact_mod_cast hsplit
        linarith [homega_pd]
      -- the numerator bound (A1W's block)
      have hL2 : 0 ≤ Real.log ((x - 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
      have hL3 : 0 ≤ Real.log ((x / 2 - 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
      have hlx2 : Real.log ((x - 2 : ℕ) : ℝ) ≤ Real.log x :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < x - 2))
          (by exact_mod_cast (by omega : x - 2 ≤ x))
      have hlx3 : Real.log ((x / 2 - 1 : ℕ) : ℝ) ≤ Real.log x :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < x / 2 - 1))
          (by exact_mod_cast (by omega : x / 2 - 1 ≤ x))
      have hnum : ((Qm * (p * d)).primeFactors.card : ℝ) * Real.log ((x - 2 : ℕ) : ℝ)
            + ((Qm * (p * d)).primeFactors.card : ℝ) * Real.log ((x / 2 - 1 : ℕ) : ℝ)
          ≤ 2 * Real.log x
              * ((Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3) := by
        have hm1 := mul_le_mul homega hlx2 hL2 hWb
        have hm2 := mul_le_mul homega hlx3 hL3 hWb
        nlinarith [hm1, hm2]
      -- φ(Qm·(p·d)) ≥ (p−1)·φ(d): divisibility-monotone φ, then φ(p·d) = (p−1)·φ(d)
      have hφQpd : (0 : ℝ) < ((Qm * (p * d)).totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos (by omega) hpdpos)
      have hφle : ((p : ℝ) - 1) * (d.totient : ℝ) ≤ ((Qm * (p * d)).totient : ℝ) := by
        have h2 : (p * d).totient = (p - 1) * d.totient := by
          rw [Nat.totient_mul hpd, Nat.totient_prime hpp]
        have h1 : (p - 1) * d.totient ≤ (Qm * (p * d)).totient := by
          rw [← h2]
          exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.mul_pos (by omega) hpdpos))
            (Nat.totient_dvd_of_dvd (dvd_mul_left _ _))
        calc ((p : ℝ) - 1) * (d.totient : ℝ) = (((p - 1) * d.totient : ℕ) : ℝ) := by
              push_cast [Nat.cast_sub hpp.one_lt.le]; ring
          _ ≤ ((Qm * (p * d)).totient : ℝ) := by exact_mod_cast h1
      have hden_pos : (0 : ℝ) < ((p : ℝ) - 1) * (d.totient : ℝ) := mul_pos hp1pos hφd
      calc convTerm x (Qm * (p * d))
          = (((Qm * (p * d)).primeFactors.card : ℝ) * Real.log ((x - 2 : ℕ) : ℝ)
              + ((Qm * (p * d)).primeFactors.card : ℝ) * Real.log ((x / 2 - 1 : ℕ) : ℝ))
              / ((Qm * (p * d)).totient : ℝ) := by
            unfold convTerm; ring
        _ ≤ (2 * Real.log x * ((Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3))
              / ((Qm * (p * d)).totient : ℝ) :=
            (div_le_div_iff_of_pos_right hφQpd).mpr hnum
        _ ≤ (2 * Real.log x * ((Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3))
              / (((p : ℝ) - 1) * (d.totient : ℝ)) :=
            div_le_div_of_nonneg_left hfac0 hden_pos hφle
        _ = 2 * Real.log x * ((Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3)
              * (1 / (Nat.totient d : ℝ)) * (1 / ((p : ℝ) - 1)) := by
            rw [div_eq_mul_inv, mul_inv]
            ring
    · rw [if_neg hlt]
      have h1 : (0 : ℝ) ≤ 2 * Real.log x
          * ((Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3)
          * (1 / (Nat.totient d : ℝ)) := mul_nonneg hfac0 (by positivity)
      exact mul_nonneg h1 hp1inv0
  -- aggregate over p and re-associate to the product shape
  calc (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
        if (d : ℝ) < boundf p then convTerm x (Qm * (p * d)) else 0)
      ≤ ∑ p ∈ (Finset.Icc z y).filter Nat.Prime,
          2 * Real.log x * ((Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3)
            * (∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)) * (1 / ((p : ℝ) - 1)) :=
        Finset.sum_le_sum hper
    _ = 2 * Real.log x * ((Qm.primeFactors.card : ℝ) + Real.log BND / Real.log 3)
          * (∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d))
          * (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1)) := by
        conv_rhs => rw [Finset.mul_sum]

/-- **A2W′ — the aggregated W BV discharge** (`twinA1_hBV_W` mirrored through the
`(p, d) ↦ Q·(p·d)` a-fortiori).  Instantiating the unconditional BV keystone
`psi_BV_of_siegelWalfisz'` at saving `11`, the SUM of the per-prime Rosser remainders over
the A₂ window — each at its own level `Qlev·⌈Dtot/p⌉`, the `twin_A2_per_prime_B` cut — is
`≤ x/(log x)^10`, given the two NAMED GLU-2W rows (module header):

* the **W2-LEVEL row** `(Q : ℝ)·(Qlev·(Dtot + y)) ≤ √x/(log x)^B`;
* the **W2-CLOSE row** `C·x/L¹¹ + C·x/L¹¹ + 2L·(ω(Q) + log(Qlev·(Dtot+y))/log 3)
  ·((1+ε)·log z/log w₀)·(Σ_{p ∈ Icc z y prime} 1/(p−1)) ≤ x/L¹⁰`.

Both hold at the frozen operating point for `x ≥ x₀(B, C)` (GLU-2W discharges them after
destructuring this existential, exactly as for `twinA1_hBV_W`). -/
theorem twinA2_hBVagg_W (Qm a x z y Dtot P : ℕ) (ε Qlev : ℝ)
    (hP : Squarefree P) (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q)
    (hPz : ∀ q ∈ P.primeFactors, q < z)
    (hPlow : ∀ q ∈ P.primeFactors, w0R ε ≤ (q : ℝ))
    (hx : 4 ≤ x) (hz3 : 3 ≤ z) (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hwz : w0R ε ≤ (z : ℝ))
    (hQm1 : 1 ≤ Qm) (hQmP : Nat.Coprime Qm P) (hQma : Nat.Coprime Qm a)
    (hQmPr : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, Nat.Coprime Qm p)
    (hQlev : 1 ≤ Qlev) (hD1 : 1 ≤ Dtot) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ( (Qm : ℝ) * (Qlev * ((Dtot : ℝ) + (y : ℝ))) ≤ Real.sqrt (x : ℝ) / (Real.log x) ^ B →
        C * (x : ℝ) / (Real.log x) ^ (11 : ℝ) + C * (x : ℝ) / (Real.log x) ^ (11 : ℝ)
          + 2 * Real.log x
              * ((Qm.primeFactors.card : ℝ)
                  + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
              * (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1))
          ≤ (x : ℝ) / (Real.log x) ^ 10 →
        ∑ p ∈ (Finset.Icc z y).filter Nat.Prime,
            rosserRemainder (twinA2SieveW Qm a x P p hP hPodd) (Qlev * (cdiv Dtot p : ℝ))
          ≤ (x : ℝ) / (Real.log x) ^ 10 ) := by
  obtain ⟨B, C, hB, hC, hbv⟩ :=
    psi_BV_of_siegelWalfisz' Salt.SW.siegelWalfisz_holds 11 (by norm_num)
  refine ⟨B, C, hB, hC, fun hlevel hclose => ?_⟩
  classical
  have hx2 : 2 ≤ x := by omega
  have hQlev0 : (0 : ℝ) ≤ Qlev := by linarith
  -- 1 ≤ BND := Qlev·(Dtot + y)
  have hBND1 : (1 : ℝ) ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
    have hD1R : (1 : ℝ) ≤ (Dtot : ℝ) := by exact_mod_cast hD1
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
    nlinarith [hQlev, hD1R, hy0]
  -- the collapsed level bound: in-cut pairs satisfy p·d ≤ Qlev·(Dtot + y)
  have hpdB : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, ∀ d ∈ P.divisors,
      (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) →
      (p : ℝ) * (d : ℝ) ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
    intro p hpR d _hd hlt
    rw [Finset.mem_filter, Finset.mem_Icc] at hpR
    obtain ⟨⟨_hzp, hpy⟩, hpp⟩ := hpR
    have hppos : 0 < p := hpp.pos
    have hpposR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
    -- ℕ: p·⌈Dtot/p⌉ ≤ Dtot + p
    have hcd : p * cdiv Dtot p ≤ Dtot + p := by
      have h1 : (Dtot - 1) / p * p ≤ Dtot - 1 := Nat.div_mul_le_self _ _
      unfold cdiv
      calc p * ((Dtot - 1) / p + 1) = (Dtot - 1) / p * p + p := by ring
        _ ≤ Dtot + p := by omega
    have hcdR : (p : ℝ) * (cdiv Dtot p : ℝ) ≤ (Dtot : ℝ) + (p : ℝ) := by
      calc (p : ℝ) * (cdiv Dtot p : ℝ) = ((p * cdiv Dtot p : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((Dtot + p : ℕ) : ℝ) := by exact_mod_cast hcd
        _ = (Dtot : ℝ) + (p : ℝ) := by push_cast; ring
    have hpyR : (p : ℝ) ≤ (y : ℝ) := by exact_mod_cast hpy
    calc (p : ℝ) * (d : ℝ)
        ≤ (p : ℝ) * (Qlev * (cdiv Dtot p : ℝ)) :=
          mul_le_mul_of_nonneg_left hlt.le hpposR.le
      _ = Qlev * ((p : ℝ) * (cdiv Dtot p : ℝ)) := by ring
      _ ≤ Qlev * ((Dtot : ℝ) + (p : ℝ)) := mul_le_mul_of_nonneg_left hcdR hQlev0
      _ ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hQlev0
          linarith
  -- the modulus-level bound for the injection
  have hlev' : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, ∀ d ∈ P.divisors,
      (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) →
      ((Qm * (p * d) : ℕ) : ℝ) ≤ Real.sqrt (x : ℝ) / (Real.log x) ^ B := by
    intro p hpR d hd hlt
    have h1 := hpdB p hpR d hd hlt
    have hQm0 : (0 : ℝ) ≤ (Qm : ℝ) := Nat.cast_nonneg _
    calc ((Qm * (p * d) : ℕ) : ℝ) = (Qm : ℝ) * ((p : ℝ) * (d : ℝ)) := by push_cast; ring
      _ ≤ (Qm : ℝ) * (Qlev * ((Dtot : ℝ) + (y : ℝ))) := mul_le_mul_of_nonneg_left h1 hQm0
      _ ≤ Real.sqrt (x : ℝ) / (Real.log x) ^ B := hlevel
  -- the per-prime split, summed
  have hsum : (∑ p ∈ (Finset.Icc z y).filter Nat.Prime,
        rosserRemainder (twinA2SieveW Qm a x P p hP hPodd) (Qlev * (cdiv Dtot p : ℝ)))
      ≤ (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then dispDisc (x - 2) (Qm * (p * d)) else 0)
        + (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then dispDisc (x / 2 - 1) (Qm * (p * d)) else 0)
        + (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then convTerm x (Qm * (p * d)) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hpR
    have hpR' := hpR
    rw [Finset.mem_filter, Finset.mem_Icc] at hpR'
    obtain ⟨⟨hzp, _hpy⟩, hpp⟩ := hpR'
    have hp3 : 3 ≤ p := by omega
    have hpP : Nat.Coprime p P := (Nat.Prime.coprime_iff_not_dvd hpp).mpr (fun hpdvd =>
      absurd (hPz p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, hP.ne_zero⟩)) (by omega))
    exact rosserRemainderW2_le_split Qm a x P p hP hPodd hQm1 hQma hQmP
      (hQmPr p hpR) hpp hp3 hpP hx _
  -- the two dispDisc double sums via the injection + the unconditional BV
  have hbv1 := hbv x (x - 2) hx2 (by omega : x - 2 ≤ x)
  have hbv2 := hbv x (x / 2 - 1) hx2 (by omega : x / 2 - 1 ≤ x)
  have hS1 : (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
        then dispDisc (x - 2) (Qm * (p * d)) else 0)
      ≤ C * x / (Real.log x) ^ (11 : ℝ) :=
    le_trans (dispDiscW2_double_le_Icc Qm (x - 2) hQm1 hP.ne_zero hPz hlev') hbv1
  have hS2 : (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
        then dispDisc (x / 2 - 1) (Qm * (p * d)) else 0)
      ≤ C * x / (Real.log x) ^ (11 : ℝ) :=
    le_trans (dispDiscW2_double_le_Icc Qm (x / 2 - 1) hQm1 hP.ne_zero hPz hlev') hbv2
  -- the conversion double sum, then the `Σ 1/φ(d)` V-ratio bound (the A1W route)
  have hconv := convSumW2_le Qm hP hPodd hQm1 hPz hz3 hx hBND1 hpdB
  have hMbound : ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      ≤ (1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε) := by
    have hvr := vratio_prod_le (twinA1SieveW Qm a x P hP hPodd) P.primeFactors hε.le hw0 hwz
      (w0R_threshold hε) (fun q hq => ⟨Nat.prime_of_mem_primeFactors hq, hPlow q hq,
        by exact_mod_cast hPz q hq, twinA1_hnu P q hq⟩)
    exact le_trans (sum_inv_totient_le_Winv hP hPodd) hvr
  have hSp0 : (0 : ℝ) ≤ ∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1) := by
    apply Finset.sum_nonneg
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hK0 : 0 ≤ 2 * Real.log x
      * ((Qm.primeFactors.card : ℝ)
          + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3) := by
    have h0 : 0 ≤ Real.log x := Real.log_natCast_nonneg x
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hlogB : 0 ≤ Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) := Real.log_nonneg hBND1
    have : 0 ≤ (Qm.primeFactors.card : ℝ)
        + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3 := by positivity
    exact mul_nonneg (by positivity) this
  have hconv2 : (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) then convTerm x (Qm * (p * d)) else 0)
      ≤ 2 * Real.log x
          * ((Qm.primeFactors.card : ℝ)
              + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3)
          * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
          * (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1)) := by
    refine le_trans hconv ?_
    apply mul_le_mul_of_nonneg_right _ hSp0
    exact mul_le_mul_of_nonneg_left hMbound hK0
  linarith [hsum, hS1, hS2, hconv2, hclose]

/-! ## Part G — the `hA2`-slot chain (deliverables 2–5 composed; deliverable 6)

The `example` below #checks the full chain into the `hA2` slot shape
(`omegaPrimeSumW Q a x P y ≤ mainA2` at a CONCRETE `mainA2`), which is simultaneously
GLU-1's `hrawA2` (`mainA2 ≤ X_W^Q·(A2grid + aggSlack) + R2` with `R2 := x/L¹⁰`):

* deliverable 2 (`omegaPrimeSumW_decomp` + `A2pW_le_siftedSumW`) rewrites the carrier as
  the per-prime aggregate and majorizes each slice by the instance `siftedSum`;
* deliverables 1+3 (`twinA2SieveW` + `twin_A2_per_prime_W` at `Dlev := cdiv Dtot p`) supply
  `twin_A2_upper`'s `hper` slot;
* deliverable 4 (`twinA2W_hcoef`) supplies the `hcoef` slot at
  `Λmass·V = X_W^Q = totalMass (twinA1SieveW)·W (twinA1SieveW)`;
* `twin_A2_upper` aggregates to `X_W^Q·(A2grid + aggSlack) + Σ_p R_p`;
* deliverable 5 (`twinA2_hBVagg_W`) bounds `Σ_p R_p ≤ x/L¹⁰` given the two named GLU-2W
  rows (taken in the honest `∀ B C ≥ 0` form — GLU-2W picks `x₀ = x₀(B, C)` AFTER
  destructuring the existential, the Finding-4 pattern).

The concrete `mainA2` is
`X_W^Q·(A2grid (Icc z y prime) z Dtot Nf + Σ_p (1/(p−1))·slackB_p) + x/L¹⁰`, with
`Nf p = maxDepth (twinA2SieveW … p)` and `slackB_p = ε·CsharpB ε·e²·hBJS (logRatio z
⌈Dtot/p⌉)` — the FREEZE-V2 sharp slack at the per-prime operating point. -/

-- the slot shapes this example instantiates:
--   `hA2 : omegaPrimeSumW Q a x P y ≤ mainA2`     (W-SURG, Assembly Part K)
--   `hrawA2 : mainA2 ≤ XW·(A2grid + aggSlack) + R2` (GLU-1, GlueNormalized)
-- #check @Salt.Chen.chen_of_hypotheses_W    -- the H_W consumer (Assembly)
-- #check @Salt.Chen.twin_A2_upper           -- the aggregation keystone (TwinA2)
-- #check @Salt.Chen.omegaPrimeSumW_decomp   -- deliverable 2 (this file)
-- #check @Salt.Chen.twin_A2_per_prime_W     -- deliverable 3 (this file)
-- #check @Salt.Chen.twinA2W_hcoef           -- deliverable 4 (this file)
-- #check @Salt.Chen.twinA2_hBVagg_W         -- deliverable 5 (this file)

example (Qm a x z y Dtot P w' : ℕ) (ε K Qlev : ℝ)
    (hP : Squarefree P) (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q)
    (hPz : ∀ q ∈ P.primeFactors, q < z)
    (hPlow : ∀ q ∈ P.primeFactors, w0R ε ≤ (q : ℝ))
    (hx : 4 ≤ x) (hz3 : 3 ≤ z)
    (hε : 0 < ε) (hε49B : ε < 1 / 249) (hKe : K ≤ 1 + ε)
    (hw0 : 3 ≤ w0R ε) (hwz : w0R ε ≤ (z : ℝ))
    (hQm1 : 1 ≤ Qm) (hQmP : Nat.Coprime Qm P) (hQma : Nat.Coprime Qm a)
    (hQmPr : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, Nat.Coprime Qm p)
    (hQlev : 1 ≤ Qlev) (hD1 : 1 ≤ Dtot)
    -- the split sifting trio (W-SURG Part I; pays the carrier identification)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Qm)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Qm (a + 2))
    -- the per-prime operating-point rows (GLU-2W discharges at the frozen exponents)
    (hD2 : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, 2 ≤ cdiv Dtot p)
    (hStop : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 ≤ logRatio z (cdiv Dtot p))
    (hstepWPC : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε))
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    -- the two named GLU-2W rows, in the honest ∀-form (x₀ chosen after B, C emerge):
    (hrows : ∀ B C : ℝ, 0 ≤ B → 0 ≤ C →
      ((Qm : ℝ) * (Qlev * ((Dtot : ℝ) + (y : ℝ))) ≤ Real.sqrt (x : ℝ) / (Real.log x) ^ B ∧
        C * (x : ℝ) / (Real.log x) ^ (11 : ℝ) + C * (x : ℝ) / (Real.log x) ^ (11 : ℝ)
          + 2 * Real.log x
              * ((Qm.primeFactors.card : ℝ)
                  + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
              * (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1))
          ≤ (x : ℝ) / (Real.log x) ^ 10)) :
    -- the hA2 slot shape at the concrete mainA2 (= GLU-1's hrawA2 with R2 := x/L¹⁰):
    omegaPrimeSumW Qm a x P y
      ≤ ((twinA1SieveW Qm a x P hP hPodd).totalMass
            * Salt.BrunLower.W (twinA1SieveW Qm a x P hP hPodd))
          * (A2grid ((Finset.Icc z y).filter Nat.Prime) z Dtot
                (fun p => maxDepth (twinA2SieveW Qm a x P p hP hPodd))
              + ∑ p ∈ (Finset.Icc z y).filter Nat.Prime,
                  (1 / ((p : ℝ) - 1))
                    * (ε * CsharpB ε * Real.exp 2 * hBJS (logRatio z (cdiv Dtot p))))
        + (x : ℝ) / (Real.log x) ^ 10 := by
  classical
  -- deliverable 2: the carrier identification
  have hdecomp := omegaPrimeSumW_decomp (x := x) (y := y) (z := z) hQfull hPfull' hQa2
  -- slack nonnegativity (CsharpB ≥ 0 at ε < 1/249; hBJS > 0)
  have hCs : 0 ≤ CsharpB ε := by
    rw [CsharpB]
    apply div_nonneg (by norm_num)
    have := chSharpB_lt_one hε49B
    linarith
  have hslacknn : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime,
      0 ≤ ε * CsharpB ε * Real.exp 2 * hBJS (logRatio z (cdiv Dtot p)) := fun p _ =>
    mul_nonneg (mul_nonneg (mul_nonneg hε.le hCs) (Real.exp_pos 2).le)
      (hBJS_pos (logRatio z (cdiv Dtot p))).le
  -- deliverables 1+3: the per-prime supplier bounds (twin_A2_upper's hper slot)
  have hper : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime,
      A2pW Qm a x P p
        ≤ ((twinA2SieveW Qm a x P p hP hPodd).totalMass
              * Salt.BrunLower.W (twinA2SieveW Qm a x P p hP hPodd))
            * (Fchain (maxDepth (twinA2SieveW Qm a x P p hP hPodd))
                  (logRatio z (cdiv Dtot p))
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio z (cdiv Dtot p)))
          + rosserRemainder (twinA2SieveW Qm a x P p hP hPodd)
              (Qlev * (cdiv Dtot p : ℝ)) := by
    intro p hp
    have hp' := hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp'
    exact le_trans (A2pW_le_siftedSumW Qm a x P p hP hPodd)
      (twin_A2_per_prime_W Qm a x P p z (cdiv Dtot p) ε K Qlev hP hPodd hPz hPlow
        hp'.2.one_lt.le (hD2 p hp) hQlev hε hw0 hKe hε49B hstepWPC h4 (hStop p hp))
  -- deliverable 4: the density coefficient (twin_A2_upper's hcoef slot)
  have hcoef : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime,
      (twinA2SieveW Qm a x P p hP hPodd).totalMass
          * Salt.BrunLower.W (twinA2SieveW Qm a x P p hP hPodd)
        ≤ ((twinA1SieveW Qm a x P hP hPodd).totalMass
            * Salt.BrunLower.W (twinA1SieveW Qm a x P hP hPodd)) * (1 / ((p : ℝ) - 1)) :=
    fun p _ => twinA2W_hcoef Qm a x P p hP hPodd
  -- the aggregation keystone
  have hupper := twin_A2_upper
    (Λmass := (twinA1SieveW Qm a x P hP hPodd).totalMass)
    (V := Salt.BrunLower.W (twinA1SieveW Qm a x P hP hPodd))
    ((Finset.Icc z y).filter Nat.Prime) z Dtot
    (fun p => A2pW Qm a x P p)
    (fun p => (twinA2SieveW Qm a x P p hP hPodd).totalMass
        * Salt.BrunLower.W (twinA2SieveW Qm a x P p hP hPodd))
    (fun p => rosserRemainder (twinA2SieveW Qm a x P p hP hPodd) (Qlev * (cdiv Dtot p : ℝ)))
    (fun p => ε * CsharpB ε * Real.exp 2 * hBJS (logRatio z (cdiv Dtot p)))
    (fun p => maxDepth (twinA2SieveW Qm a x P p hP hPodd))
    hslacknn hper hcoef
  -- deliverable 5: the aggregated BV row
  obtain ⟨B, C, hB, hC, himp⟩ := twinA2_hBVagg_W Qm a x z y Dtot P ε Qlev hP hPodd hPz
    hPlow hx hz3 hε hw0 hwz hQm1 hQmP hQma hQmPr hQlev hD1
  obtain ⟨hrow1, hrow2⟩ := hrows B C hB hC
  have hagg := himp hrow1 hrow2
  -- compose
  rw [hdecomp]
  linarith [hupper, hagg]

end Salt.Chen
