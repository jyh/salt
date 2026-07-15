/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.SharpClose
import Salt.Chen.Assembly

/-!
# SW12 — the switched `BoundingSieve` + the conditional Λ-carrier A₃ bound

Design: the catch-#41 repair (flags entries "2026-07-13 THE hledger GATE" and
"2026-07-13 SW-A₃ RECON") + the H-AMENDMENT in `Assembly.chen_positivity`.  The honest
`hA3 : triplePrimeSum x P y ≤ mainA3` slot needs the **switched-sequence sieve**: the upper
linear sieve applied to `{p₁p₂p₃ − 2}`, the step Chen's proof is famous for and exactly the
step catch #41 found missing (the `Λ(n) ≤ log x` conversion of `triplePrimeSum_le` drops `Λ`'s
prime support and lands at `x`-scale; a genuine sieve carries `W ~ 1/log` and restores the
`x/log x` scale).

## Part A — the switched instance (`switchSieve`)

The switched sequence sifts `n = p₁p₂p₃ − 2` for primality, so — unlike `twinA1Sieve`, which
sifts the *shifted* value `n + 2` — the sieve tests the window point `n` ITSELF: the relevant
congruence per sifting prime `q` is `q ∣ n`, i.e. `p₁p₂p₃ ≡ 2 (mod q)` on the product.  Hence:

* `support = twinWindow x` — the window points `n` (= the admissible triple products shifted
  back by `−2`; the weight vanishes off the actual products);
* `weights n = aCount x z y n` — the switch multiplicity `#{(p₁,p₂,p₃) admissible :
  p₁p₂p₃ = n + 2}` (C3d's fibre count; `α ∈ {0,1,…}`, an honest overcount per the recon's
  multiplicity finding);
* `totalMass = tripleSum x z y` — the C3d count `∑_{n ∈ window} aₙ` (58c note: priced in the
  FINAL chain by the c̄/2-weighted `tripleSum_le_cbar_final`, CountFinal.lean — the old
  unsifted `0.29827` pricing was superseded by catch #53);
* `nu = nuChen` — ONE residue class (`p₁p₂p₃ ≡ 2 mod q`) on the product ⟹ the dimension-1
  density `ν(q) = 1/(q−1) = 1/φ(q)`, the same density as `twinA1Sieve`; `rem d =
  multSum d − ν(d)·totalMass` is then BY DEFINITION the honest deviation of the switched
  sequence in the residue class — no distributional claim is smuggled into the instance
  (SW3/hPerE price the deviation; `hBVswitch` names its summed bound here);
* `prodPrimes = Ps` — the switch sifting modulus, the `∏_{w₀ ≤ q < y} q`-shape: the caller
  supplies squarefreeness, oddness (`3 ≤ q`), the ℚ-window floor (`w₀(ε) ≤ q`, for `hguard`),
  and the **`P(y)` ceiling `q < y`** (the switch sifts by primes `< y`, NOT `< z` — a
  survivor `n` is then prime for `n` in the window once `x` is large; the primality
  endgame is SW4's).

## Part B/C — the side conditions + the sharp upper keystone application

`switch_hnu`/`switch_hguard` clone `twinA1_hnu`/`twinA1_hguard` (both are generic in the
modulus).  `switch_upper_B` applies the FREEZE-V2 sharp cB upper keystone through
`twin_A2_per_prime_B` (which is generic in the instance) at `zTop = y`, level `Dlev`,
operating point `s = logRatio y Dlev`, with the per-step slot filled by `stepHypWPC_sharpB`
(so `hεsmall : ε ≤ 1/1000` rides as a hypothesis and the contraction gate `ε < 1/249` is
derived).  The `fchain`-values stay symbolic — SW4 instantiates the numerics.

## Part D/E — the bridge and the conditional A₃ bound

`triplePrimeSum_le_sifted` — THE BRIDGE: every window point `n` carrying positive
`Λ·keepR·tripleT` mass has `n` prime (from `keepR`), `n + 2 = p₁p₂p₃` an admissible triple
(`aCount ≥ 1` via `aCount_ge_one_of`; admissibility `z ≤ p₁` from the coprimality cut
`hPfull`), and `n` SURVIVES the switch sieve: `n` prime and `n ≥ x/2 ≥ y >` every sifting
prime forces `gcd(Ps, n) = 1`.  With `Λ(n) ≤ log x`, termwise domination gives
`triplePrimeSum x P y ≤ log x · siftedSum`.  Note the TWO moduli: `P` (the razor's `z`-cut,
inside `keepR`) and `Ps` (the switch's `y`-window modulus) are independent.

`mainA3_of_hBVswitch` composes bridge + keystone under the NAMED remainder hypothesis
`hBVswitch : rosserRemainder (switchSieve …) (Q·Dlev) ≤ x/(log x)^10` — the honest A₁/A₂
pattern (`hBV`); its discharge is the SW3 → hPerE arc, NOT this node.  The conclusion is the
exact `mainA3`-shape the H-glue consumes:

  `triplePrimeSum x P y ≤ log x · (tripleSum·W·(Fchain N s + ε·CsharpB ε·e²·hBJS s)
                                    + x/(log x)^10)`.

The catch-#41 trap does not recur: `W (switchSieve …) ~ ∏_{w₀ ≤ q < y}(1 − 1/(q−1)) ~
c/log y` supplies the `1/log` that the naive `Λ ≤ log x` bound lost (recon finding (ii)).

No `sorry`, no `native_decide`, no new axioms; `maxHeartbeats` default (every proof is a
composition of landed lemmas).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the switched `BoundingSieve` instance -/

/-- `0 ≤ aCount` — the switch weight is a cast card. -/
lemma aCount_nonneg (x z y n : ℕ) : 0 ≤ aCount x z y n := by
  rw [aCount]; positivity

/-- **The switched `BoundingSieve`** (the catch-#41 repair's carrier).  Support = the window
points `n` (the sieve tests `q ∣ n`, i.e. `p₁p₂p₃ ≡ 2 (mod q)` on the product — NO shift,
unlike `twinA1Sieve`), weight = the switch multiplicity `aCount`, `totalMass` = the C3d triple
count, density `ν = 1/φ` (one residue class on the product), sifting modulus `Ps` (the
`[w₀, y)` window, all prime factors `≥ 3` via `hPodd`; the `< y` ceiling and `≥ w₀` floor are
supplied at application time, exactly as `twinA1Sieve` threads its window). -/
noncomputable def switchSieve (x z y Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) : BoundingSieve where
  support := twinWindow x
  prodPrimes := Ps
  prodPrimes_squarefree := hPs
  weights := fun n => aCount x z y n
  weights_nonneg := fun n => aCount_nonneg x z y n
  totalMass := tripleSum x z y
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hPs.ne_zero⟩))

section Facts

variable (x z y Ps : ℕ) (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)

@[simp] lemma switchSieve_support :
    (switchSieve x z y Ps hPs hPodd).support = twinWindow x := rfl

@[simp] lemma switchSieve_prodPrimes :
    (switchSieve x z y Ps hPs hPodd).prodPrimes = Ps := rfl

@[simp] lemma switchSieve_nu : (switchSieve x z y Ps hPs hPodd).nu = nuChen := rfl

@[simp] lemma switchSieve_totalMass :
    (switchSieve x z y Ps hPs hPodd).totalMass = tripleSum x z y := rfl

/-- **`multSum d` = the window triple-mass in the residue class `p₁p₂p₃ ≡ 2 (mod d)`** —
the sieve counts (with multiplicity `aCount`) the products whose shift `n = p₁p₂p₃ − 2` is
divisible by `d`. -/
lemma switchSieve_multSum (d : ℕ) :
    (switchSieve x z y Ps hPs hPodd).multSum d
      = ∑ n ∈ twinWindow x, if d ∣ n then aCount x z y n else 0 := rfl

/-- **`siftedSum` = the surviving switch mass** — the `aCount`-weighted count of window
points `n` coprime to the switch modulus `Ps`. -/
lemma switchSieve_siftedSum :
    (switchSieve x z y Ps hPs hPodd).siftedSum
      = ∑ n ∈ twinWindow x, if Nat.Coprime Ps n then aCount x z y n else 0 := rfl

/-- **`rem d`** — the switched AP-remainder, defined by the sieve equation
`rem d = multSum d − ν(d)·totalMass`.  This is the honest deviation of the switched sequence
(SW3 reduces it; `hBVswitch` names its summed bound). -/
lemma switchSieve_rem (d : ℕ) :
    (switchSieve x z y Ps hPs hPodd).rem d
      = (∑ n ∈ twinWindow x, if d ∣ n then aCount x z y n else 0)
        - nuChen d * tripleSum x z y := rfl

/-- `0 ≤ totalMass` — the triple count is a cast card (`tripleSum_eq_card`). -/
lemma switch_totalMass_nonneg : 0 ≤ (switchSieve x z y Ps hPs hPodd).totalMass := by
  rw [switchSieve_totalMass, tripleSum_eq_card]; positivity

end Facts

/-! ## Part B — the sieve-class side conditions (`hnu`, `hguard`) -/

/-- **`hnu`** — `ν(q) ≤ 1/(q−1)` at every sifting prime (an equality; the density is the
same dimension-1 `nuChen` as `twinA1Sieve`, so `twinA1_hnu` transfers verbatim). -/
lemma switch_hnu (Ps : ℕ) : ∀ q ∈ Ps.primeFactors, nuChen q ≤ 1 / ((q : ℝ) - 1) :=
  twinA1_hnu Ps

/-- **`hguard`** — the hypothesis-(4) threshold guard at every sifting prime, from the
ℚ-window floor `q ≥ w₀(ε)` via `w0R_threshold` + `thresh_mono` (the `twinA1_hguard` route;
the guard is generic in the modulus). -/
lemma switch_hguard {Ps : ℕ} {ε : ℝ} (hε : 0 < ε) (hw0 : 3 ≤ w0R ε)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ)) :
    ∀ q ∈ Ps.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
  twinA1_hguard hε hw0 hPodd hPlow

/-! ## Part C — the sharp cB upper keystone at the switched instance -/

/-- **`switch_upper_B` — the sharp (cB) upper linear sieve at the switched sequence.**
`twin_A2_per_prime_B` (the keystone application pattern, generic in the instance) at
`sp0 = switchSieve`, `zTop = y` (the `P(y)` sieve), level `Dlev`, operating point
`logRatio y Dlev`, with the FREEZE-V2 per-step slot filled by `stepHypWPC_sharpB` and the
contraction gate `ε < 1/249` derived from `hεsmall`.  Conclusion (`totalMass` unfolded to
`tripleSum`, the shape SW4 consumes):

  `siftedSum ≤ (tripleSum·W)·(Fchain N s + ε·CsharpB ε·e²·hBJS s) + rosserRemainder (Q·Dlev)`.

The `Fchain`-value stays symbolic; `Q = Qval ε`-shape is threaded through `hQ` exactly as in
the A₁/A₂ carriers. -/
theorem switch_upper_B (x z y Ps Dlev : ℕ) (ε K Q : ℝ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hD2 : 2 ≤ Dlev) (hQ : 1 ≤ Q)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev) :
    (switchSieve x z y Ps hPs hPodd).siftedSum
      ≤ (tripleSum x z y * Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd))
          * (Fchain (maxDepth (switchSieve x z y Ps hPs hPodd)) (logRatio y Dlev)
              + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
        + rosserRemainder (switchSieve x z y Ps hPs hPodd) (Q * Dlev) := by
  set s := switchSieve x z y Ps hPs hPodd with hs
  -- side conditions at the concrete instance (the twinA1/twin_A2 discipline)
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < y := hPy
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    switch_hguard hε hw0 hPodd hPlow
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := switch_hnu Ps
  have htm : 0 ≤ s.totalMass := switch_totalMass_nonneg x z y Ps hPs hPodd
  -- the keystone application, per-step slot filled by `stepHypWPC_sharpB`
  have h := twin_A2_per_prime_B s y Dlev ε K Q hD2 htm hQ hzTop hguard hnu hε.le
    (lt_of_le_of_lt hεsmall (by norm_num)) hKe (stepHypWPC_sharpB ε hε.le hεsmall) h4 hStop
  -- unfold `totalMass = tripleSum` in the conclusion
  have htm_eq : s.totalMass = tripleSum x z y := rfl
  rw [← htm_eq]
  exact h

/-! ## Part D — the bridge: the Λ-carrier is dominated by `log x ·` the sifted sum -/

/-- **`triplePrimeSum_le_sifted` — THE BRIDGE.**  The honest A₃ Λ-carrier is dominated by
`log x` times the switched sifted sum: each window point `n` with `Λ(n)·keepR(P,n)·
tripleT(y,n+2) > 0` has `n` prime and `(P, n+2) = 1` (from `keepR`), so `n + 2 = p₁p₂p₃` is an
ADMISSIBLE triple (`z ≤ p₁` via the coprimality cut `hPfull`; `aCount ≥ 1` by
`aCount_ge_one_of`), and `n` SURVIVES the switch sieve — `n` prime with
`n ≥ x/2 ≥ y >` every prime factor of `Ps` forces `gcd(Ps, n) = 1`.  Finally `Λ(n) ≤ log x`.

The two moduli are independent: `P` is the razor's `z`-cut (inside `keepR`), `Ps` the switch's
`[w₀, y)`-window modulus.  Size hypotheses: `2 ≤ x` and `y ≤ x/2` (nat division). -/
theorem triplePrimeSum_le_sifted (x z y P Ps : ℕ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hx : 2 ≤ x) (hyx2 : y ≤ x / 2)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P) :
    triplePrimeSum x P y
      ≤ Real.log x * (switchSieve x z y Ps hPs hPodd).siftedSum := by
  have hlogx : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  rw [triplePrimeSum, switchSieve_siftedSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hk : Nat.Prime n ∧ Nat.Coprime P (n + 2)
  · by_cases htp : TripleP y (n + 2)
    · -- the survivor case: keep = 1, tripleT = 1, n coprime to Ps, aCount ≥ 1
      have hnmem := hn
      rw [twinWindow, Finset.mem_Icc] at hnmem
      have hkeep1 : keepR P n = 1 := keepR_eq_one_iff.mpr hk
      have htT : tripleT y (n + 2) = 1 := tripleT_eq_one htp
      -- the survival: n prime, n ≥ x/2 ≥ y > every sifting prime ⟹ gcd(Ps, n) = 1
      have hyn : y ≤ n := le_trans hyx2 hnmem.1
      have hcop : Nat.Coprime Ps n := by
        rw [Nat.coprime_comm]
        refine (hk.1.coprime_iff_not_dvd).mpr fun hdvd => ?_
        have hmem : n ∈ Ps.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hk.1, hdvd, hPs.ne_zero⟩
        exact absurd (hPy n hmem) (by omega)
      -- Λ(n) ≤ log x
      have hn1 : 1 ≤ n := hk.1.one_lt.le
      have hnx : n ≤ x := by omega
      have hΛle : vonMangoldt n ≤ Real.log x := by
        refine le_trans vonMangoldt_le_log (Real.log_le_log ?_ ?_)
        · exact_mod_cast hn1
        · exact_mod_cast hnx
      -- the survivor's weight is ≥ 1
      have hge1 : (1 : ℝ) ≤ aCount x z y n := aCount_ge_one_of hx hn hk hPfull htp
      rw [hkeep1, htT, mul_one, mul_one, if_pos hcop]
      calc vonMangoldt n ≤ Real.log x := hΛle
        _ = Real.log x * 1 := (mul_one _).symm
        _ ≤ Real.log x * aCount x z y n := mul_le_mul_of_nonneg_left hge1 hlogx
    · -- no triple pattern: LHS term vanishes
      have h0 : tripleT y (n + 2) = 0 := by unfold tripleT; rw [if_neg htp]
      rw [h0, mul_zero]
      refine mul_nonneg hlogx ?_
      split_ifs
      · exact aCount_nonneg x z y n
      · exact le_refl 0
  · -- not kept: LHS term vanishes
    have hkeep0 : keepR P n = 0 := by unfold keepR; rw [if_neg hk]
    rw [hkeep0, mul_zero, zero_mul]
    refine mul_nonneg hlogx ?_
    split_ifs
    · exact aCount_nonneg x z y n
    · exact le_refl 0

/-! ## Part E — the conditional A₃ bound (`hBVswitch` NAMED, the honest A₁/A₂ pattern) -/

/-- **`mainA3_of_hBVswitch` — the composed CONDITIONAL A₃ bound (the SW12 endpoint).**
Bridge + sharp keystone under the NAMED remainder hypothesis

  `hBVswitch : rosserRemainder (switchSieve …) (Q·Dlev) ≤ x/(log x)^10`

(the honest A₁/A₂ `hBV` pattern; its discharge is the SW3 → hPerE arc).  Conclusion — the
exact `mainA3` the H-glue's `hA3 : triplePrimeSum x P y ≤ mainA3` slot takes, with

  `mainA3 = log x · (tripleSum·W·(Fchain N s + ε·CsharpB ε·e²·hBJS s) + x/(log x)^10)`

at `N = maxDepth (switchSieve …)`, `s = logRatio y Dlev`.  The `W`-factor carries the
`~ 1/log` the catch-#41 route lost; SW4 collapses the numerics (`W`, `Fchain`, the C3d count)
against the c̄ ledger row. -/
theorem mainA3_of_hBVswitch (x z y P Ps Dlev : ℕ) (ε K Q : ℝ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hx : 2 ≤ x) (hyx2 : y ≤ x / 2)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hD2 : 2 ≤ Dlev) (hQ : 1 ≤ Q)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev)
    (hBVswitch : rosserRemainder (switchSieve x z y Ps hPs hPodd) (Q * Dlev)
        ≤ (x : ℝ) / (Real.log x) ^ 10) :
    triplePrimeSum x P y
      ≤ Real.log x *
          (tripleSum x z y * Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd)
              * (Fchain (maxDepth (switchSieve x z y Ps hPs hPodd)) (logRatio y Dlev)
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
            + (x : ℝ) / (Real.log x) ^ 10) := by
  have hlogx : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  have hbridge := triplePrimeSum_le_sifted x z y P Ps hPs hPodd hPy hx hyx2 hPfull
  have hupper := switch_upper_B x z y Ps Dlev ε K Q hPs hPodd hPy hPlow hD2 hQ hε hw0
    hεsmall hKe h4 hStop
  -- fold the named remainder bound into the keystone conclusion
  have hsift : (switchSieve x z y Ps hPs hPodd).siftedSum
      ≤ tripleSum x z y * Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd)
          * (Fchain (maxDepth (switchSieve x z y Ps hPs hPodd)) (logRatio y Dlev)
            + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
        + (x : ℝ) / (Real.log x) ^ 10 := by linarith [hupper, hBVswitch]
  calc triplePrimeSum x P y
      ≤ Real.log x * (switchSieve x z y Ps hPs hPodd).siftedSum := hbridge
    _ ≤ Real.log x *
          (tripleSum x z y * Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd)
              * (Fchain (maxDepth (switchSieve x z y Ps hPs hPodd)) (logRatio y Dlev)
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
            + (x : ℝ) / (Real.log x) ^ 10) := mul_le_mul_of_nonneg_left hsift hlogx

end Salt.Chen
