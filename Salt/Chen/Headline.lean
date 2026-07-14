/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.GlueFinal

/-!
# GLU-2 re-run — ★ CATCH #65 ★: the H-package's `hPfull` is torn from every landed
A₁ supplier (the ℚ-window bridge is unpayable "in the choice of `P`")

This node's mandate (post-D0W) was the summit: discharge `chen_of_hypotheses`' H at the
operating point and land `chen_headline`.  The re-run's STEP-0 sweep — matching every
H-conjunct against its landed supplier's verbatim signature — found the H-package
**unsatisfiable at the `hPfull`/`hA1` pair**, kernel-checked below (Part 1).  The BV half
(`hBVblocks`) is NOT torn; its remaining op-point findings are recorded in Part 2's
docstrings for the post-repair run.

## ★ CATCH #65 — the slot tear ★

`chen_of_hypotheses` (Salt/Chen/Assembly.lean) requires ONE modulus `P` carrying BOTH

* `hPfull : ∀ q, q.Prime → q < z → q ∣ P`   (razor: `factors_ge_z_of_sift`, the weight
  argument, and the survivor's `IsP2` all need every prime `< z` — including `2` — to
  divide `P`), and
* `hA1 : mainA1 ≤ A1primeSum x P` with `hledger` at the certified constants — whose ONLY
  landed suppliers (`TwinA1.twin_A1_lower`, `TwinSharp.twin_A1_lower_B`, threading
  `twinA1Sieve x P hP hPodd`) carry
  `hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p` and `hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ p`.

`hPodd` is NOT an incidental convention: the sieve density is `ν = 1/φ`, and
`nuChen 2 = 1/φ(2) = 1`, so `BoundingSieve.nu_lt_one_of_prime` structurally excludes `2`
from every modulus (TwinA1.lean:102, `nuChen_lt_one` requires `3 ≤ p`).  For `z ≥ 3`:

* `hPfull` at `q = 2` forces `2 ∣ P`; with `hPodd` this forces **`P = 0`**
  (`catch65_slot_torn` below — in ℕ, `q ∣ 0` for all `q`, so `P = 0` is the unique
  survivor);
* at `P = 0` the keep-indicator vanishes (`Nat.Coprime 0 (n+2)` means `n + 2 = 1`), so
  `A1primeSum x 0 = 0`, and the ledger conjunct collapses:
  `0 < mainA1 − mainA2/2 − mainA3/2 − strip/2 ≤ 0` — **False**
  (`catch65_no_H_at_odd_P` below, stated against the verbatim H-conjunct shapes).

So NO instantiation of H is compatible with the landed A₁ machinery.  The Assembly-era
claim ("the honest home of the ℚ-window `[w₀,z)` vs `[2,z)` bridge — paid by the caller
in the choice of `P`") is refuted: there is no choice of `P` that pays it.

**The deeper (normalization) half, for the record** (true mathematics, not kernel-checked
here): even if the parity tear were patched by hand, the range `[3, w₀)`
(`w₀ = w0R(2·10⁻⁸) ≈ exp(2·10⁹)`) is structurally outside the Rosser-chain machinery —
the per-prime guard `19/log q + 4/(q−1) ≤ log(1+ε)` fails for every small `q` at every
admissible `ε ≤ 1/1000`.  A hypothetical FULL-primorial carrier `A1primeSum x (∏_{p<z} p)`
sits a factor `≍ ∏_{3≤p<w₀}(1 − 1/(p−1)) ≍ c/log w₀ ≈ 10⁻⁹` below the `[w₀,z)`-normalised
`X_W = totalMass·W(twinA1Sieve)` line, while `hledger` at the certified constants needs
`mainA1 > (mainA2 + mainA3)/2 ≈ 0.483·X_W`.  Both sides: required `≳ 0.483·X_W`; available
`≲ 10⁻⁹·X_W`-scale.  No threshold `x₀` cures a normalization ratio.

**Repair direction (Fable-tier; Iron Rule 1 — no landed statement touched here).**  The
classical fix is the one the corpus's own conventions anticipate: restrict the razor
carriers to a residue class `n ≡ a (mod Q)`, `Q = ∏_{p<w₀} p`, with `a + 2` coprime to `Q`
(the BV level `Q·D` threaded through `twin_A1_lower`/`mainA3_*` since C2a was sized for
exactly this).  Then: `2` is free by parity (window survivors are odd primes, `n + 2` odd);
`[3, w₀)` is free by AP-membership; `hPfull` keeps only its `[w₀, z)` range, matching the
suppliers.  This re-states `keepR`/`A1primeSum`/`omegaPrimeSum`/`triplePrimeSum`/
`p2PrimeSum` (an `a mod Q` slot), `razor_reduction`'s factor-floor step (parity +
AP-membership + `[w₀,z)`-coprimality in place of `hPfull`), and the H shape — i.e.
Assembly.lean surgery + supplier re-threading: a design node, not glue.

## Part 2 — the re-run recon (durable findings for the post-#65 run)

Recorded here because they are carrier-independent of the #65 repair and were verified
against the landed statements during this run's STEP 0:

* **Finding 3 (D0W floor gap).**  `d0_window_nonempty` (SqrtDFold §12) hypothesizes
  `hNfloor : x^{11/24}/8 ≤ N`, but the honest floor for terminal-needing boundary boxes is
  weaker: a high box needs a price (rather than an α-support-empty zero) only when
  `2^i < z·N + 1`, which with boundary clause 3 (`x/2 + 1 < (2^{i+1}−1)·M`, `M = 2N+1`)
  forces only `x < 4(2N+1)(zN+1) ≤ 24·z·N²`, i.e. `N > √(x/(24z)) = x^{7/16}/(2√6) ≈
  x^{0.4375}/4.9` — POLYNOMIALLY below `x^{11/24}/8 = x^{0.4583}/8`.  Pieces in the strip
  `[x^{7/16}/4.9, x^{11/24}/8)` carry non-cancelling boundary boxes with no landed D0
  witness.  The SAME construction covers them: at `log N ≥ (7/16)·t − 2` the binding row
  `4L^{17} ≤ (log N)^{18}` needs `t·(7/16)^{18} ≥ 4(1+o(1))`, i.e. `t ≥ 1.2·10⁷` — room
  ≈ 83× at the `t = 10⁹` threshold (vs D0W's 39×).  A one-hypothesis variant of
  `d0_window_nonempty` (hNfloor at `x^{7/16}/8`) suffices; deliberately NOT re-proved here
  (the D0W-consumption directive) — flagged for a one-line floor amendment instead.
* **Finding 4 (the block width `ε₀` is free — and MUST be taken huge).**  No statement in
  the `hBVblocks` chain constrains `ε₀` beyond `0 < ε₀` (+ `1 ≤ z`) for the coverage
  identities; `hBlock_of_window_prices` takes bare `ε₀ : ℝ`.  Take `ε₀ := (x : ℝ)` so
  `maxBlock x z ε₀ = O(1)`.  This is not merely convenient but REQUIRED at the pinned
  `A = 13`: the SW couplings force per-box `Km, Kβ′ ≳ K·L·(L/log N)^{A+2C0} ≈ K·t·e^{41}`
  (one net power of `t` plus `(24/13)^{49}`-type constants), so with `Θ(t/log(1+ε₀))`
  blocks × `Θ(t)` pieces the price sum lands at `(const·K/log(1+ε₀))·x/t^{10}` — over the
  `x/(log x)^{10}` budget by a CONSTANT for any constant `ε₀`, but under it by a factor
  `t/(const·K)` at `maxBlock = O(1)`.  Corollary: the master threshold must be chosen
  AFTER destructuring the terminal's existential — `x₀ = x₀(K)` (legal inside the
  H-proof; `K` is fixed by `A = 13`, `C0 = 18` before any `x` is picked).
* **Finding 5 (hCE route).**  `hCE`'s residual (the ν-weighted `blockNonUnitCount` sum) is
  closable without new analytic inputs: a non-unit triple shares a prime with `d ∣ Ps`;
  since `p₂, p₃ > y >` every factor of `Ps`, that prime is `p₁`, so `p₁ ∣ d`;
  `Σ_{d ∣ Ps} ν(d)·[p ∣ d] ≤ ν(p)·Σ_{d' ∣ Ps} ν(d')` with
  `Σ_{d ∣ Ps} ν(d) = ∏(1+ν) ≤ 1/W(switchSieve) ≤ e^{35}·log(y+1)` (via `W_twinA1_ge` at
  `P := Ps`, real cutoff `y+1`); the per-`p₁` triple count is `≤ (x/p₁)·(1 + log x)`
  (harmonic fiber count, `sum_inv_Icc_le_log`); total `≤ e^{35}·x·polylog/z = x^{7/8}·polylog
  ≪ x/(log x)^{10}` with `x^{1/8}` room.
* **Finding 6 (A₁ prime-power bridge).**  `twin_A1_lower_B`'s conclusion is the coprime
  Λ-sum WITHOUT the `[n prime]` restriction that `A1primeSum` carries; the bridge mass
  (prime powers `p^k ≤ x`, `k ≥ 2`) is `≤ √x·log₂x·log x` — one small lemma at the re-run.
* The still-good pieces from this file's predecessor run (`GlueFinal.lean`): `hyx_at_op`,
  `sievePrimorial_dvd` (serves `mainA3_of_block_remainders`' hPfull — the A₃ line's `P` is
  NOT torn: only the A₁ suppliers pin `P`'s parity), `hDsq_row`, `hfloor_row`, `habs_row`
  (note: at boundary boxes `N·M ≥ N² ≥ x²·⁰·⁴³⁷⁵/24 ≥ x^{7/8}/24` — the landed
  `x^{7/8}/8`-form row needs only the trivial `/8 → /24` adjustment or the sharper floor),
  `logRatio_A3_mem_range` (the shifted-`Dlev` membership).

No `sorry`, no `native_decide`, no new axioms; NEW file, no landed file touched.
-/

open ArithmeticFunction

namespace Salt.Chen

/-! ## Part 1 — ★ CATCH #65 ★, kernel-checked -/

/-- **The parity tear.**  For `z ≥ 3`, any `P` satisfying the H-package's `hPfull`
(`∀ q prime < z, q ∣ P`) together with the A₁-suppliers' structural parity constraint
`hPodd` (`∀ p ∈ P.primeFactors, 3 ≤ p` — forced by `ν(2) = 1/φ(2) = 1` through
`nuChen_lt_one`/`nu_lt_one_of_prime`) must be `0`: `hPfull` gives `2 ∣ P`, and a nonzero
`P` would then have `2 ∈ P.primeFactors`, contradicting `hPodd`. -/
theorem catch65_slot_torn {z P : ℕ} (hz : 3 ≤ z)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) : P = 0 := by
  by_contra hne
  have h2P : 2 ∣ P := hPfull 2 Nat.prime_two (by omega)
  have h2mem : 2 ∈ P.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2P, hne⟩
  have := hPodd 2 h2mem
  omega

/-- At the modulus `P = 0` the keep-indicator vanishes: `Nat.Coprime 0 (n+2)` says
`gcd 0 (n+2) = n + 2 = 1`, impossible. -/
lemma keepR_zero_modulus (n : ℕ) : keepR 0 n = 0 := by
  unfold keepR
  rw [if_neg]
  rintro ⟨-, hcop⟩
  have h1 : n + 2 = 1 := by rwa [Nat.Coprime, Nat.gcd_zero_left] at hcop
  omega

/-- The A₁ carrier vanishes at `P = 0`. -/
lemma A1primeSum_zero_modulus (x : ℕ) : A1primeSum x 0 = 0 := by
  unfold A1primeSum
  exact Finset.sum_eq_zero fun n _ => by rw [keepR_zero_modulus, mul_zero]

/-- The aggregated A₂ carrier is nonnegative (termwise `Λ ≥ 0`, `keepR ≥ 0`, `ω ≥ 0`). -/
lemma omegaPrimeSum_nonneg (x P y : ℕ) : 0 ≤ omegaPrimeSum x P y := by
  unfold omegaPrimeSum
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepR_nonneg P n)) (Nat.cast_nonneg _)

/-- The A₃ switch carrier is nonnegative (termwise, via `tripleT_nonneg`). -/
lemma triplePrimeSum_nonneg (x P y : ℕ) : 0 ≤ triplePrimeSum x P y := by
  unfold triplePrimeSum
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepR_nonneg P n)) (tripleT_nonneg y (n + 2))

/-- ★ **CATCH #65 — the headline.** ★  NO instantiation of `chen_of_hypotheses`' H-package
whose modulus `P` carries the landed A₁-suppliers' parity constraint (`hPodd`, structural
in `twinA1Sieve`/`twin_A1_lower`/`twin_A1_lower_B` via `ν(2) = 1`) can satisfy the
H-conjuncts at any `z ≥ 3` (in particular at the operating `z = ⌊x^{1/8}⌋ ≥ w₀`): the
`hPfull` + `hPodd` pair forces `P = 0` (`catch65_slot_torn`), where the A₁ carrier is `0`
and the `hA1`/`hA2`/`hA3`/`hledger` conjuncts — stated verbatim below — are jointly
`False`.  Consequence: `chen_headline` is NOT dischargeable through the landed corpus;
the ℚ-window bridge (`[2, w₀)`-handling) must be paid at the STATEMENT level (module
header: the mod-`Q` AP repair), not "in the choice of `P`". -/
theorem catch65_no_H_at_odd_P {x z P y : ℕ} {mainA1 mainA2 mainA3 : ℝ}
    (hz3 : 3 ≤ z)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hA1 : mainA1 ≤ A1primeSum x P)
    (hA2 : omegaPrimeSum x P y ≤ mainA2)
    (hA3 : triplePrimeSum x P y ≤ mainA3)
    (hledger : 0 < mainA1 - mainA2 / 2 - mainA3 / 2
        - Real.log x * (x : ℝ) / ((z : ℝ) - 1) / 2) : False := by
  have hP0 : P = 0 := catch65_slot_torn hz3 hPfull hPodd
  subst hP0
  have hA1z : A1primeSum x 0 = 0 := A1primeSum_zero_modulus x
  have h2 : 0 ≤ omegaPrimeSum x 0 y := omegaPrimeSum_nonneg x 0 y
  have h3 : 0 ≤ triplePrimeSum x 0 y := triplePrimeSum_nonneg x 0 y
  have hstrip : 0 ≤ Real.log x * (x : ℝ) / ((z : ℝ) - 1) := by
    have hz1 : (1 : ℝ) ≤ (z : ℝ) - 1 := by
      have h3R : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz3
      linarith
    exact div_nonneg (mul_nonneg (Real.log_natCast_nonneg x) (Nat.cast_nonneg x))
      (by linarith)
  linarith

/-! ## Composition sanity — the torn slots' verbatim sources -/

section CompositionSanity

-- the H-package (the `hPfull`/`hA1`/`hledger` conjuncts this catch is stated against)
#check @Salt.Chen.chen_of_hypotheses
#check @Salt.Chen.chen_positivity
-- the A₁ suppliers carrying `hPodd`/`hPlow` (the other side of the tear)
#check @Salt.Chen.twin_A1_lower_B
#check @Salt.Chen.twinA1Sieve
-- the untorn A₃/BV side (post-D0W), still the F2 target after the #65 repair
#check @Salt.Chen.mainA3_of_block_remainders
#check @Salt.Chen.d0_window_nonempty
#check @Salt.Chen.general_BV_cutoff_sqrtD
-- this file
#check @Salt.Chen.catch65_slot_torn
#check @Salt.Chen.catch65_no_H_at_odd_P

end CompositionSanity

end Salt.Chen
