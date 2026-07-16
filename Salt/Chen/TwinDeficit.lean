/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.Assembly
import Salt.Chen.RazorClose

/-!
# Q5b Axis B — the twin-target deficit (exploration probe)

**This is EXPLORATION, not a frozen blueprint node.**  Design context:
`docs/exploration/q5b-class.md` (Axis B, frozen by registration amendment A2).  The file adds NEW
work only; it edits no landed file and is not wired into `Salt.Chen.All`.  Everything here is
sorry-free and axiom-clean; every OPEN gap is recorded as a NAMED HYPOTHESIS plus prose, never as
a `sorry`'d theorem.

## THE CONSTRAINT STORE (the exact P₁-razor form — READ BEFORE ANY PROOF)

The landed razor (`Assembly.razor_reduction`) lower-bounds the P₂ carrier over the landed window
`twinWindow x`, keep `keepR P`, and weight `chenWeight y`:

  `p2RazorLHS := A1primeSum − ½·omegaPrimeSum − ½·triplePrimeSum − ½·stripPrimeSum ≤ p2PrimeSum`.

The P₁ (twin) target splits the P₂ mass EXACTLY: `IsP2 z m ↔ m.Prime ∨ IsE2 z m`, a disjoint
union (`IsE2` = a product of two primes both `≥ z`, never prime), so pointwise
`p2Ind z m = p1Ind m + e2Ind z m` and carrier-wise `p2PrimeSum = p1PrimeSum + e2PrimeSum`.
Chen's weight `w = 1 − ½ω − ½·1_T − ½S` dominates `1_{P₂} = 1_{P₁} + 1_{E2}` at sifted points;
hence the honest P₁-form of the razor — SAME carriers, SAME window, SAME keep, SAME weight,
the target hardened from P₂ to P₁ — is

  `p1RazorValue := p2RazorLHS − e2PrimeSum   (≤ p1PrimeSum, the P₁-razor reduction)`:

the landed razor value minus the entire two-factor mass the landed argument deliberately keeps.
The frozen Axis-B question: is this value NEGATIVE with an explicit kernel-checked deficit?

## The ledger: LANDED vs HYPOTHESIZED

**Landed here (unconditional, from landed material only):**
* the split `p2Ind_split` / `p2PrimeSum_split` (+ `_W` mirrors at the live H-AMENDMENT-2 carriers);
* `p1_razor_reduction` (+`_W`): `p1RazorValue ≤ p1PrimeSum` — one inequality, two readings:
  (i) the P₁-razor honestly lower-bounds the twin carrier (the structural analogue LANDS), and
  (ii) the P₁-razor's guaranteed value is CAPPED by the very twin mass it targets, so landed
  one-sided certificates can never certify it positive (the R4 tripwire is structurally safe);
* `p1RazorValue_eq`: `p1RazorValue = p1PrimeSum − (p2PrimeSum − p2RazorLHS)` — the deficit is
  EXACTLY the assertion that the razor's slack on the P₂ carrier exceeds the twin mass;
* the pointwise obstruction `heavy_semiprime_obstruction`: at `m = p·q` with `y < p, q` (both
  `≥ z`), Chen's weight is the FULL unit `1`, all three decorations vanish, and the point is
  P₂-but-not-P₁ — the E2 mass above `y` is INVISIBLE to every decoration of the landed weight;
* the certified floor (Part G, consuming `razor_scalar_margin`, hence `cbar_lt` + the LogToolkit
  sandwiches): at the certified constants `XW/200 ≤ p2RazorLHS`, so any discharge of the deficit
  must certify the two-factor mass ABOVE the razor's entire certified output plus the deficit
  (`deficit_floor_of_certs : 1/200 + δ ≤ e2lo`), and the razor-derived E2 lower bound is capped
  at `XW·(1/200 − tup)` given a twin-mass budget `tup` (`e2_lower_of_certs_twinup`).

**Hypothesized (the two NAMED gaps — the honest conditional boundary):**
* **GAP-U** `hA1up : A1primeSum ≤ XW·a1up` — an X_W-scale UPPER bound on the sifted prime mass:
  the F-side (upper) Rosser–Iwaniec chain at `s = 4`.  The corpus carries only the f-side/lower
  chain (`fchain`, `SuperClose.fchain_A1_final ≥ 9779/10000`); no upper `Fchain`-value node exists.
* **GAP-E** `hE2lo : XW·e2lo ≤ e2PrimeSum` — an X_W-scale LOWER bound on the two-factor mass.
  The landed switching layer (`SwitchSieve`/`CountFinal`, the τ/step-bound machinery) bounds the
  TRIPLE mass from ABOVE; nothing in the corpus bounds the E2 mass from BELOW.  (Chen's own
  semiprime count would discharge it; that is genuinely new analytic content.)

**The self-funding no-go (why the conditional form is forced).**  Every landed lower bound on
`e2PrimeSum` routes through `e2 = p2 − p1 ≥ p2RazorLHS − p1` — the razor's own value minus the
twin mass — and feeding that back gives `p1RazorValue ≤ p1PrimeSum`: nonnegative-capped, never
negative.  Kernel-checked shape: `p1RazorValue_eq` + `deficit_floor_of_certs` (any deficit
discharge needs `e2lo` strictly above the razor's whole certified margin).  The deficit therefore
CANNOT be closed from the razor alone; it is equivalent to the genuinely-new comparison
`e2lo > a1up`, which the frozen deliverable `twin_razor_deficit` takes as its arithmetic gate.
(GATE ERRATUM, 2026-07-17: this gate is VACUOUS as a target — `e2PrimeSum ≤ A1primeSum` always
(`e2Ind ≤ 1` term-by-term), so `e2lo ≤ a1up` is forced and no operating point satisfies the gate
with `δ > 0`. The theorem stands as stated (a conditional with an unsatisfiable-at-op hypothesis
family); the HONEST one-hypothesis no-go is `deficit_floor_of_certs` below — the E2 mass against
the razor's certified VALUE (`e2lo ≥ 1/200 + δ`), not the sifted mass. See the sprint-2 GAP-U
gate report in the exploration ledger.)

## THE DELIVERABLE (honest conditional form; deviation from the frozen shape reported)

`twin_razor_deficit : p1RazorValue ≤ −(δ·XW)` given `hA1up` (GAP-U), `hE2lo` (GAP-E), and the
gate `a1up + δ ≤ e2lo`; `twin_razor_deficit'` restates it as the literal frozen `≤ −δ` for
`XW ≥ 1`.  Deviations from the frozen `twin_razor_deficit : (P₁-razor value) ≤ −δ`:
(i) CONDITIONAL on the two named gaps (the sanctioned fallback — the Q5a
resolved-as-obstruction pattern); (ii) the primary form is `XW`-normalised (the razor value is
`XW`-scaled; the unnormalised corollary is provided).  Never strengthened silently.

## R4 (the too-good-to-be-true tripwire) — armed, and structurally CLEAR

Nothing here proves `p1RazorValue` positive: every unconditional statement is an UPPER cap
(`≤ p1PrimeSum`, `≤ −δ·XW` conditionally), and the inhabitation witnesses certify only carrier
positivity at a toy point (`x = 35`: the twin pair `(17, 19)` and the semiprime point
`19 + 2 = 3·7` — trivially true facts, no twin-prime content).  The certified-floor lemmas pin
the landed material's P₁-guarantee at the twin-mass cap; no intermediate implies twins.
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the constraint store: the P₁/E2 split objects at the landed carriers -/

/-- **The E2 (two-factor) shape** — exactly the second disjunct of `IsP2 z`: a product of two
primes, both `≥ z`.  `IsP2 z m ↔ m.Prime ∨ IsE2 z m` definitionally, and the disjuncts are
disjoint (`IsE2.not_prime`), so the P₂ mass splits EXACTLY into P₁ mass + E2 mass. -/
def IsE2 (z m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q ∧ z ≤ p ∧ z ≤ q

/-- A two-factor number is never prime — the disjointness of the P₂ split. -/
theorem IsE2.not_prime {z m : ℕ} (h : IsE2 z m) : ¬ m.Prime := by
  obtain ⟨p, q, hp, hq, rfl, -, -⟩ := h
  exact Nat.not_prime_mul hp.ne_one hq.ne_one

/-- `IsP2` is definitionally the disjunction of the P₁ and E2 shapes. -/
theorem isP2_iff_p1_or_e2 (z m : ℕ) : IsP2 z m ↔ m.Prime ∨ IsE2 z m := Iff.rfl

/-- `1_{P₁}(m)` — the prime indicator, the twin target. -/
noncomputable def p1Ind (m : ℕ) : ℝ := by
  classical exact if m.Prime then 1 else 0

/-- `1_{E2,z}(m)` — the two-factor indicator, the mass the P₁ weight must additionally pay. -/
noncomputable def e2Ind (z m : ℕ) : ℝ := by
  classical exact if IsE2 z m then 1 else 0

theorem p1Ind_nonneg (m : ℕ) : 0 ≤ p1Ind m := by
  unfold p1Ind; split_ifs <;> norm_num

theorem e2Ind_nonneg (z m : ℕ) : 0 ≤ e2Ind z m := by
  unfold e2Ind; split_ifs <;> norm_num

/-- The P₁ (twin) carrier `Σ_{n} Λ(n)·1_keep·1_{P₁}(n+2)` — the quantity a twin razor would have
to lower-bound, over the LANDED window/keep. -/
noncomputable def p1PrimeSum (x P : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepR P n * p1Ind (n + 2)

/-- The E2 carrier `Σ_{n} Λ(n)·1_keep·1_{E2,z}(n+2)` — the P₂-but-not-P₁ mass over the LANDED
window/keep: the deficit driver. -/
noncomputable def e2PrimeSum (x z P : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepR P n * e2Ind z (n + 2)

/-- The landed razor's guaranteed expression (the LHS of `razor_reduction`), as a named value. -/
noncomputable def p2RazorLHS (x P y : ℕ) : ℝ :=
  A1primeSum x P - omegaPrimeSum x P y / 2 - triplePrimeSum x P y / 2 - stripPrimeSum x P y / 2

/-- **The P₁-razor value** — the honest P₁-form of the landed razor: the landed razor value minus
the two-factor mass.  Chen's weight dominates `1_{P₁} + 1_{E2}` at sifted points, so
`p1RazorValue ≤ p1PrimeSum` (`p1_razor_reduction`); the Axis-B question is its SIGN. -/
noncomputable def p1RazorValue (x z P y : ℕ) : ℝ :=
  p2RazorLHS x P y - e2PrimeSum x z P

/-! ## Part B — the exact split of the P₂ mass -/

/-- **The pointwise split** `1_{P₂,z} = 1_{P₁} + 1_{E2,z}` — exact, since the two shapes are
disjoint (`IsE2.not_prime`) and exhaust `IsP2 z`. -/
theorem p2Ind_split (z m : ℕ) : p2Ind z m = p1Ind m + e2Ind z m := by
  unfold p2Ind p1Ind e2Ind
  by_cases hp : m.Prime
  · have hP2 : IsP2 z m := Or.inl hp
    have hne : ¬ IsE2 z m := fun he => he.not_prime hp
    rw [if_pos hP2, if_pos hp, if_neg hne]
    norm_num
  · by_cases he : IsE2 z m
    · have hP2 : IsP2 z m := Or.inr he
      rw [if_pos hP2, if_neg hp, if_pos he]
      norm_num
    · have hnP2 : ¬ IsP2 z m := by
        rintro (h | h)
        · exact hp h
        · exact he h
      rw [if_neg hnP2, if_neg hp, if_neg he]
      norm_num

/-- **The carrier split** `p2PrimeSum = p1PrimeSum + e2PrimeSum` — the P₂ carrier is EXACTLY the
twin mass plus the two-factor mass, over the landed window/keep. -/
theorem p2PrimeSum_split (x z P : ℕ) :
    p2PrimeSum x z P = p1PrimeSum x P + e2PrimeSum x z P := by
  rw [p2PrimeSum, p1PrimeSum, e2PrimeSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by rw [p2Ind_split, mul_add]

/-! ## Part C — the pointwise obstruction: heavy semiprimes are invisible to the weight

At `m = p·q` with BOTH factors above the decoration cutoff `y`, every prime factor of `m` exceeds
`y`, so `ω_{≤y}(m) = 0`, the strip count is `0`, and the triple pattern (which needs a factor
`≤ y`) fails — Chen's weight takes its FULL value `1` while the P₁ target is `0`.  Every such
point charges the P₁ ledger a full `Λ(n)·keep` unit that no decoration of the landed weight can
see: this is WHY the P₁-form must pay `e2PrimeSum` and why no retuning of the `½`-coefficients
helps (the decorations are identically zero there). -/

/-- Every prime factor of a heavy semiprime `p·q` (`y < p`, `y < q`) exceeds `y`. -/
theorem heavy_semiprime_factors {y p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hyp : y < p) (hyq : y < q) : ∀ r ∈ (p * q).primeFactors, y < r := by
  intro r hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hrd : r ∣ p * q := Nat.dvd_of_mem_primeFactors hr
  rcases (Nat.Prime.dvd_mul hrp).mp hrd with h | h
  · rwa [(Nat.prime_dvd_prime_iff_eq hrp hp).mp h]
  · rwa [(Nat.prime_dvd_prime_iff_eq hrp hq).mp h]

/-- `ω_{≤y}` vanishes on heavy semiprimes. -/
theorem omegaLe_eq_zero_of_heavy {y p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hyp : y < p) (hyq : y < q) : omegaLe y (p * q) = 0 := by
  rw [omegaLe, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro r hr
  exact not_le.mpr (heavy_semiprime_factors hp hq hyp hyq r hr)

/-- The square strip vanishes on heavy semiprimes. -/
theorem sqStrip_eq_zero_of_heavy {y p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hyp : y < p) (hyq : y < q) : sqStrip y (p * q) = 0 := by
  rw [sqStrip, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro r hr hcon
  exact absurd hcon.1 (not_le.mpr (heavy_semiprime_factors hp hq hyp hyq r hr))

/-- The triple pattern fails on heavy semiprimes (its smallest factor must be `≤ y`). -/
theorem not_tripleP_of_heavy {y p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hyp : y < p) (hyq : y < q) : ¬ TripleP y (p * q) := by
  rintro ⟨p₁, p₂, p₃, hp1, _hp2, _hp3, hprod, hp1y, -, -⟩
  have hd : p₁ ∣ p * q := by rw [hprod]; exact ⟨p₂ * p₃, by ring⟩
  have hne : p * q ≠ 0 := (Nat.mul_pos hp.pos hq.pos).ne'
  have hmem : p₁ ∈ (p * q).primeFactors := Nat.mem_primeFactors.mpr ⟨hp1, hd, hne⟩
  exact absurd hp1y (not_le.mpr (heavy_semiprime_factors hp hq hyp hyq p₁ hmem))

/-- Chen's weight takes its FULL value `1` on heavy semiprimes: all three decorations vanish. -/
theorem chenWeight_eq_one_of_heavy {y p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hyp : y < p) (hyq : y < q) : chenWeight y (p * q) = 1 := by
  have ht : tripleT y (p * q) = 0 := by
    unfold tripleT; rw [if_neg (not_tripleP_of_heavy hp hq hyp hyq)]
  rw [chenWeight, omegaLe_eq_zero_of_heavy hp hq hyp hyq,
    sqStrip_eq_zero_of_heavy hp hq hyp hyq, ht]
  norm_num

/-- **THE POINTWISE OBSTRUCTION.**  A heavy semiprime (`z ≤ p, q` and `y < p, q`) takes full
Chen weight `1`, is not a P₁ point, and is an E2 point: the landed weight charges the P₁ ledger
one whole unit of P₂-but-not-P₁ mass there, invisibly to all three decorations. -/
theorem heavy_semiprime_obstruction {z y p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hzp : z ≤ p) (hzq : z ≤ q) (hyp : y < p) (hyq : y < q) :
    chenWeight y (p * q) = 1 ∧ p1Ind (p * q) = 0 ∧ e2Ind z (p * q) = 1 := by
  refine ⟨chenWeight_eq_one_of_heavy hp hq hyp hyq, ?_, ?_⟩
  · unfold p1Ind; rw [if_neg (Nat.not_prime_mul hp.ne_one hq.ne_one)]
  · unfold e2Ind; rw [if_pos ⟨p, q, hp, hq, rfl, hzp, hzq⟩]

/-! ## Part D — the P₁-razor reduction (unconditional, from landed material) -/

theorem omegaPrimeSum_nonneg (x P y : ℕ) : 0 ≤ omegaPrimeSum x P y := by
  rw [omegaPrimeSum]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepR_nonneg P n)) (Nat.cast_nonneg _)

theorem triplePrimeSum_nonneg (x P y : ℕ) : 0 ≤ triplePrimeSum x P y := by
  rw [triplePrimeSum]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepR_nonneg P n)) (tripleT_nonneg y (n + 2))

theorem stripPrimeSum_nonneg (x P y : ℕ) : 0 ≤ stripPrimeSum x P y := by
  rw [stripPrimeSum]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepR_nonneg P n)) (Nat.cast_nonneg _)

theorem e2PrimeSum_nonneg (x z P : ℕ) : 0 ≤ e2PrimeSum x z P := by
  rw [e2PrimeSum]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepR_nonneg P n)) (e2Ind_nonneg z (n + 2))

theorem p1PrimeSum_nonneg (x P : ℕ) : 0 ≤ p1PrimeSum x P := by
  rw [p1PrimeSum]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepR_nonneg P n)) (p1Ind_nonneg (n + 2))

/-- The razor value is capped by the A₁ carrier alone (the subtracted carriers are nonneg). -/
theorem p2RazorLHS_le_A1primeSum (x P y : ℕ) : p2RazorLHS x P y ≤ A1primeSum x P := by
  have h1 := omegaPrimeSum_nonneg x P y
  have h2 := triplePrimeSum_nonneg x P y
  have h3 := stripPrimeSum_nonneg x P y
  rw [p2RazorLHS]; linarith

/-- **The P₁-razor reduction — one inequality, two readings.**  (i) The P₁-form of the landed
razor honestly lower-bounds the twin carrier: `p1RazorValue ≤ p1PrimeSum` — the structural
analogue of `razor_reduction` LANDS at the P₁ target.  (ii) Read as a cap: the P₁-razor's
guaranteed value never exceeds the twin mass itself, so landed material alone can never certify
it positive (the R4-safe direction); the Axis-B question is exactly whether it goes NEGATIVE. -/
theorem p1_razor_reduction {x z P y : ℕ} (hx : 2 ≤ x) (hyx : x < (y + 1) ^ 3)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P) :
    p1RazorValue x z P y ≤ p1PrimeSum x P := by
  have hred : p2RazorLHS x P y ≤ p2PrimeSum x z P := by
    rw [p2RazorLHS]; exact razor_reduction hx hyx hPfull
  have hsplit := p2PrimeSum_split x z P
  rw [p1RazorValue]
  linarith

/-- **The deficit identity.**  `p1RazorValue = p1PrimeSum − (razor slack on the P₂ carrier)`:
the P₁-razor value is negative exactly when the landed razor's slack `p2PrimeSum − p2RazorLHS`
EXCEEDS the twin mass.  Landed certificates are all one-sided the wrong way for the slack (lower
on A₁, upper on A₂/A₃/strip), which is why the deficit needs the two named gaps of Part F. -/
theorem p1RazorValue_eq (x z P y : ℕ) :
    p1RazorValue x z P y = p1PrimeSum x P - (p2PrimeSum x z P - p2RazorLHS x P y) := by
  rw [p1RazorValue, p2PrimeSum_split]; ring

/-! ## Part E — inhabitation (the anti-vacuity ritual)

The NEW carriers are certified nonvacuous at a genuine toy operating point `(x, z, P, y) =
(35, 2, 1, 3)`: `hPfull` is vacuously true (no primes `< 2`), `hyx : 35 < 4³` holds, and the
window `[17, 33]` contains both a twin point (`17`, with `19` prime) and an E2 point (`19`, with
`21 = 3·7`).  So the full P₁-razor reduction chain is inhabited, and — decisively for Axis B —
the deficit driver `e2PrimeSum` is a genuinely POSITIVE mass, not an empty-sum artifact.  (These
witnesses carry no twin-prime content: they certify only that the finite carrier sums at `x = 35`
are positive.) -/

/-- The E2 carrier (the deficit driver) is inhabited: at `x = 35`, the window point `n = 19`
is prime with `19 + 2 = 21 = 3·7` a two-factor number. -/
theorem e2_carrier_inhabited : 0 < e2PrimeSum 35 2 1 := by
  have hmem : (19 : ℕ) ∈ twinWindow 35 := by
    rw [twinWindow]; exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have hterm : vonMangoldt 19 * keepR 1 19 * e2Ind 2 (19 + 2) = Real.log 19 := by
    have hk : keepR 1 19 = 1 := by
      unfold keepR; rw [if_pos ⟨by norm_num, Nat.coprime_one_left _⟩]
    have he : e2Ind 2 (19 + 2) = 1 := by
      unfold e2Ind
      rw [if_pos ⟨3, 7, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩]
    rw [hk, he, mul_one, mul_one, vonMangoldt_apply_prime (by norm_num)]
    norm_num
  have hsum : Real.log 19 ≤ e2PrimeSum 35 2 1 := by
    rw [e2PrimeSum, ← hterm]
    exact Finset.single_le_sum
      (f := fun n => vonMangoldt n * keepR 1 n * e2Ind 2 (n + 2))
      (fun n _ => mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepR_nonneg 1 n))
        (e2Ind_nonneg 2 (n + 2))) hmem
  have hpos : (0 : ℝ) < Real.log 19 := Real.log_pos (by norm_num)
  linarith

/-- The twin carrier (the P₁ target) is inhabited: at `x = 35`, the window point `n = 17` is
prime with `17 + 2 = 19` prime. -/
theorem p1_carrier_inhabited : 0 < p1PrimeSum 35 1 := by
  have hmem : (17 : ℕ) ∈ twinWindow 35 := by
    rw [twinWindow]; exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have hterm : vonMangoldt 17 * keepR 1 17 * p1Ind (17 + 2) = Real.log 17 := by
    have hk : keepR 1 17 = 1 := by
      unfold keepR; rw [if_pos ⟨by norm_num, Nat.coprime_one_left _⟩]
    have hp : p1Ind (17 + 2) = 1 := by
      unfold p1Ind; rw [if_pos (by norm_num : Nat.Prime (17 + 2))]
    rw [hk, hp, mul_one, mul_one, vonMangoldt_apply_prime (by norm_num)]
    norm_num
  have hsum : Real.log 17 ≤ p1PrimeSum 35 1 := by
    rw [p1PrimeSum, ← hterm]
    exact Finset.single_le_sum
      (f := fun n => vonMangoldt n * keepR 1 n * p1Ind (n + 2))
      (fun n _ => mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepR_nonneg 1 n))
        (p1Ind_nonneg (n + 2))) hmem
  have hpos : (0 : ℝ) < Real.log 17 := Real.log_pos (by norm_num)
  linarith

/-! ## Part F — the conditional deficit (the Axis-B deliverable, honest form)

The two named gaps (GAP-U, GAP-E — see the module docstring's ledger) enter as hypotheses about
the LANDED carriers; the arithmetic gate `a1up + δ ≤ e2lo` is the exact quantitative content the
corpus does not yet carry.  No abstract Φ: every hypothesis is about `A1primeSum`/`e2PrimeSum`
at a landed operating tuple. -/

/-- **`twin_razor_deficit` — the Axis-B deliverable (conditional form).**  Given an X_W-scale
upper bound on the sifted prime mass (GAP-U: the F-side upper-sieve certificate, NOT in the
corpus), an X_W-scale lower bound on the two-factor mass (GAP-E: a Chen-type semiprime count
from below, NOT in the corpus), and the arithmetic gate `a1up + δ ≤ e2lo`, the P₁-form of the
landed razor is NEGATIVE with explicit deficit `δ·XW`:

  `p1RazorValue ≤ −δ·XW`.

The gate is exactly where the deficit lives: by `deficit_floor_of_certs` any discharge at the
certified operating point forces `e2lo ≥ 1/200 + δ` (above the razor's whole certified margin),
and classically `a1up ≈ F(4)`-scale while `e2lo` is Chen's semiprime constant — the comparison
the landed one-sided certificates cannot make. -/
theorem twin_razor_deficit {x z P y : ℕ} {XW a1up e2lo δ : ℝ}
    (hXW : 0 < XW)
    (hA1up : A1primeSum x P ≤ XW * a1up)
    (hE2lo : XW * e2lo ≤ e2PrimeSum x z P)
    (hgap : a1up + δ ≤ e2lo) :
    p1RazorValue x z P y ≤ -(δ * XW) := by
  have hle : p2RazorLHS x P y ≤ XW * a1up :=
    le_trans (p2RazorLHS_le_A1primeSum x P y) hA1up
  have hmul : XW * (a1up - e2lo) ≤ XW * (-δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hXW.le
  have hr1 : XW * a1up - XW * e2lo = XW * (a1up - e2lo) := by ring
  have hr2 : XW * (-δ) = -(δ * XW) := by ring
  rw [p1RazorValue]
  linarith

/-- The literal frozen shape `(P₁-razor value) ≤ −δ`, for normalisations `XW ≥ 1` and `δ ≥ 0`. -/
theorem twin_razor_deficit' {x z P y : ℕ} {XW a1up e2lo δ : ℝ}
    (hXW : 1 ≤ XW) (hδ : 0 ≤ δ)
    (hA1up : A1primeSum x P ≤ XW * a1up)
    (hE2lo : XW * e2lo ≤ e2PrimeSum x z P)
    (hgap : a1up + δ ≤ e2lo) :
    p1RazorValue x z P y ≤ -δ := by
  have h := twin_razor_deficit (y := y) (by linarith : (0:ℝ) < XW) hA1up hE2lo hgap
  nlinarith [h, mul_le_mul_of_nonneg_left hXW hδ]

/-! ## Part G — the certified floor: what the landed constants force on any discharge

These lemmas genuinely consume `razor_scalar_margin` (hence `cbar_lt` and the LogToolkit log
sandwiches) and pin the consistency landscape of Part F's hypotheses: the landed certificates
FLOOR the razor value at `XW/200`, so the deficit's `e2lo` must clear the razor's entire
certified output plus `δ` — the kernel-checked statement that the two-factor mass must exceed
everything the landed argument produces before the P₁-razor can go negative. -/

/-- The quantitative form of `hledger_at_certs`' algebra: at the certified per-carrier bounds
(the same inputs, `S` the strip value), the main-term ledger is floored at `XW/200`, not merely
positive.  Consumes `razor_scalar_margin` (`≥ 1/100`) against the error bundle (`≤ 1/200`). -/
theorem deficit_quant_ledger {XW mainA1 mainA2 mainA3 S e1 e2 e3 e4 : ℝ}
    (hXW : 0 < XW)
    (hE : e1 + e2 / 2 + e3 / 2 + e4 / 2 ≤ 1 / 200)
    (hmA1 : XW * (9779 / 10000 - e1) ≤ mainA1)
    (hmA2 : mainA2 ≤ XW * ((3 + 43 / 75) * (Real.log 6 / 4) + e2))
    (hmA3 : mainA3 ≤ XW * (cbar * (3 / 8) * (243 / 100) + e3))
    (hstrip : S ≤ XW * e4) :
    XW * (1 / 200) ≤ mainA1 - mainA2 / 2 - mainA3 / 2 - S / 2 := by
  have hM := razor_scalar_margin
  have hgap : XW * (1 / 200)
      ≤ XW * ((9779 / 10000 - (3 + 43 / 75) * (Real.log 6 / 4) / 2
          - cbar * (3 / 8) * (243 / 100) / 2) - (e1 + e2 / 2 + e3 / 2 + e4 / 2)) := by
    apply mul_le_mul_of_nonneg_left _ hXW.le
    linarith
  have hexpand : XW * ((9779 / 10000 - (3 + 43 / 75) * (Real.log 6 / 4) / 2
          - cbar * (3 / 8) * (243 / 100) / 2) - (e1 + e2 / 2 + e3 / 2 + e4 / 2))
      = XW * (9779 / 10000 - e1) - XW * ((3 + 43 / 75) * (Real.log 6 / 4) + e2) / 2
        - XW * (cbar * (3 / 8) * (243 / 100) + e3) / 2 - XW * e4 / 2 := by ring
  rw [hexpand] at hgap
  linarith

/-- **The certified razor floor at the carriers.**  Under the full landed package — structure
(`hx`/`hz`/`hPfull`), the certified normalised bounds (as `hledger_at_certs`), and the carrier
links (`hA1`/`hA2`/`hA3`, the H-package slots) — the razor value is floored: `XW/200 ≤
p2RazorLHS`.  Any upper bound `a1up` of GAP-U therefore satisfies `1/200 ≤ a1up`: the deficit
hypotheses are consistent with the landed certificates only above this floor. -/
theorem p2RazorLHS_ge_of_certs {x z P y : ℕ} {XW mainA1 mainA2 mainA3 e1 e2 e3 e4 : ℝ}
    (hx : 2 ≤ x) (hz : 2 ≤ z)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hXW : 0 < XW)
    (hE : e1 + e2 / 2 + e3 / 2 + e4 / 2 ≤ 1 / 200)
    (hmA1 : XW * (9779 / 10000 - e1) ≤ mainA1)
    (hmA2 : mainA2 ≤ XW * ((3 + 43 / 75) * (Real.log 6 / 4) + e2))
    (hmA3 : mainA3 ≤ XW * (cbar * (3 / 8) * (243 / 100) + e3))
    (hstrip : Real.log x * (x : ℝ) / ((z : ℝ) - 1) ≤ XW * e4)
    (hA1 : mainA1 ≤ A1primeSum x P)
    (hA2 : omegaPrimeSum x P y ≤ mainA2)
    (hA3 : triplePrimeSum x P y ≤ mainA3) :
    XW * (1 / 200) ≤ p2RazorLHS x P y := by
  have hq := deficit_quant_ledger hXW hE hmA1 hmA2 hmA3 hstrip
  have hS := stripPrimeSum_le (y := y) hx hz hPfull
  rw [p2RazorLHS]
  linarith

/-- **The razor-derived E2 lower bound is capped by its own source.**  Adding a twin-mass budget
`hTwinUp : p1PrimeSum ≤ XW·tup` to the certified package yields `XW·(1/200 − tup) ≤ e2PrimeSum`
— the ONLY lower bound on the two-factor mass the landed corpus can produce, and it is
structurally `≤` the razor's own value: feeding it back into the deficit gives
`p1RazorValue ≤ XW·tup` (nonnegative for `tup ≥ 0`), never a negative bound.  This is the
kernel-checked self-funding no-go: GAP-E cannot be discharged from the razor. -/
theorem e2_lower_of_certs_twinup {x z P y : ℕ} {XW mainA1 mainA2 mainA3 e1 e2 e3 e4 tup : ℝ}
    (hx : 2 ≤ x) (hz : 2 ≤ z) (hyx : x < (y + 1) ^ 3)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hXW : 0 < XW)
    (hE : e1 + e2 / 2 + e3 / 2 + e4 / 2 ≤ 1 / 200)
    (hmA1 : XW * (9779 / 10000 - e1) ≤ mainA1)
    (hmA2 : mainA2 ≤ XW * ((3 + 43 / 75) * (Real.log 6 / 4) + e2))
    (hmA3 : mainA3 ≤ XW * (cbar * (3 / 8) * (243 / 100) + e3))
    (hstrip : Real.log x * (x : ℝ) / ((z : ℝ) - 1) ≤ XW * e4)
    (hA1 : mainA1 ≤ A1primeSum x P)
    (hA2 : omegaPrimeSum x P y ≤ mainA2)
    (hA3 : triplePrimeSum x P y ≤ mainA3)
    (hTwinUp : p1PrimeSum x P ≤ XW * tup) :
    XW * (1 / 200 - tup) ≤ e2PrimeSum x z P := by
  have hq := p2RazorLHS_ge_of_certs hx hz hPfull hXW hE hmA1 hmA2 hmA3 hstrip hA1 hA2 hA3
  have hred : p2RazorLHS x P y ≤ p2PrimeSum x z P := by
    rw [p2RazorLHS]; exact razor_reduction hx hyx hPfull
  have hsplit := p2PrimeSum_split x z P
  have hring : XW * (1 / 200 - tup) = XW * (1 / 200) - XW * tup := by ring
  linarith

/-- **The deficit floor.**  Any discharge of `twin_razor_deficit`'s hypotheses at the certified
operating point must certify the two-factor mass ABOVE the razor's entire certified margin plus
the deficit: `1/200 + δ ≤ e2lo`.  (The certified floor forces `1/200 ≤ a1up`, and the gate adds
`δ`.)  This is the quantitative shape of what GAP-E must deliver. -/
theorem deficit_floor_of_certs {x z P y : ℕ}
    {XW mainA1 mainA2 mainA3 e1 e2 e3 e4 a1up e2lo δ : ℝ}
    (hx : 2 ≤ x) (hz : 2 ≤ z)
    (hPfull : ∀ q, q.Prime → q < z → q ∣ P)
    (hXW : 0 < XW)
    (hE : e1 + e2 / 2 + e3 / 2 + e4 / 2 ≤ 1 / 200)
    (hmA1 : XW * (9779 / 10000 - e1) ≤ mainA1)
    (hmA2 : mainA2 ≤ XW * ((3 + 43 / 75) * (Real.log 6 / 4) + e2))
    (hmA3 : mainA3 ≤ XW * (cbar * (3 / 8) * (243 / 100) + e3))
    (hstrip : Real.log x * (x : ℝ) / ((z : ℝ) - 1) ≤ XW * e4)
    (hA1 : mainA1 ≤ A1primeSum x P)
    (hA2 : omegaPrimeSum x P y ≤ mainA2)
    (hA3 : triplePrimeSum x P y ≤ mainA3)
    (hA1up : A1primeSum x P ≤ XW * a1up)
    (hgap : a1up + δ ≤ e2lo) :
    1 / 200 + δ ≤ e2lo := by
  have hq := p2RazorLHS_ge_of_certs hx hz hPfull hXW hE hmA1 hmA2 hmA3 hstrip hA1 hA2 hA3
  have h1 : XW * (1 / 200) ≤ XW * a1up :=
    le_trans hq (le_trans (p2RazorLHS_le_A1primeSum x P y) hA1up)
  have h2 : (1 : ℝ) / 200 ≤ a1up := le_of_mul_le_mul_left h1 hXW
  linarith

/-! ## Part H — the W-family mirror (H-AMENDMENT 2's live carriers)

The headline consumer is `chen_of_hypotheses_W` at the `keepW` carriers, so the P₁ split and the
deficit are mirrored there verbatim (the landed proofs consume the sifting data only through the
split bridge, exactly as in Assembly Parts H–K).  Inhabitation transfers through `keepW_one_zero`
(`Q = 1, a = 0` collapses `keepW` to `keepR`). -/

/-- The W-restricted P₁ (twin) carrier. -/
noncomputable def p1PrimeSumW (Q a x P : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepW Q a P n * p1Ind (n + 2)

/-- The W-restricted E2 carrier — the deficit driver at the live carriers. -/
noncomputable def e2PrimeSumW (Q a x z P : ℕ) : ℝ :=
  ∑ n ∈ twinWindow x, vonMangoldt n * keepW Q a P n * e2Ind z (n + 2)

/-- The W-razor's guaranteed expression (the LHS of `razor_reduction_W`), as a named value. -/
noncomputable def p2RazorLHSW (Q a x P y : ℕ) : ℝ :=
  A1primeSumW Q a x P - omegaPrimeSumW Q a x P y / 2 - triplePrimeSumW Q a x P y / 2
    - stripPrimeSumW Q a x P y / 2

/-- The P₁-razor value at the W carriers. -/
noncomputable def p1RazorValueW (Q a x z P y : ℕ) : ℝ :=
  p2RazorLHSW Q a x P y - e2PrimeSumW Q a x z P

/-- The carrier split at the W carriers. -/
theorem p2PrimeSumW_split (Q a x z P : ℕ) :
    p2PrimeSumW Q a x z P = p1PrimeSumW Q a x P + e2PrimeSumW Q a x z P := by
  rw [p2PrimeSumW, p1PrimeSumW, e2PrimeSumW, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by rw [p2Ind_split, mul_add]

theorem omegaPrimeSumW_nonneg (Q a x P y : ℕ) : 0 ≤ omegaPrimeSumW Q a x P y := by
  rw [omegaPrimeSumW]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepW_nonneg Q a P n)) (Nat.cast_nonneg _)

theorem triplePrimeSumW_nonneg (Q a x P y : ℕ) : 0 ≤ triplePrimeSumW Q a x P y := by
  rw [triplePrimeSumW]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepW_nonneg Q a P n)) (tripleT_nonneg y (n + 2))

theorem stripPrimeSumW_nonneg (Q a x P y : ℕ) : 0 ≤ stripPrimeSumW Q a x P y := by
  rw [stripPrimeSumW]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg vonMangoldt_nonneg (keepW_nonneg Q a P n)) (Nat.cast_nonneg _)

/-- The W-razor value is capped by the W A₁ carrier alone. -/
theorem p2RazorLHSW_le_A1primeSumW (Q a x P y : ℕ) :
    p2RazorLHSW Q a x P y ≤ A1primeSumW Q a x P := by
  have h1 := omegaPrimeSumW_nonneg Q a x P y
  have h2 := triplePrimeSumW_nonneg Q a x P y
  have h3 := stripPrimeSumW_nonneg Q a x P y
  rw [p2RazorLHSW]; linarith

/-- The P₁-razor reduction at the W carriers (both readings, as `p1_razor_reduction`). -/
theorem p1_razor_reduction_W {x z P y Q a w' : ℕ} (hx : 2 ≤ x) (hyx : x < (y + 1) ^ 3)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2)) :
    p1RazorValueW Q a x z P y ≤ p1PrimeSumW Q a x P := by
  have hred : p2RazorLHSW Q a x P y ≤ p2PrimeSumW Q a x z P := by
    rw [p2RazorLHSW]; exact razor_reduction_W hx hyx hQfull hPfull' hQa2
  have hsplit := p2PrimeSumW_split Q a x z P
  rw [p1RazorValueW]
  linarith

/-- **The conditional deficit at the live (W) carriers** — `twin_razor_deficit` verbatim with the
same two named gaps, now about `A1primeSumW`/`e2PrimeSumW`. -/
theorem twin_razor_deficit_W {Q a x z P y : ℕ} {XW a1up e2lo δ : ℝ}
    (hXW : 0 < XW)
    (hA1up : A1primeSumW Q a x P ≤ XW * a1up)
    (hE2lo : XW * e2lo ≤ e2PrimeSumW Q a x z P)
    (hgap : a1up + δ ≤ e2lo) :
    p1RazorValueW Q a x z P y ≤ -(δ * XW) := by
  have hle : p2RazorLHSW Q a x P y ≤ XW * a1up :=
    le_trans (p2RazorLHSW_le_A1primeSumW Q a x P y) hA1up
  have hmul : XW * (a1up - e2lo) ≤ XW * (-δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hXW.le
  have hr1 : XW * a1up - XW * e2lo = XW * (a1up - e2lo) := by ring
  have hr2 : XW * (-δ) = -(δ * XW) := by ring
  rw [p1RazorValueW]
  linarith

/-- `keepW` at `Q = 1, a = 0` collapses to `keepR` (the residue condition mod `1` is trivial):
the W-carriers inherit Part E's inhabitation. -/
theorem keepW_one_zero (P n : ℕ) : keepW 1 0 P n = keepR P n := by
  unfold keepW keepR
  by_cases h : Nat.Prime n ∧ Nat.Coprime P (n + 2)
  · rw [if_pos ⟨h.1, h.2, by omega⟩, if_pos h]
  · rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩), if_neg h]

/-- The W E2 carrier at `Q = 1, a = 0` equals the plain E2 carrier. -/
theorem e2PrimeSumW_one_zero (x z P : ℕ) : e2PrimeSumW 1 0 x z P = e2PrimeSum x z P := by
  rw [e2PrimeSumW, e2PrimeSum]
  exact Finset.sum_congr rfl fun n _ => by rw [keepW_one_zero]

/-- The deficit driver is inhabited at the live carriers too. -/
theorem e2W_carrier_inhabited : 0 < e2PrimeSumW 1 0 35 2 1 := by
  rw [e2PrimeSumW_one_zero]; exact e2_carrier_inhabited

end Salt.Chen
