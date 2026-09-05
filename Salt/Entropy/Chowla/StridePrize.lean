/-
# λ-BV wave 2-S, step F5 — THE PRIZE STATEMENT AND THE COMPOSITION AT A BINDER (the RIPE block)

**Frozen statement-only 2026-09-04 18:4x (math, Fable head on kriterion), from the price brief
`2026-09-04-math-PRICE-lbv-w2S-F5-grade-line.md` and the helm's word 18:38 ("RIPE WITHOUT THE FORK:
F5-E, F5-P, F5-C's statement — fire on ONE Opus").**  The grade re-cut itself (the road's envelope
`doorRhoOfDelta` at `2^11`, the α″ arm) is a STATEMENT decision reserved to the Captain and is NOT
in this file; everything here is stated so that its discharge after that re-cut is one line.

THE DEMAND, at the landed object (`log_chowla_aff_of_door_crowned_unslotted`,
`StrideEntropyReceipt.lean:73`): the door at grade `a·Zr·ρ + E` with `ρ ≤ 1/(837782·k²)`, `Zr ≤
1.02`
beside `∀ ρ' ≤ δ₀, door ρ' → ¬ fails` with `1/(838400·k²) ≤ δ₀`, `k = a·h` — the composition
`a·Zr·ρ + E ≤ δ₀` is MISSED by `1.020753·a`.  At the graded head (`ρ ≤ 1/(837782·2^11·k²)`) it
CLOSES
with `a ≤ 1096` (`hah7`): `a·Zr·ρ ≤ 1117.9/(837782·2048·k²) = 0.5462/(838400·k²)`, and `E` is free
at `Ra.x/Ra.ω ≥ Ra.Hhi ≥ Ra.Hlo ≥ flatDesignBase A ≥ 2^600` and `log Ra.ω ≥ 65` (the regime's
`hωbig`): `E ≤ 2^539/(2^600·64) ≤ 2^{-67} ≤ 0.45/(838400·1096²)`.

THE PRIZE, per the helm's K3 word (F4b A13) and F4a verdict A8(i): the landed `LogChowlaAffSupply`
(`AffineFork.lean:96`, `R.Hlo = flatDesignBase A`) is UNTOUCHED; the crown exports `≤`, so the prize
gets a SIBLING `LogChowlaAffSupplyW` at `flatDesignBase A ≤ R.Hlo`, which its consumers survive by
one
line (`zRough_oddOmega_infinite_of_affSupply` uses `hHloeq` only through `flatDesignBase A ≤ R.x /
R.ω`).
`hgcd : Nat.gcd (b + h) a ∣ h` is DERIVED from the consumer's `hcop : Nat.Coprime (r·(r+2)) P` at
`(P, r, 2)` (`gcd_dvd_two_of_coprime`), so the consumers gain no binder.

⛔ HONEST LABEL.  Every declaration below is statement-only at the freeze (sorry-bodied, recipe in
the
docstring), built as a module through `../saltbuild.sh`; ONE Opus executor fires on the helm's word.
Nothing here closes the prize: `logChowlaAffSupplyW_of_headG` takes the GRADED head's conclusion as
a
BINDER (under an `∃`, two facts compose only through the same witness — the landed head's statement
cannot carry the finer grade, so the composition is ripe only at a binder; its discharge after the
Captain's word on the envelope is one application).  The unconditional prize at `primorial z ≤ 548`
(`z ≤ 7`: `z`-rough + `Ω(n(n+2))` odd, Tao Thm 2.3 at one class — NOT almost-primality) waits on
that
word.  Nothing here bears on twin primes.  ⛔ MERGE FENCE (iron rule 2): `math/lbv-w2s-f5` never
reaches `main` until every obligation in this file lands sorry-free.
-/
import Salt.Entropy.Chowla.StrideShell
import Salt.Entropy.Chowla.AffineFork
import Mathlib

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ## F5-E — the design base clears `2^600` -/

/-- **F5-E (class A).**  `flatDesignBase A = ⌈exp(exp(3.2·A))⌉₊ ≥ 2^600` at `A ≥ 162`:
`Nat.le_ceil`-shape (`Nat.le_ceil` / `Nat.ceil_le`), `2^600 = exp(600·log 2)` (`Real.exp_log`,
`Real.rpow_natCast`… or `Real.exp_nat_mul`), `600·log 2 < 416 < 1 + 518.4 ≤ exp(3.2·162) ≤
exp(3.2·A)`
(`Real.log_two_lt_d9`, `Real.add_one_le_exp`, `Real.exp_le_exp`), then `Real.exp_le_exp` once more.
The twin of `flatDoorM_ge_pow355` (`FlatFloorBump.lean:113`) at the base instead of the modulus. -/
theorem flatDesignBase_ge_pow600 {A : ℝ} (hA : 162 ≤ A) :
    (2 : ℕ) ^ 600 ≤ flatDesignBase A := by
  sorry

/-! ## F5-P — the prize statement at the crown's `≤` -/

/-- **F5-P0 (def) — THE SUPPLY DEMAND AT THE CROWN'S FLOOR.**  `LogChowlaAffSupply`
(`AffineFork.lean:96`)
with `R.Hlo = flatDesignBase A` relaxed to `flatDesignBase A ≤ R.Hlo` — the form the affine crown
exports (`mrtUniformityXiL2AffW_holds_flat_stride`: `Ra.Hlo = Rd.a · flatDesignBase A`, the
builder's
stride not exported).  The landed `=` def is untouched (F4a verdict A8(i)). -/
def LogChowlaAffSupplyW (a b h : ℕ) : Prop :=
  ∀ A₀ : ℝ, ∃ A : ℝ, 162 ≤ A ∧ A₀ ≤ A ∧
    ∃ R : ChowlaRegime, flatDesignBase A ≤ R.Hlo ∧ ¬ logChowlaFailsAff a b h R.eps R.x R.ω

/-- **F5-P1 (class A) — the landed supply implies the sibling.**  `intro A₀; obtain ⟨A, hA, hA₀, R,
hHlo, hnf⟩ := hsup A₀; exact ⟨A, hA, hA₀, R, hHlo.ge, hnf⟩`. -/
theorem logChowlaAffSupplyW_of_supply {a b h : ℕ} (hsup : LogChowlaAffSupply a b h) :
    LogChowlaAffSupplyW a b h := by
  sorry

/-- **F5-P2 (class A) — `hgcd` from the consumer's coprimality.**  `Nat.Coprime (r·(r+2)) P` gives
`Nat.Coprime (r + 2) P` (`Nat.Coprime.coprime_dvd_left (dvd_mul_left (r + 2) r) hcop`, the move at
`AffineFork.lean:228`), so `Nat.gcd (r + 2) P = 1` (`Nat.Coprime.gcd_eq_one`) and `1 ∣ 2`
(`one_dvd`).  This is `hgcd : Nat.gcd (b + h) a ∣ h` at `(a, b, h) := (P, r, 2)` — the freeze's
spelling (helm K3), strictly weaker than `Coprime`. -/
theorem gcd_dvd_two_of_coprime {P r : ℕ} (hcop : Nat.Coprime (r * (r + 2)) P) :
    Nat.gcd (r + 2) P ∣ 2 := by
  sorry

/-- **F5-P3 (class B) — the consumer at the sibling supply.** 
`zRough_oddOmega_infinite_of_affSupply`
(`AffineFork.lean:302`) with ONE line changed: where the landed proof does `rw [← hHloeq]; exact
le_trans R.hHlohi R.hheadroom` to obtain `flatDesignBase A ≤ R.x / R.ω`, use `le_trans hHlole
(le_trans R.hHlohi R.hheadroom)`.  Everything else verbatim (`Set.infinite_of_not_bddAbove`,
`flatDesignBase_unbounded`, `exists_affSurvivor_of_not_failsAff hP hnf`,
`coprime_twinProd_of_affine`,
`liouville_shift_two_eq_neg_one_iff`, `omega`). -/
theorem zRough_oddOmega_infinite_of_affSupplyW {P r : ℕ} (hP : 0 < P)
    (hcop : Nat.Coprime (r * (r + 2)) P) (hsup : LogChowlaAffSupplyW P r 2) :
    {n : ℕ | Nat.Coprime (n * (n + 2)) P
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))}.Infinite := by
  sorry

/-- **F5-P4 (class A) — at the primorial.**  `zRough_oddOmega_infinite_of_affSupplyW (primorial_pos
z)
hcop hsup` under `Set.Infinite.mono` with `rough_of_coprime_primorial` — the landed
`zRough_oddOmega_infinite_of_affSupply_primorial` (`AffineFork.lean:335`) at the sibling. -/
theorem zRough_oddOmega_infinite_of_affSupplyW_primorial {z r : ℕ}
    (hcop : Nat.Coprime (r * (r + 2)) (primorial z))
    (hsup : LogChowlaAffSupplyW (primorial z) r 2) :
    {n : ℕ | (∀ p ∈ (n * (n + 2)).primeFactors, z < p)
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))}.Infinite := by
  sorry

/-! ## F5-C — the composition, at the GRADED head as a binder -/

/-- **F5-C0 (def) — THE GRADED AFFINE HEAD'S CONCLUSION AT `A₀`.**  Byte for byte the conclusion of
`log_chowla_aff_of_door_crowned_unslotted a b h … A₀` (`StrideEntropyReceipt.lean:76-84`) with the
door's grade ceiling `ρ ≤ 1/(837782·(ah)²)` re-cut to **`ρ ≤ 1/(837782·2^11·(ah)²)`** — the shape
the
head exports once the road's envelope `doorRhoOfDelta` carries the `2^11` (the α″ arm; the Captain's
statement decision).  A def so the composition and the supply are stated ONCE against it. -/
def GradedAffHeadAt (a b h : ℕ) (A₀ : ℝ) : Prop :=
  ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
    ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
      flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
      (∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2) ∧
        1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
        E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
            * (Real.log (Ra.ω : ℝ) - 1)) ∧
        MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E)) ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) ≤ δ₀ ∧
        ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ δ₀ → MRTUniformityXiL2AffW h Ra ρ' →
          ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω

/-- **F5-C (class B) — THE COMPOSITION.**  From the graded head at `A₀`: `obtain` the two payloads
(ONE witness `Ra`, both facts leave through it); `hk : a ≤ 1096` from
`h_le_1096_of_log_le_seven (Nat.mul_pos ha hh) hah7` and `a ≤ a·h`; **`hle : a·Zr·ρ + E ≤ δ₀`** by
(i) `a·Zr·ρ ≤ 1096·1.02·(1/(837782·2^11·k²)) ≤ (0.55)·(1/(838400·k²))` (`mul_le_mul` three times,
`div_le_div_iff₀`, `norm_num`/`nlinarith` on the numerals — `1096·1.02·838400 = 9.373×10⁸ ≤
0.55·837782·2048 = 9.437×10⁸`), (ii) `E ≤ (0.45)·(1/(838400·k²))`: `a·(x/ω) + 1 ≥ a·(x/ω) ≥ a·2^600`
from `hheadroom : Hhi ≤ x/ω`, `hHlohi`, `flatDesignBase_ge_pow600 hA162`, `hHlo`; `log ω − 1 ≥ 64`
from the regime's `hωbig` (`Regime.lean`, the `64/ε + 1 ≤ log ω` arm at `ε ≤ 1`); so `E ≤
2^539·a/(a·2^600·64)
= 2^{-67}` and `2^{-67}·838400·1096² ≤ 0.45`; then `linarith`.  Finally `himpl (a·Zr·ρ + E)
(by positivity) hle hdoor` and re-export `ε, A, Ra` with the same conjuncts.  Class B: numerals and
one cast (`((Ra.x / Ra.ω : ℕ) : ℝ)` against `Nat.cast_le`). -/
theorem log_chowla_aff_composed_of_headG (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7) (A₀ : ℝ) (hheadG : GradedAffHeadAt a b h A₀) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω := by
  sorry

/-- **F5-S (class A) — THE SUPPLY AT THE GRADED HEAD.**  `intro A₀; obtain ⟨ε, A, -, -, hA162, hA₀A,
Ra, -, -, -, hHlo, -, hnf⟩ := log_chowla_aff_composed_of_headG a b h ha hh hah7 A₀ (hheadG A₀);
exact ⟨A, hA162, hA₀A, Ra.toChowlaRegime, hHlo, hnf⟩` (`Ra.eps = Ra.toChowlaRegime.eps` by `rfl`).
With `hheadG` discharged by the graded head after the envelope re-cut, this IS
`LogChowlaAffSupplyW a b h` at every `(a, b, h)` with `b < a`, `0 < h`, `gcd(b+h, a) ∣ h`,
`log(ah) ≤ 7` — the stride supply at `a ≥ 2` that `AffineFork.lean:96` records as held by nobody. -/
theorem logChowlaAffSupplyW_of_headG (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7) (hheadG : ∀ A₀ : ℝ, GradedAffHeadAt a b h A₀) :
    LogChowlaAffSupplyW a b h := by
  sorry

end Salt.Entropy.Chowla
