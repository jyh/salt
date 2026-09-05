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
with `a ≤ 1096` (`hah7`): `a·Zr·ρ ≤ 1117.92/(837782·2048·k²) ≤ 0.5463/(838400·k²)` (exact ratio
`0.546262…`), and `E` is free at `Ra.x/Ra.ω ≥ Ra.Hhi ≥ Ra.Hlo ≥ flatDesignBase A ≥ 2^600` and
`log Ra.ω ≥ 129` (the landed `regime_logOmega_ge`, `SignSplit.lean:174`): the landed route spends
only
`log ω − 1 ≥ 1`, so `E ≤ 2^539/2^600 = 2^{-61} ≤ 0.45/(838400·1096²)` (6 orders of room).

THE PRIZE, per the helm's K3 word (F4b A13) and F4a verdict A8(i): the landed `LogChowlaAffSupply`
(`AffineFork.lean:96`, `R.Hlo = flatDesignBase A`) is UNTOUCHED; the crown exports `≤`, so the prize
gets a SIBLING `LogChowlaAffSupplyW` at `flatDesignBase A ≤ R.Hlo`, which its consumers survive by
one
line (`zRough_oddOmega_infinite_of_affSupply` uses `hHloeq` only through `flatDesignBase A ≤ R.x /
R.ω`).
`hgcd : Nat.gcd (b + h) a ∣ h` is DERIVED from the consumer's `hcop : Nat.Coprime (r·(r+2)) P` at
`(P, r, 2)` (`gcd_dvd_two_of_coprime`), so the consumers gain no binder.

⛔ HONEST LABEL.  LANDED 2026-09-04 19:0x: every declaration below is sorry-free (ONE Opus executor,
7/7, 6 at one attempt; every theorem `[propext, Classical.choice, Quot.sound]` or less; audited in
`Salt.Entropy.All`).  The `E` arm landed at the regime's own `regime_logOmega_ge` (`log ω ≥ 129`)
rather than the `hωbig` field the recipe named.  Nothing here closes the prize:
`logChowlaAffSupplyW_of_headG` takes the GRADED head's conclusion as a BINDER (under an `∃`, two
facts compose only through the same witness — the landed head's statement cannot carry the finer
grade, so the composition is ripe only at a binder; its discharge is one application of the graded
sibling head once the β lane lands).  The unconditional prize at `primorial z ≤ 548` (`z ≤ 10`, the
gate being on the primorial — `primorial 8 = primorial 9 = primorial 10 = 210`:
`z`-rough + `Ω(n(n+2))` odd, Tao Thm 2.3 at one class — NOT almost-primality) waits on that lane.
Nothing here bears on twin primes.
-/
import Salt.Entropy.Chowla.StrideShell
import Salt.Entropy.Chowla.AffineFork
import Mathlib

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ## F5-E — the design base clears `2^600` -/

set_option exponentiation.threshold 4000 in
/-- **F5-E (class A).**  `flatDesignBase A = ⌈exp(exp(3.2·A))⌉₊ ≥ 2^600` at `A ≥ 162`.  THE LANDED
ROUTE: `Real.log_pow` + `Real.exp_log` give `(2:ℝ)^600 = exp(600·log 2)`; `600·log 2 < 416`
(`Real.log_two_lt_d9`) and `416 ≤ 3.2·162 + 1 ≤ exp(3.2·162) ≤ exp(3.2·A)` (`Real.add_one_le_exp`,
`Real.exp_le_exp`); `Real.exp_le_exp` once more, then `Nat.le_ceil` after `rw [flatDesignBase]`, and
`exact_mod_cast`.  25 bits of margin (the composition's true floor is `2^575`).  The twin of
`flatDoorM_ge_pow355` (`FlatFloorBump.lean:113`) at the base instead of the modulus. -/
theorem flatDesignBase_ge_pow600 {A : ℝ} (hA : 162 ≤ A) :
    (2 : ℕ) ^ 600 ≤ flatDesignBase A := by
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlogpow : Real.log ((2 : ℝ) ^ (600 : ℕ)) = 600 * Real.log 2 := by
    rw [Real.log_pow]; norm_num
  have h2 : ((2 : ℝ) ^ (600 : ℕ)) = Real.exp (600 * Real.log 2) := by
    rw [← hlogpow, Real.exp_log (by positivity)]
  have hmono : Real.exp (3.2 * 162) ≤ Real.exp (3.2 * A) :=
    Real.exp_le_exp.mpr (by linarith)
  have hlin : 3.2 * 162 + 1 ≤ Real.exp (3.2 * 162) := Real.add_one_le_exp _
  have hbig : (416 : ℝ) ≤ Real.exp (3.2 * A) := by linarith
  have hchain : ((2 : ℝ) ^ (600 : ℕ)) ≤ Real.exp (Real.exp (3.2 * A)) := by
    rw [h2]
    exact Real.exp_le_exp.mpr (by linarith)
  have hceil : Real.exp (Real.exp (3.2 * A)) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    rw [flatDesignBase]; exact Nat.le_ceil _
  have hfin : (((2 : ℕ) ^ 600 : ℕ) : ℝ) ≤ ((flatDesignBase A : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hfin

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
  intro A₀
  obtain ⟨A, hA, hA₀, R, hHlo, hnf⟩ := hsup A₀
  exact ⟨A, hA, hA₀, R, hHlo.ge, hnf⟩

/-- **F5-P2 (class A) — `hgcd` from the consumer's coprimality.**  `Nat.Coprime (r·(r+2)) P` gives
`Nat.Coprime (r + 2) P` (`Nat.Coprime.coprime_dvd_left (dvd_mul_left (r + 2) r) hcop`, the move at
`AffineFork.lean:228`), so `Nat.gcd (r + 2) P = 1` (`Nat.Coprime.gcd_eq_one`) and `1 ∣ 2`
(`one_dvd`).  This is `hgcd : Nat.gcd (b + h) a ∣ h` at `(a, b, h) := (P, r, 2)` — the freeze's
spelling (helm K3), strictly weaker than `Coprime`. -/
theorem gcd_dvd_two_of_coprime {P r : ℕ} (hcop : Nat.Coprime (r * (r + 2)) P) :
    Nat.gcd (r + 2) P ∣ 2 := by
  have hr2 : Nat.Coprime (r + 2) P :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_left (r + 2) r) hcop
  rw [Nat.Coprime.gcd_eq_one hr2]
  exact one_dvd 2

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
  apply Set.infinite_of_not_bddAbove
  intro hbdd
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨A₀, hA₀⟩ := flatDesignBase_unbounded (M : ℝ)
  obtain ⟨A, -, hA₀A, R, hHlole, hnf⟩ := hsup A₀
  obtain ⟨n, hn, hprod⟩ := exists_affSurvivor_of_not_failsAff hP hnf
  rw [Finset.mem_Ioc] at hn
  have hbaseR : (M : ℝ) < ((flatDesignBase A : ℕ) : ℝ) := hA₀ A hA₀A
  have hbase : M < flatDesignBase A := by exact_mod_cast hbaseR
  have hle : flatDesignBase A ≤ R.x / R.ω :=
    le_trans hHlole (le_trans R.hHlohi R.hheadroom)
  have hMn : M < n := lt_trans hbase (lt_of_le_of_lt hle hn.1)
  have hnle : n ≤ P * n + r := le_trans (Nat.le_mul_of_pos_left n hP) (Nat.le_add_right _ _)
  have hmpos : 0 < P * n + r := lt_of_le_of_lt (Nat.zero_le M) (lt_of_lt_of_le hMn hnle)
  have hmem : P * n + r ∈ {n : ℕ | Nat.Coprime (n * (n + 2)) P
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))} := by
    refine ⟨coprime_twinProd_of_affine hcop n, ?_⟩
    exact (liouville_shift_two_eq_neg_one_iff hmpos).mp hprod
  have hub := hM hmem
  omega

/-- **F5-P4 (class A) — at the primorial.**  `zRough_oddOmega_infinite_of_affSupplyW (primorial_pos
z)
hcop hsup` under `Set.Infinite.mono` with `rough_of_coprime_primorial` — the landed
`zRough_oddOmega_infinite_of_affSupply_primorial` (`AffineFork.lean:335`) at the sibling. -/
theorem zRough_oddOmega_infinite_of_affSupplyW_primorial {z r : ℕ}
    (hcop : Nat.Coprime (r * (r + 2)) (primorial z))
    (hsup : LogChowlaAffSupplyW (primorial z) r 2) :
    {n : ℕ | (∀ p ∈ (n * (n + 2)).primeFactors, z < p)
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))}.Infinite := by
  have hinf := zRough_oddOmega_infinite_of_affSupplyW (primorial_pos z) hcop hsup
  exact hinf.mono (fun n hn => ⟨rough_of_coprime_primorial hn.1, hn.2⟩)

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

set_option exponentiation.threshold 4000 in
/-- **F5-C (class B) — THE COMPOSITION.**  From the graded head at `A₀`: `obtain` the two payloads
(ONE witness `Ra`, both facts leave through it); `hk : a ≤ 1096` from
`h_le_1096_of_log_le_seven (Nat.mul_pos ha hh) hah7` and `a ≤ a·h`; **`hle : a·Zr·ρ + E ≤ δ₀`** by
(i) `a·Zr·ρ ≤ 1096·1.02·(1/(837782·2^11·k²)) ≤ (0.55)·(1/(838400·k²))` (`mul_le_mul` three times,
`div_le_div_iff₀`, `norm_num`/`nlinarith` on the numerals — `1096·1.02·838400 = 9.373×10⁸ ≤
0.55·837782·2048 = 9.437×10⁸`), (ii) `E ≤ (0.45)·(1/(838400·k²))`: `a·(x/ω) + 1 ≥ a·(x/ω) ≥ a·2^600`
from `hheadroom : Hhi ≤ x/ω`, `hHlohi`, `flatDesignBase_ge_pow600 hA162`, `hHlo`; `log ω − 1 ≥ 1`
from
the LANDED `regime_logOmega_ge Ra.toChowlaRegime : 129 ≤ log Ra.ω` (`SignSplit.lean:174`; the
regime field
`hωbig` is the HBUDGET window-coupling floor, not this bound — verdict A6); so `E ≤
2^539·a/(a·2^600·1) =
2^{-61}` and `2^{-61}·838400·1096² ≤ 0.45`; then `linarith`.  Finally `himpl (a·Zr·ρ + E) hgpos hle
hdoor`
with `hgpos` from `hρ`, `hZr1`, `hE0` (a positive product plus a nonnegative), and re-export `ε, A,
Ra` with the same conjuncts.  Class B: numerals and
one cast (`((Ra.x / Ra.ω : ℕ) : ℝ)` against `Nat.cast_le`). -/
theorem log_chowla_aff_composed_of_headG (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7) (A₀ : ℝ) (hheadG : GradedAffHeadAt a b h A₀) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω := by
  obtain ⟨ε, A, hε, hεeq, hA162, hA₀A, Ra, hRa, hRb, hReps, hHlo, hdes,
    ⟨ρ, Zr, E, hρ, hρle, hZr1, hZr2, hE0, hEle, hdoor⟩,
    δ₀, hδ₀, hδ₀ge, himpl⟩ := hheadG
  -- ⟦the elementary casts⟧
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have ha1R : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hk1n : 1 ≤ a * h := Nat.mul_pos ha hh
  have hk1 : (1 : ℝ) ≤ ((a * h : ℕ) : ℝ) := by exact_mod_cast hk1n
  have hKpos : (0 : ℝ) < ((a * h : ℕ) : ℝ) ^ 2 := by nlinarith
  -- ⟦the `≤ 1096` reads⟧
  have hah1096 : a * h ≤ 1096 := h_le_1096_of_log_le_seven (Nat.mul_pos ha hh) hah7
  have ha1096 : a ≤ 1096 := le_trans (Nat.le_mul_of_pos_right a hh) hah1096
  have haR1096 : (a : ℝ) ≤ 1096 := by exact_mod_cast ha1096
  have hkR1096 : ((a * h : ℕ) : ℝ) ≤ 1096 := by exact_mod_cast hah1096
  -- ⟦THE DOOR ARM⟧ `a·Zr·ρ ≤ 0.55·δ₀`
  have hZrpos : (0 : ℝ) < Zr := lt_of_lt_of_le zero_lt_one hZr1
  have hstep1 : (a : ℝ) * Zr * ρ
      ≤ 1096 * 1.02 * (1 / (837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2)) := by
    have h1 : (a : ℝ) * Zr ≤ 1096 * 1.02 :=
      mul_le_mul haR1096 hZr2 (le_trans zero_le_one hZr1) (by norm_num)
    exact mul_le_mul h1 hρle hρ.le (by norm_num)
  have hstep2 : (1096 : ℝ) * 1.02 * (1 / (837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2))
      ≤ 0.55 * (1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2)) := by
    rw [mul_one_div, mul_one_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hKpos.le]
  have hdoorarm : (a : ℝ) * Zr * ρ ≤ 0.55 * δ₀ := by
    have h3 : (0.55 : ℝ) * (1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2)) ≤ 0.55 * δ₀ :=
      mul_le_mul_of_nonneg_left hδ₀ge (by norm_num)
    linarith
  -- ⟦THE `E` ARM⟧ the design floor under `x/ω`, and `log ω − 1 ≥ 1`
  have hXn : (2 : ℕ) ^ 600 ≤ Ra.x / Ra.ω :=
    le_trans (le_trans (flatDesignBase_ge_pow600 hA162) hHlo)
      (le_trans Ra.hHlohi Ra.hheadroom)
  have hcast600 : (((2 : ℕ) ^ 600 : ℕ) : ℝ) = (2 : ℝ) ^ 600 := by norm_num
  have hX : (2 : ℝ) ^ 600 ≤ ((Ra.x / Ra.ω : ℕ) : ℝ) := by
    rw [← hcast600]
    exact (Nat.cast_le (α := ℝ)).mpr hXn
  have hlog129 : (129 : ℝ) ≤ Real.log (Ra.ω : ℝ) := regime_logOmega_ge Ra.toChowlaRegime
  have hL1 : (1 : ℝ) ≤ Real.log (Ra.ω : ℝ) - 1 := by linarith
  have hnum1 : (0 : ℝ) < (a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1 := by positivity
  have hDge : (a : ℝ) * (2 : ℝ) ^ 600
      ≤ ((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1) * (Real.log (Ra.ω : ℝ) - 1) := by
    have h1 : (a : ℝ) * (2 : ℝ) ^ 600 ≤ (a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hX haR.le
    have h2 : ((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1) * 1
        ≤ ((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1) * (Real.log (Ra.ω : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hL1 hnum1.le
    linarith
  have hDpos : (0 : ℝ)
      < ((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1) * (Real.log (Ra.ω : ℝ) - 1) := by
    have hp : (0 : ℝ) < (a : ℝ) * (2 : ℝ) ^ 600 := by positivity
    linarith
  have hEt : E ≤ 0.45 * (1 / (838400 * (1096 : ℝ) ^ 2)) := by
    refine le_trans hEle ?_
    rw [mul_one_div, div_le_div_iff₀ hDpos (by norm_num)]
    nlinarith [hDge, haR.le]
  have hEarm : E ≤ 0.45 * δ₀ := by
    have h1 : (1 : ℝ) / (838400 * (1096 : ℝ) ^ 2)
        ≤ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      nlinarith [hk1, hkR1096]
    linarith
  -- ⟦THE COMPOSITION⟧
  have hle : (a : ℝ) * Zr * ρ + E ≤ δ₀ := by linarith
  have hgpos : (0 : ℝ) < (a : ℝ) * Zr * ρ + E := by
    have hp : (0 : ℝ) < (a : ℝ) * Zr * ρ := mul_pos (mul_pos haR hZrpos) hρ
    linarith
  exact ⟨ε, A, hε, hεeq, hA162, hA₀A, Ra, hRa, hRb, hReps, hHlo, hdes,
    himpl _ hgpos hle hdoor⟩

/-- **F5-S (class A) — THE SUPPLY AT THE GRADED HEAD.**  `intro A₀; obtain ⟨ε, A, -, -, hA162, hA₀A,
Ra, -, -, -, hHlo, -, hnf⟩ := log_chowla_aff_composed_of_headG a b h ha hh hah7 A₀ (hheadG A₀);
exact ⟨A, hA162, hA₀A, Ra.toChowlaRegime, hHlo, hnf⟩` (`Ra.eps = Ra.toChowlaRegime.eps` by `rfl`).
With `hheadG` discharged by the graded head after the envelope re-cut, this IS
`LogChowlaAffSupplyW a b h` at every `(a, b, h)` with `b < a`, `0 < h`, `gcd(b+h, a) ∣ h`,
`log(ah) ≤ 7` — the stride supply at `a ≥ 2` that `AffineFork.lean:96` records as held by nobody. -/
theorem logChowlaAffSupplyW_of_headG (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7) (hheadG : ∀ A₀ : ℝ, GradedAffHeadAt a b h A₀) :
    LogChowlaAffSupplyW a b h := by
  intro A₀
  obtain ⟨ε, A, -, -, hA162, hA₀A, Ra, -, -, -, hHlo, -, hnf⟩ :=
    log_chowla_aff_composed_of_headG a b h ha hh hah7 A₀ (hheadG A₀)
  exact ⟨A, hA162, hA₀A, Ra.toChowlaRegime, hHlo, hnf⟩

end Salt.Entropy.Chowla
