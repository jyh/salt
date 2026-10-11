/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# C1 — Maynard's `M₁₀₅ > 4`, by kernel reduction (the numeric gate of bounded gaps ≤ 600)

Basis `(1 − P₁)^b · P₂^c`, `b + 2c ≤ 11` (42 functions; Maynard, *Small gaps between primes*, Ann.
of Math. 181 (2015), §8) at
`k = 105`. `intg t k b c = b!·c!·t[c]/(k+b+2c)!` with `t = T k`, the truncated power `(Σ_j (2j)!/j!
xʲ)^k`; that this is the
Dirichlet main term of the basis is `Salt.MaynardK.T_eq_coeff` + `simplexInt_basisPoly`. `I = ∫ F²`
over `R₁₀₅`,
`J = ∫ (∫ F dt₁₀₅)²` over `R₁₀₄`; `M105_gt_four : 4 < 105·J/I` by `decide +kernel` (≈ 10 s; the
value is 4.0020697619…).
`H` is an admissible 105-tuple of diameter 636 (greedy residue sieve); 600 needs Engelsma's
published tuple.
-/

namespace Salt.MaynardK

/-- `(2j)!/j!` for `j ≤ 11`. -/
def g : List ℕ := (List.range 12).map fun j => (2 * j).factorial / j.factorial

/-- one multiplication by `Σ g_j xʲ`, truncated at degree 11. -/
def pmul (a : List ℕ) : List ℕ :=
  (List.range 12).map fun n => ((List.range (n + 1)).map fun i => a.getD i 0 * g.getD (n - i) 0).sum

/-- `T_k`. -/
def T (k : ℕ) : List ℕ := Nat.iterate pmul k (1 :: List.replicate 11 0)

def T105 : List ℕ := [1, 210, 23100, 1774360, 107061360, 5413048032, 238944301120, 9475939175040,
    344896263129600, 11717241583989760, 376857954396198912, 11621414455752192000]
def T104 : List ℕ := [1, 208, 22672, 1726400, 103309856, 5182611200, 227087148288, 8943434732544,
    323417467666176, 10922337815633920, 349406131256565760, 10724133611951718400]

theorem T105_eq : T 105 = T105 := by decide +kernel
theorem T104_eq : T 104 = T104 := by decide +kernel

/-- `∫_{R_k} (1−P₁)^b P₂^c` given the table `t = T_k`. -/
def intg (t : List ℕ) (k b c : ℕ) : ℚ :=
  ((b.factorial * c.factorial * t.getD c 0 : ℕ) : ℚ) / ((k + b + 2 * c).factorial : ℕ)

/-- the basis `(b, c)` and Maynard-shape coefficients (a 30-digit rationalisation, scaled to
integers). -/
def F : List ((ℕ × ℕ) × ℤ) := [((0, 0), -14878002984396692), ((1, 0), -7836470465341039227), ((2,
    0), -83191590589539858628), ((3, 0), -557595864405359624420), ((4, 0),
    247698404624286687576182), ((5, 0), -656208687025464663790564), ((6, 0),
    -32506765796610698506830669), ((7, 0), 87092022021195361254721786), ((8, 0),
    669911962280178102864986849), ((9, 0), 2979243862349426969865371336), ((10, 0),
    -37113907844597660013830031401), ((11, 0), 68382758943176493427081237545), ((0, 1),
    3575848798781651052), ((1, 1), 1818646594199977656941), ((2, 1), 25309585035831242483565), ((3,
    1), -326260449980699361826020), ((4, 1), -46886644023244947212659583), ((5, 1),
    222168752239340852575367506), ((6, 1), 4486007903416438248208387599), ((7, 1),
    -11072727273531990920338676142), ((8, 1), -143245936498333310711666492683), ((9, 1),
    437790096720371291394618568062), ((0, 2), -350617409652130875992), ((1, 2),
    -169786022275220327810145), ((2, 2), -2663018325220598137242589), ((3, 2),
    69019723294132629371785432), ((4, 2), 3026287114122381365708294310), ((5, 2),
    -20921852077635518531983461394), ((6, 2), -194723655742266098399474922772), ((7, 2),
    1000000000000000000000000000000), ((0, 3), 17745822909641608424767), ((1, 3),
    8053748584904113325896736), ((2, 3), 119477185803583266790467526), ((3, 3),
    -4351379042782870539937327779), ((4, 3), -68794316436546821078215302558), ((5, 3),
    700733964823007813658347496574), ((0, 4), -468732866626264235186592), ((1, 4),
    -196787216405219569561686214), ((2, 4), -1983261635198645172758377662), ((3, 4),
    92334598300765250552037563595), ((0, 5), 5199130177018003171634154), ((1, 5),
    2014328343490094750760940898)]

def Iform : ℚ :=
  (F.map fun p => (F.map fun p' =>
    ((p.2 * p'.2 : ℤ) : ℚ) * intg T105 105 (p.1.1 + p'.1.1) (p.1.2 + p'.1.2)).sum).sum

/-- the `t₁₀₅`-inner integral of `F`, collected over `(e, g)`, `e + 2g ≤ 12`. -/
def innerF : List ((ℕ × ℕ) × ℚ) :=
  ((List.range 7).flatMap fun gg => (List.range (13 - 2 * gg)).map fun e => (e, gg)).map fun eg =>
    (eg, (F.map fun p => ((List.range (p.1.2 + 1)).map fun j =>
      if p.1.1 + 2 * j + 1 = eg.1 ∧ p.1.2 - j = eg.2 then
        (p.2 : ℚ) * ((p.1.2.choose j * p.1.1.factorial * (2 * j).factorial : ℕ) : ℚ) /
          ((p.1.1 + 2 * j + 1).factorial : ℕ)
      else 0).sum).sum)

def Jform : ℚ :=
  (innerF.map fun p => (innerF.map fun p' =>
    p.2 * p'.2 * intg T104 104 (p.1.1 + p'.1.1) (p.1.2 + p'.1.2)).sum).sum

/-- **The numeric gate:** `M₁₀₅ ≥ 105·J/I > 4`. -/
theorem M105_gt_four : (4 : ℚ) < 105 * Jform / Iform := by decide +kernel

/-- an admissible 105-tuple of diameter 636 (greedy residue sieve, 2026-10-11). -/
def H : List ℕ := [0, 2, 6, 8, 12, 18, 26, 30, 32, 42, 48, 50, 56, 62, 72, 86, 96, 98, 102, 110,
    116, 120, 128, 132, 138, 140, 146, 158, 162, 168, 176, 180, 182, 186, 198, 200, 212, 216, 218,
    228, 230, 240, 242, 260, 266, 270, 272, 278, 282, 288, 296, 306, 308, 312, 320, 330, 336, 342,
    348, 350, 356, 362, 366, 372, 380, 386, 392, 396, 398, 408, 410, 422, 426, 432, 438, 440, 446,
    450, 452, 468, 470, 476, 480, 488, 498, 506, 512, 516, 518, 536, 540, 546, 548, 552, 572, 576,
    578, 582, 590, 600, 602, 608, 618, 630, 636]

theorem H_length : H.length = 105 := by decide +kernel
theorem H_diam : H.getLast? = some 636 ∧ H.head? = some 0 := by decide +kernel
/-- admissible: for every prime `p ≤ 105` some residue class mod `p` is missed. -/
theorem H_admissible : ∀ p ∈ (List.range 106).filter (fun p => decide (Nat.Prime p)),
    ∃ r ∈ List.range p, ∀ h ∈ H, h % p ≠ r := by decide +kernel

end Salt.MaynardK


