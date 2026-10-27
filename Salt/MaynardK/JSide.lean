/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Cert105

/-!
# C1 — the certificate's `Jform`, re-grouped as a flat double sum (by kernel)

`Jform` (`Cert105`) collects the `t₁₀₅`-inner integral of `F` over the grid `(E, G)`,
`E + 2G ≤ 12`. `FJ` lists the same inner integral UNcollected: one entry per basis term `(b, c)` of
`F` and per `j ≤ c`, at `(b + 2j + 1, c − j)` with weight `a · C(c, j) · b!(2j)!/(b+2j+1)!`.
`Jform_eq_J2` says the two groupings give the same number, by kernel reduction.
-/

namespace Salt.MaynardK

/-- the uncollected inner integral of `F`. -/
def FJ : List ((ℕ × ℕ) × ℚ) :=
  F.flatMap fun p => (List.range (p.1.2 + 1)).map fun j =>
    ((p.1.1 + 2 * j + 1, p.1.2 - j),
      (p.2 : ℚ) * ((p.1.2.choose j * p.1.1.factorial * (2 * j).factorial : ℕ) : ℚ) /
        ((p.1.1 + 2 * j + 1).factorial : ℕ))

/-- `J` as a flat double sum over `FJ`. -/
def J2 : ℚ :=
  (FJ.map fun u => (FJ.map fun v =>
    u.2 * v.2 * intg T104 104 (u.1.1 + v.1.1) (u.1.2 + v.1.2)).sum).sum

/-- The certificate's `Jform` and its uncollected regrouping `J2` are the same rational, by kernel
reduction.
-/
theorem Jform_eq_J2 : Jform = J2 := by decide +kernel

end Salt.MaynardK
