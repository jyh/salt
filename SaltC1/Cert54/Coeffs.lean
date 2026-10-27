/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.Cert54.Checks

/-!
# C1 — the `k = 54` certificate's coefficient list

`cs54L` is the vector of the certificate at the common integer scale, one basis function
`(1 − P₁)^a · Π_m P_{2m}^{c_m}` per entry as `(a, [c₁, …, c₁₃], coefficient)`, in the basis order
(`c` over `keysW 13 23`, then `a = 0 … 23 − wt c`). It is read from `data/coef.txt` (one
`enc(a, C) coefficient` line per entry; the vector's sha256 in its header is
`c93e4811c96548f613857f0100bc0506c4ea3baf003f09af88aa8b21bf722ee6`)
by `cert54_coeffs`, which decodes each key into `(a, C)` and adds the list with `addDecl` (a source
literal of this size exhausts the elaborator). `cs54` is the same list in the type of the Lean side,
`List ((ℕ × (Fin 13 → ℕ)) × ℤ)`; `coef_keys_ok` certifies, by `decide +kernel`, that
`coefBT.getB i` is the `i`-th entry's key and coefficient, and `coef_basis_ok` that every entry is a
basis function (`a + wt C ≤ 23`, 13 exponents) — so every digit is `< 64`, the keys decode, and the
`I` form's lookups at `k_i + k_j` lie in `wi_ok`'s range (FX2 of math's read, 2026-10-15). Nothing
here bears on twin primes.
-/

namespace SaltC1.Cert54

open Lean Elab Command Meta in
/-- Read `coef.txt` and add `cs54L : List (Nat × List Nat × Int)`. -/
elab "cert54_coeffs " dir:str : command => do
  let txt ← readPinned dir.getString "coef.txt"
  let secs ← match parseSections txt with
    | .ok s => pure s
    | .error e => throwError "coef.txt: {e}"
  let some (_, a) := secs.find? (·.1 == "coef") | throwError "coef.txt: section coef missing"
  unless a.size == 1236 && a.all (·.length == 2) do throwError "coef.txt: not 1236 pairs"
  let eTy := prodTy natTy (prodTy natListTy (mkConst ``Int))
  let es := a.toList.map fun l =>
    let key := l[0]!.toNat
    let c := (List.range 13).map fun m => (key / 64 ^ (m + 1)) % 64
    pairE natTy (prodTy natListTy (mkConst ``Int)) (mkRawNatLit (key % 64))
      (pairE natListTy (mkConst ``Int) (listOfE natTy (c.map mkRawNatLit)) (intExpr l[1]!))
  addData `SaltC1.Cert54.cs54L (mkApp (mkConst ``List [Level.zero]) eTy) (listOfE eTy es)

cert54_coeffs "SaltC1/Cert54/data"

/-- The coefficient list in the type of the Lean side. -/
noncomputable def cs54 : List ((ℕ × (Fin 13 → ℕ)) × ℤ) :=
  cs54L.map fun e => ((e.1, fun m => e.2.1.getD m 0), e.2.2)

/-- `l` has `nB` entries and its `i`-th entry's key and coefficient are `coefBT.getB i`. -/
noncomputable def checkCoefKeys (l : List (Nat × List Nat × Int)) : Bool :=
  Nat.beq l.length nB && ((List.range nB).zip l).all fun (i, e) =>
    let kv := coefBT.getB i
    Nat.beq kv.1 (encKey e.1 e.2.1) && kv.2 == e.2.2

theorem coef_keys_ok : checkCoefKeys cs54L = true := by decide +kernel

/-- Every entry is a basis function of the certificate: `a + wt C ≤ 23` and 13 exponents (so each
`c_m ≤ 11`, every digit of `encKey a C` is `< 64`, and the key decodes to `(a, C)`). -/
def checkCoefBasis (l : List (Nat × List Nat × Int)) : Bool :=
  l.all fun e => Nat.ble (e.1 + wt e.2.1) 23 && Nat.beq e.2.1.length 13

theorem coef_basis_ok : checkCoefBasis cs54L = true := by decide +kernel

end SaltC1.Cert54
