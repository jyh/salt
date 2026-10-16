/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Lean
import SaltC1.Cert54.Sha256

/-!
# C1 — the `k = 54` certificate's data

The tables of the `k = 54`, `d = 23` certificate (arXiv:1407.4897v4 Thm 3.9(vii)), as kernel terms.
Every table here is DATA: nothing in this file asserts anything about it. The kernel theorems of
`SaltC1.Cert54.Tables` and `SaltC1.Cert54.Forms` certify each one, link by link.

The text files under `SaltC1/Cert54/data/` (written by `scripts/c1/emit_cert54.py`) are read by the
command `cert54_data`, which builds each table as a constructor term and adds it with `addDecl`: one
syntax node per table, so the build has no per-numeral information to walk. `Int` values are the
constructor forms `Int.ofNat n` / `Int.negSucc n` over raw `Nat` literals.

Every file is PINNED: `cert54Pins` names each file's SHA-256 (as `shasum -a 256` prints it), every
reader checks the file it reads through `readPinned`, and `cert54_data` first runs `checkCert54Pins`
— every pinned file present and matching, and no unpinned file in the directory. Lake does not track
a file read by `IO.FS.readFile`, so without the pins a changed table could be replayed from a stale
build; with them, a data change that is not re-pinned is refused at elaboration.

* read: `coefBT` (the coefficients `enc(a, C) ↦ c`, basis order, in the bit-reversal layout of
  `BT.getB`), `WBT` (the 24!-scaled marginal, key order), `p54T`, `p53T` (the coefficients of
  `GM 13 ^ 54` and `GM 13 ^ 53`), `wsh0`, `wsh1`, `wsh2` (the marginal's terms, four shards each);
* derived here by `Nat` arithmetic: `factT` (`n!`, `n ≤ 101`), `gT46`, `gT48` (`wt C! / Π c_m!`),
  and the value tables `WItree`, `WJtree` from `factT`, `p54T`, `p53T`.

Keys are `encKey A C = A + Σ_m c_m · 64^m`; `wt C = Σ_m 2m · c_m`. Nothing here bears on twin primes.
-/

set_option maxRecDepth 100000

namespace SaltC1.Cert54

/-- A key-sorted binary search tree `Nat ↦ Int`. -/
inductive BST
  | leaf
  | node (l : BST) (k : Nat) (v : Int) (r : BST)

/-- Lookup by descent on the kernel's `Bool` primitives; `0` off the tree. -/
def BST.findB : BST → Nat → Int
  | .leaf, _ => 0
  | .node l k v r, x =>
    match Nat.blt x k with
    | true => BST.findB l x
    | false =>
      match Nat.beq x k with
      | true => v
      | false => BST.findB r x

/-- A complete binary tree of `(key, value)` leaves, indexed in the bit-reversal layout. -/
inductive BT
  | leaf (k : Nat) (v : Int)
  | node (l r : BT)

/-- The `i`-th leaf: the low bit of `i` picks the side. -/
def BT.getB : BT → Nat → Nat × Int
  | .leaf k v, _ => (k, v)
  | .node l r, i =>
    match Nat.beq (Nat.land i 1) 0 with
    | true => BT.getB l (i / 2)
    | false => BT.getB r (i / 2)

/-- A coefficient-identity entry `(A, [c₁, …, c₁₃])`. -/
abbrev FEntry := Nat × List Nat
/-- A marginal term `(i, a, [c₁, …, c₁₃], [j₁, …, j₁₃])`. -/
abbrev WTerm := Nat × Nat × List Nat × List Nat

/-- `Σ_m c_m · p · 64^m` over the list. -/
def encAux : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, p => c * p + encAux cs (p * 64)

/-- `encKey A C = A + Σ_m c_m · 64^m` (`m = 1..13`). -/
def encKey (a : Nat) (c : List Nat) : Nat := a + encAux c 64

/-- `Σ_m m' · c_m` with the multiplier stepping by 2. -/
def wtAux : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, m => m * c + wtAux cs (m + 2)

/-- `wt C = Σ_m 2m · c_m`. -/
def wt (c : List Nat) : Nat := wtAux c 2

/-- The exponent lists of weight `≤ rem` on the last `m` of the 13 variables, by structural
recursion on `m`: the first element is `c_{14-m}`, of weight `2(14-m)`; `keysW 13 w` lists
`c₁, …, c₁₃` with `c₁` outermost. -/
def keysW : (m : Nat) → (rem : Nat) → List (List Nat)
  | 0, _ => [[]]
  | m + 1, rem =>
    (List.range (rem / (2 * (13 - m)) + 1)).flatMap fun c =>
      (keysW m (rem - 2 * (13 - m) * c)).map fun cs => c :: cs

/-- The number of basis functions. -/
def nB : Nat := 1236
/-- The number of keys of the collected marginal. -/
def nW : Nat := 1236

open Lean Elab Command Meta

/-- An `Int` as the constructor form the kernel matches on, over a raw `Nat` literal. -/
def intExpr (v : Int) : Expr :=
  if v ≥ 0 then mkApp (mkConst ``Int.ofNat) (mkRawNatLit v.toNat)
  else mkApp (mkConst ``Int.negSucc) (mkRawNatLit (-v - 1).toNat)

/-- The balanced `BST` over the key-sorted slice `a[lo:hi)`. -/
partial def bstExpr (a : Array (Nat × Int)) (lo hi : Nat) : Expr :=
  if lo ≥ hi then mkConst ``BST.leaf
  else
    let m := (lo + hi) / 2
    let (k, v) := a[m]!
    mkApp4 (mkConst ``BST.node) (bstExpr a lo m) (mkRawNatLit k) (intExpr v) (bstExpr a (m + 1) hi)

/-- The `BT` of depth `d` in the layout `BT.getB` reads; leaves past the end are `(0, 0)`. -/
partial def btExpr (a : Array (Nat × Int)) (d off stride : Nat) : Expr :=
  if d = 0 then
    let (k, v) := if h : off < a.size then a[off] else (0, 0)
    mkApp2 (mkConst ``BT.leaf) (mkRawNatLit k) (intExpr v)
  else
    mkApp2 (mkConst ``BT.node) (btExpr a (d - 1) off (2 * stride))
      (btExpr a (d - 1) (off + stride) (2 * stride))

/-- `Nat`. -/
def natTy : Expr := mkConst ``Nat
/-- `List Nat`. -/
def natListTy : Expr := mkApp (mkConst ``List [Level.zero]) natTy
/-- `α × β`. -/
def prodTy (a b : Expr) : Expr := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b
/-- `(x, y) : α × β`. -/
def pairE (a b x y : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) a b x y
/-- A list literal. -/
def listOfE (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)
/-- `WTerm` as an expression. -/
def wtermTy : Expr := prodTy natTy (prodTy natTy (prodTy natListTy natListTy))
/-- A `WTerm` literal. -/
def wtermExpr (i a : Nat) (c j : List Nat) : Expr :=
  pairE natTy (prodTy natTy (prodTy natListTy natListTy)) (mkRawNatLit i)
    (pairE natTy (prodTy natListTy natListTy) (mkRawNatLit a)
      (pairE natListTy natListTy (listOfE natTy (c.map mkRawNatLit)) (listOfE natTy (j.map mkRawNatLit))))

/-- `n!` in the elaborator. -/
def factN (n : Nat) : Nat := (List.range n).foldl (fun p i => p * (i + 1)) 1

/-- A data file's sections `## name count`, each a list of lines of integers; `#` lines are
comments. The count on the header is checked against the lines read. -/
def parseSections (txt : String) : Except String (Array (String × Array (List Int))) := do
  let mut out : Array (String × Nat × Array (List Int)) := #[]
  for line in txt.splitOn "\n" do
    if line.startsWith "## " then
      let ws := line.splitOn " "
      out := out.push (ws[1]!, (ws[2]!).toNat!, #[])
    else if line.startsWith "#" || line.isEmpty then
      pure ()
    else
      let vs := (line.splitOn " ").map String.toInt!
      match out.back? with
      | some (nm, n, acc) => out := out.pop.push (nm, n, acc.push vs)
      | none => throw "a data line before any section"
  for (nm, n, acc) in out do
    unless acc.size == n do throw s!"section {nm}: {acc.size} lines, header says {n}"
  return out.map fun (nm, _, acc) => (nm, acc)

/-- The SHA-256 of every file under `SaltC1/Cert54/data/`, as `shasum -a 256` prints it: the five
files `scripts/c1/emit_cert54.py` writes, and `vector-k54-eps0-d23.txt`, its input, whose digest
each emitted file's header line 3 repeats. Derived from the files (`scripts/c1/pin_cert54_data.py`
prints this table from them and `--check` compares it), never typed. -/
def cert54Pins : List (String × String) := [
  ("W.txt", "691a8389d865b19f2d266a1d326e97651a7cc534c083276ef29695e987c5ff14"),
  ("coef.txt", "688677e411ea0e33557333446453228acf3c5fe97b62cbe69a77b84f06c28eca"),
  ("p53.txt", "a614369a3c9aea918ae10b36c06821d9e894aa6b48079c75fec081ba6b615b1c"),
  ("p54.txt", "0f515661b5db73cd7acdbaf678b380a5e474d80a93622ae693c43b7a2f4a35c0"),
  ("vector-k54-eps0-d23.txt", "c93e4811c96548f613857f0100bc0506c4ea3baf003f09af88aa8b21bf722ee6"),
  ("wterms.txt", "fd23868410dd944fe4ff77461934550392fb7c8f0fc31699677c92f6b06843f6")]

/-- Read `dir/f` as text, after refusing it unless its SHA-256 is the one `cert54Pins` names. -/
def readPinned (dir f : String) : CommandElabM String := do
  let some pin := List.lookup f cert54Pins
    | throwError "{f}: no SHA-256 pin in cert54Pins (pin it with scripts/c1/pin_cert54_data.py)"
  let bytes ← IO.FS.readBinFile (dir ++ "/" ++ f)
  let got := Sha256.hex bytes
  unless got == pin do
    throwError "{f}: SHA-256 {got} is not the pinned {pin}: this is not the file the certificate \
      was emitted from (re-emit with scripts/c1/emit_cert54.py, then re-pin cert54Pins)"
  match String.fromUTF8? bytes with
  | some s => pure s
  | none => throwError "{f}: not UTF-8"

/-- Every pinned file present under `dir` and matching its pin, and no other file there (entries
whose name starts with `.` are ignored). -/
def checkCert54Pins (dir : String) : CommandElabM Unit := do
  for (f, _) in cert54Pins do
    let _ ← readPinned dir f
  let entries ← System.FilePath.readDir dir
  for e in entries do
    unless e.fileName.startsWith "." || (List.lookup e.fileName cert54Pins).isSome do
      throwError "{dir}/{e.fileName}: a data file with no SHA-256 pin in cert54Pins"
  logInfo m!"cert54 pins: {cert54Pins.length} files match cert54Pins, nothing unpinned in {dir}"

/-- Add a definition with a given value; the kernel checks its type. -/
def addData (n : Name) (ty val : Expr) : CommandElabM Unit :=
  liftCoreM <| addDecl (.defnDecl { name := n, levelParams := [], type := ty, value := val,
                                     hints := .regular 1, safety := .safe })

/-- Read the data directory and add every table. -/
elab "cert54_data " dir:str : command => do
  checkCert54Pins dir.getString
  let rd (f : String) : CommandElabM (Array (String × Array (List Int))) := do
    let txt ← readPinned dir.getString f
    match parseSections txt with
    | .ok s => pure s
    | .error e => throwError "{f}: {e}"
  let one (f nm : String) (n : Nat) : CommandElabM (Array (Nat × Int)) := do
    let secs ← rd f
    match secs.find? (·.1 == nm) with
    | some (_, a) =>
      unless a.size == n && a.all (·.length == 2) do throwError "{f}: section {nm} is not {n} pairs"
      pure (a.map fun l => (l[0]!.toNat, l[1]!))
    | none => throwError "{f}: section {nm} missing"
  let nm (s : String) : Name := Name.mkStr `SaltC1.Cert54 s
  -- the read tables
  let coef ← one "coef.txt" "coef" 1236
  let W ← one "W.txt" "W" 1236
  let p54 ← one "p54.txt" "p54" 5479
  let p53 ← one "p53.txt" "p53" 6915
  addData (nm "coefBT") (mkConst ``BT) (btExpr coef 11 0 1)
  addData (nm "WBT") (mkConst ``BT) (btExpr W 11 0 1)
  addData (nm "p54T") (mkConst ``BST) (bstExpr p54 0 p54.size)
  addData (nm "p53T") (mkConst ``BST) (bstExpr p53 0 p53.size)
  -- the derived tables
  let fact : Array Nat := (List.range 102).toArray.map factN
  addData (nm "factT") (mkConst ``BST)
    (bstExpr ((List.range 102).toArray.map fun n => (n, (fact[n]! : Int))) 0 102)
  let gTab (w : Nat) : Array (Nat × Int) :=
    (((keysW 13 w).map fun c => (encKey 0 c, ((fact[wt c]! / (c.map (fact[·]!)).foldl (· * ·) 1 : Nat) : Int)))
      |>.toArray.qsort (·.1 < ·.1))
  let g46 := gTab 46
  let g48 := gTab 48
  unless g46.size == 5479 && g48.size == 6915 do throwError "g: {g46.size} {g48.size}"
  addData (nm "gT46") (mkConst ``BST) (bstExpr g46 0 g46.size)
  addData (nm "gT48") (mkConst ``BST) (bstExpr g48 0 g48.size)
  let pm (a : Array (Nat × Int)) : Std.HashMap Nat Int := a.foldl (fun m (k, v) => m.insert k v) {}
  let p54m := pm p54
  let p53m := pm p53
  let wTab (k w F : Nat) (pmap : Std.HashMap Nat Int) : Array (Nat × Int) :=
    ((keysW 13 w).flatMap fun c => (List.range (w + 1 - wt c)).map fun a =>
      let num : Int := (fact[a]! * (c.map (fact[·]!)).foldl (· * ·) 1 * fact[F]! : Nat) * pmap.getD (encKey 0 c) 0
      (encKey a c, num / (fact[k + a + wt c]! : Int))) |>.toArray.qsort (·.1 < ·.1)
  let WI := wTab 54 46 100 p54m
  let WJ := wTab 53 48 101 p53m
  unless WI.size == 42511 && WJ.size == 54905 do throwError "WI/WJ: {WI.size} {WJ.size}"
  addData (nm "WItree") (mkConst ``BST) (bstExpr WI 0 WI.size)
  addData (nm "WJtree") (mkConst ``BST) (bstExpr WJ 0 WJ.size)
  -- the marginal's terms: the shards in file order, four to a chain link
  let secs ← rd "wterms.txt"
  let shardE (a : Array (List Int)) : CommandElabM Expr := do
    unless a.all (·.length == 28) do throwError "wterms.txt: a line is not (i, a, c₁..c₁₃, j₁..j₁₃)"
    let ls := a.toList.map (·.map Int.toNat)
    pure (listOfE wtermTy (ls.map fun l => wtermExpr l[0]! l[1]! ((l.drop 2).take 13) (l.drop 15)))
  let shards ← secs.mapM fun (_, a) => shardE a
  unless shards.size == 11 do throwError "wterms.txt: {shards.size} shards, expected 11"
  let shTy := mkApp (mkConst ``List [Level.zero]) wtermTy
  for g in [0, 1, 2] do
    addData (nm s!"wsh{g}") (mkApp (mkConst ``List [Level.zero]) shTy)
      (listOfE shTy ((shards.extract (4 * g) (4 * g + 4)).toList))
  logInfo m!"cert54_data: coefBT {coef.size} · WBT {W.size} · p54T {p54.size} · p53T {p53.size} · \
    factT 102 · gT46 {g46.size} · gT48 {g48.size} · WItree {WI.size} · WJtree {WJ.size} · \
    wsh0..2 ({shards.size} shards)"

cert54_data "SaltC1/Cert54/data"

end SaltC1.Cert54
