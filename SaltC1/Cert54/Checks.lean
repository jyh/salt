/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.Cert54.Data
import Mathlib.Data.Nat.Choose.Basic

/-!
# C1 — the `k = 54` certificate's check functions

Every function a kernel theorem of `SaltC1.Cert54.Tables` / `SaltC1.Cert54.Forms` reduces. Their
text is the interface the Lean side (the `MvPowerSeries` identities) is written against; each check
is a `Bool` the kernel evaluates by `decide +kernel`, never `native_decide`.

* `checkFact` — `factT` holds `n!` for `n ≤ 101`;
* `checkG` — `g_C · Π c_m! = (wt C)!`;
* `checkRecGen` — the Miller power recurrence at one key, the box `{0 ≠ A ≤ C}` and its
  coefficients generated here: `wt(C)·p_C = Σ_{0≠A≤C} (k·wt(A) − wt(C−A))·g_A·p_{C−A}`;
* `checkWI`, `checkWJ` — the closed forms of the two value tables;
* `checkWChain` / `checkWShards` — the collected marginal: every term valid (its digits bounded, so
  its `(a, c)` are its coefficient's), its value recomputed, the list strictly increasing in
  `(key, i, enc j)`, each key run's sum equal to `WBT`'s entry at the next position, the positions
  and keys threaded through the shards, the count exact;
* `Ihalf`, `Jhalf` — the symmetric half of the two quadratic forms, by rows.

Every definition that names an `addDecl`ed table is `noncomputable` (the compiler has no code for
the tables; the kernel reduces them regardless). Nothing here bears on twin primes.
-/

namespace SaltC1.Cert54

/-- `c − j`, componentwise. -/
def subL : List Nat → List Nat → List Nat
  | c :: cs, j :: js => (c - j) :: subL cs js
  | _, _ => []

/-- `j ≤ c`, componentwise, and the same length. -/
def leL : List Nat → List Nat → Bool
  | j :: js, c :: cs => Nat.ble j c && leL js cs
  | [], [] => true
  | _, _ => false

/-- Every component is `0`. -/
def allZero : List Nat → Bool
  | [] => true
  | c :: cs => Nat.beq c 0 && allZero cs

/-- The box `{A : A ≤ C}` (componentwise), the zero tuple included — a `List Nat` twin of
`tuplesLE`. -/
def boxL : List Nat → List (List Nat)
  | [] => [[]]
  | c :: cs => (List.range (c + 1)).flatMap fun a => (boxL cs).map fun as => a :: as

/-- The 13 exponents of a key, decoded base 64 (the `A` digit dropped). -/
def decodeC (key : Nat) : List Nat := (List.range 13).map fun m => (key / 64 ^ (m + 1)) % 64

/-- The keys of weight `≤ w` whose first exponent `c₁` lies in `[lo, hi)`, in `keysW`'s order: for
`hi ≤ w / 2 + 1` a contiguous block of `keysW 13 w` (`keysW_eq_keysRange`). The shard theorems
generate only their own block, never the list before it. -/
def keysRange (w lo hi : Nat) : List (List Nat) :=
  (List.range (hi - lo)).flatMap fun t => (keysW 12 (w - 2 * (lo + t))).map fun cs => (lo + t) :: cs

/-- `Π_m c_m!` from the factorial table. -/
noncomputable def facProd : List Nat → Int
  | [] => 1
  | c :: cs => factT.findB c * facProd cs

/-- `Π_m C(c_m, j_m)`. -/
noncomputable def chooseProd : List Nat → List Nat → Int
  | c :: cs, j :: js => (Nat.choose c j : Int) * chooseProd cs js
  | _, _ => 1

/-- `24!/n!` for `n ≤ 24`, from the factorial table. -/
noncomputable def f24q (n : Nat) : Int := Int.ofNat ((factT.findB 24).toNat / (factT.findB n).toNat)

/-- `f` on every element. -/
noncomputable def checkAllL {α : Type} (f : α → Bool) (es : List α) : Bool := es.all f

/-- `factT 0 = 1` and `factT (n+1) = (n+1)·factT n` for `n < 101`. -/
noncomputable def checkFact : Bool :=
  factT.findB 0 == 1 &&
    (List.range 101).all fun n => factT.findB (n + 1) == (n + 1 : Int) * factT.findB n

/-- `g_C · Π c_m! = (wt C)!`. -/
noncomputable def checkG (t : BST) (c : List Nat) : Bool :=
  t.findB (encKey 0 c) * facProd c == factT.findB (wt c)

/-- The Miller recurrence at the key `c`, the box generated:
`Σ_{0≠A≤C} (k·wt A − wt(C−A))·g_A·p_{C−A} = wt C · p_C`. -/
noncomputable def checkRecGen (p g : BST) (k : Nat) (c : List Nat) : Bool :=
  let s := (boxL c).foldl (fun acc a =>
    match allZero a with
    | true => acc
    | false =>
      let b := subL c a
      acc + (((k * wt a : Nat) : Int) - ((wt b : Nat) : Int)) * g.findB (encKey 0 a) *
        p.findB (encKey 0 b))
    (0 : Int)
  s == ((wt c : Nat) : Int) * p.findB (encKey 0 c)

/-- `WI(enc(A,C)) · (54+A+wt C)! = A! · Π c_m! · p54(C) · 100!`. -/
noncomputable def checkWI (t : BST) (e : FEntry) : Bool :=
  (t.findB (encKey e.1 e.2) * factT.findB (54 + e.1 + wt e.2))
    == (factT.findB e.1 * facProd e.2 * p54T.findB (encKey 0 e.2) * factT.findB 100)

/-- `WJ(enc(E,G)) · (53+E+wt G)! = E! · Π g_m! · p53(G) · 101!`. -/
noncomputable def checkWJ (t : BST) (e : FEntry) : Bool :=
  (t.findB (encKey e.1 e.2) * factT.findB (53 + e.1 + wt e.2))
    == (factT.findB e.1 * facProd e.2 * p53T.findB (encKey 0 e.2) * factT.findB 101)

/-- Every `(A, C)` with `A + wt C ≤ 46`: the keys of the `I` value table. -/
def wiEntries : List FEntry :=
  (keysW 13 46).flatMap fun c => (List.range (47 - wt c)).map fun a => (a, c)

/-- Every `(E, G)` with `E + wt G ≤ 48`: the keys of the `J` value table. -/
def wjEntries : List FEntry :=
  (keysW 13 48).flatMap fun c => (List.range (49 - wt c)).map fun a => (a, c)

/-- The entries of `wiEntries` whose key lies in `keysRange 46 lo hi`. -/
def wiEntriesR (lo hi : Nat) : List FEntry :=
  (keysRange 46 lo hi).flatMap fun c => (List.range (47 - wt c)).map fun a => (a, c)

/-- The entries of `wjEntries` whose key lies in `keysRange 48 lo hi`. -/
def wjEntriesR (lo hi : Nat) : List FEntry :=
  (keysRange 48 lo hi).flatMap fun c => (List.range (49 - wt c)).map fun a => (a, c)

/-- One marginal term's `(key, value, k_i = enc(a, c))`. The third component ties the term's
`(a, c)` to `coefBT`'s entry `i` by an `encKey` equality, which pins the digits only because
`validT` bounds them (`a < 64`, every `c_m < 64`, 13 of them): on bounded digits `encKey` is
injective, and without the bounds it is not (`encKey 3 [2, 0, …] = encKey 67 [1, 0, …]`; FX1 of
math's read, 2026-10-15 — the decoding tie `decodeC kc.1` was measured at 4.1–4.3 GB per marginal
link, over the per-theorem cap, so the bound lives in `validT` and this text is the freeze's). -/
noncomputable def termKV (t : WTerm) : Nat × Int × Bool :=
  let e := wt t.2.2.2
  let kc := coefBT.getB t.1
  (encKey (t.2.1 + e + 1) (subL t.2.2.1 t.2.2.2),
   kc.2 * factT.findB t.2.1 * factT.findB e * f24q (t.2.1 + e + 1) * chooseProd t.2.2.1 t.2.2.2,
   Nat.beq kc.1 (encKey t.2.1 t.2.2.1))

/-- Every component is `< 64`: a base-64 digit. -/
def allLt64 : List Nat → Bool
  | [] => true
  | c :: cs => Nat.blt c 64 && allLt64 cs

/-- A term is valid: `i < 1236`, both lists of length 13, `j ≤ c` componentwise, and the digits
bounded — `a < 64` and every `c_m < 64` (so `j_m < 64` too) — which is what makes `termKV`'s
`encKey` tie injective (FX1). -/
def validT (t : WTerm) : Bool :=
  Nat.blt t.1 1236 && Nat.beq t.2.2.1.length 13 && Nat.beq t.2.2.2.length 13 &&
    leL t.2.2.2 t.2.2.1 && Nat.blt t.2.1 64 && allLt64 t.2.2.1

/-- The fold's state: `(pos, key, sum, ok, prevI, prevEj, count)`. -/
abbrev WState := Nat × Nat × Int × Bool × Nat × Nat × Nat

/-- One term: in the same key run, strictly increasing in `(i, enc j)`; a new key strictly greater,
closing the previous run against `WBT` at `pos`. -/
noncomputable def wStep (st : WState) (t : WTerm) : WState :=
  let (pos, key, sum, ok, pi, pj, cnt) := st
  let kv := termKV t
  let i := t.1
  let ej := encKey 0 t.2.2.2
  let okV := kv.2.2 && validT t
  match Nat.beq kv.1 key with
  | true =>
    (pos, key, sum + kv.2.1, ok && okV && (Nat.blt pi i || (Nat.beq pi i && Nat.blt pj ej)), i, ej,
      cnt + 1)
  | false =>
    let w := WBT.getB pos
    (pos + 1, kv.1, kv.2.1, ok && okV && Nat.blt key kv.1 && Nat.beq w.1 key && (w.2 == sum), i, ej,
      cnt + 1)

/-- One shard from position `pos0` after `prevKey` ↦
`(ok, last key, runs consumed, terms counted)`. -/
noncomputable def checkWFrom (terms : List WTerm) (pos0 prevKey : Nat) : Bool × Nat × Nat × Nat :=
  match terms with
  | [] => (true, prevKey, 0, 0)
  | t :: ts =>
    let kv := termKV t
    let st := ts.foldl wStep
      (pos0, kv.1, kv.2.1, kv.2.2 && validT t && Nat.blt prevKey kv.1, t.1, encKey 0 t.2.2.2, 1)
    let (pos, key, sum, ok, _, _, cnt) := st
    let w := WBT.getB pos
    (ok && Nat.beq w.1 key && (w.2 == sum), key, pos + 1 - pos0, cnt)

/-- `Σ_i Π_m (c_{i,m} + 1)` from `coefBT`'s own keys: the number of marginal terms. -/
noncomputable def expectedLen : Nat :=
  (List.range nB).foldl
    (fun acc i => acc + (decodeC (coefBT.getB i).1).foldl (fun p c => p * (c + 1)) 1) 0

/-- One shard of the marginal, the state `(pos, prevKey, count, ok)` threaded through. -/
noncomputable def wShardStep (st : Nat × Nat × Nat × Bool) (s : List WTerm) :
    Nat × Nat × Nat × Bool :=
  let (pos, pk, cnt, ok) := st
  let (okS, lastKey, ng, c) := checkWFrom s pos pk
  (pos + ng, lastKey, cnt + c, ok && okS)

/-- Every shard in turn, positions and keys threaded through (no shard metadata is data); then all
of `WBT` consumed and the count exact. -/
noncomputable def checkWShards (sh : List (List WTerm)) : Bool :=
  let r := sh.foldl wShardStep (0, 0, 0, true)
  r.2.2.2 && Nat.beq r.1 nW && Nat.beq r.2.2.1 expectedLen

/-- One link of the chained marginal check: the shards from `(pos0, pk0)` ↦
`(ok, pos, lastKey, count)`, the state the next link starts from. -/
noncomputable def checkWChain (sh : List (List WTerm)) (pos0 pk0 : Nat) : Bool × Nat × Nat × Nat :=
  let r := sh.foldl wShardStep (pos0, pk0, 0, true)
  (r.2.2.2, r.1, r.2.1, r.2.2.1)

/-- The marginal's terms, all eleven shards. -/
noncomputable def wshards : List (List WTerm) := wsh0 ++ wsh1 ++ wsh2

/-- The rows `[i0, i1)` of the `I` form's symmetric half:
`Σ_i (c_i·c_i·WI(2 k_i) + 2·Σ_{j > i} c_i·c_j·WI(k_i + k_j))`. -/
noncomputable def Ihalf (i0 i1 : Nat) : Int :=
  (List.range (i1 - i0)).foldl (fun acc ii =>
    let i := i0 + ii
    let (ki, ci) := coefBT.getB i
    acc + ci * ci * WItree.findB (2 * ki) + 2 * (List.range (nB - i - 1)).foldl (fun acc2 jj =>
      let (kj, cj) := coefBT.getB (i + 1 + jj)
      acc2 + ci * cj * WItree.findB (ki + kj)) 0) 0

/-- The rows `[x0, x1)` of the `J` form's symmetric half over the marginal `WBT`. -/
noncomputable def Jhalf (x0 x1 : Nat) : Int :=
  (List.range (x1 - x0)).foldl (fun acc xx =>
    let x := x0 + xx
    let (kx, wx) := WBT.getB x
    acc + wx * wx * WJtree.findB (2 * kx) + 2 * (List.range (nW - x - 1)).foldl (fun acc2 yy =>
      let (ky, wy) := WBT.getB (x + 1 + yy)
      acc2 + wx * wy * WJtree.findB (kx + ky)) 0) 0

end SaltC1.Cert54
