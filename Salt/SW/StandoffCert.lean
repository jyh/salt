/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.StandoffGate
import Salt.SW.SiegelClose
import Salt.SW.SiegelFinal
import Salt.SW.DHCore

/-!
# The constant-closure CERTIFICATE for `Salt.SW.StandoffGate` — a check that can FAIL

`Salt.BV.SiegelWalfisz` is one Prop and `#print axioms` is the same three lines whichever
proof is behind it, so "Siegel-free" is not visible to either. It is a property of the PROOF
TERM: the transitive constant closure of `siegelWalfisz_of_standoff` must exclude
`siegel_theorem` (`SiegelClose.lean`), `siegel_L_one_exceptional` (`SiegelFinal.lean`) and
`L1_lower_siegel` (`DHCore.lean`). This module ASSERTS that, and it asserts the positive
controls first, so a green here means the instrument saw the reach it was built to see.

## The instrument

The shape of the kernel's own reach relation, as the non-author reader (h2c) drove it for
GOLDMINE kill-check 1 (`ScratchKC1.lean`, 2026-09-24): `Lean.CollectAxioms.collect`
(toolchain v4.32.0-rc1) with a parent map — for every constant, `Expr.getUsedConstants` of
its TYPE and its VALUE, transitively, over the imported environment; a REACH prints its
path. `#print axioms` walks the same edges, which is why it sees a `sorryAx` buried in a
proof and why this walk sees a `siegel_theorem` buried in one.

## Commands (each logs an ERROR on failure, so the module — and any build of it — goes red)

* `#assert_targets_exist` — every target NAME is in this environment (T control; a missing
  import would make every NOT-REACHED below vacuous).
* `#assert_reaches root target` — the positive control: the walk from `root` FINDS `target`
  (else error). Used on `psi1AP_main_bound` (direct, `Fold.lean:167`) and on
  `siegelWalfisz_holds` (proof-only: its statement never names Siegel).
* `#assert_not_reaches root target` — the certificate: the walk from `root` must NOT find
  `target`; a reach prints its path and errors.
* `#assert_conclusion_is new n old` — strip `n` leading binders from the TYPE of `new` and
  compare the remainder, as an `Expr`, with the TYPE of `old` (syntactic `==`, never defeq):
  the wave changes no landed statement.
* `#closure_report root` — the per-root census (closure size, Salt modules, the Siegel/DHCore/
  Page-named modules touched, whether `sorryAx` is in the closure). Report only.

## Declared limits, beside the verdicts

* The walk is over the elaboration environment's `find?` — the same constants the kernel
  holds for imported names. It does not see `native_decide`-style reflection (none here; the
  axiom audit is the separate `#print axioms` pair in `salt/CLAUDE.md`).
* "Reaches" is transitive constant reference, the relation `#print axioms` uses.
* ⚠️ **At the statement freeze every proof in `StandoffGate` is `sorry`.** The NOT-REACHED
  verdicts on the frozen names are then the VACUOUS half: the closure is the statement's plus
  `sorryAx`, and `#closure_report` says so in its `sorryAx` field. The certificate is armed
  for the wave; it is EVIDENCE only when `sorryAx: false` prints beside a NOT-REACHED.
* `not_fulcrum_siegelFree_SW` is REPORTED and not asserted: its `¬F` horn runs through the
  fulcrum gadget, whose closure is the fulcrum campaign's business, and the label already
  says its `c` is nonconstructive.

Red-first: the same commands, pointed the wrong way (`#assert_not_reaches siegelWalfisz_holds
siegel_theorem`; `#assert_conclusion_is psi1AP_main_bound_of_standoff 3 siegelWalfisz_holds`),
must go red at the predicted line — driven in an UNCOMMITTED scratch whose log is kept with
the freeze's receipts.
-/

open Lean Elab Command Meta

namespace Salt.SW.StandoffCert

structure St where
  visited : NameSet := {}
  parent  : NameMap Name := {}
  count   : Nat := 0
  saltN   : Nat := 0

abbrev M := ReaderT Environment (StateM St)

/-- The toolchain's `CollectAxioms.collect`, with a parent map instead of an axiom list. -/
partial def walk (c : Name) (from? : Option Name) : M Unit := do
  let s ← get
  if s.visited.contains c then return
  modify fun s => { s with
    visited := s.visited.insert c
    count := s.count + 1
    saltN := if (`Salt).isPrefixOf c then s.saltN + 1 else s.saltN
    parent := match from? with | some p => s.parent.insert c p | none => s.parent }
  let env ← read
  let go (e : Expr) : M Unit := e.getUsedConstants.forM fun d => walk d (some c)
  match env.find? c with
  | some (.axiomInfo v)  => go v.type
  | some (.defnInfo v)   => go v.type *> go v.value
  | some (.thmInfo v)    => go v.type *> go v.value
  | some (.opaqueInfo v) => go v.type *> go v.value
  | some (.quotInfo _)   => pure ()
  | some (.ctorInfo v)   => go v.type
  | some (.recInfo v)    => go v.type
  | some (.inductInfo v) => go v.type *> v.ctors.forM fun d => walk d (some c)
  | none                 => pure ()

/-- Path from `root` to `t` by parent pointers (root first). -/
partial def pathTo (s : St) (root t : Name) (acc : List Name := []) (fuel : Nat := 100000) :
    List Name :=
  if fuel = 0 then t :: acc else
  if t == root then t :: acc else
  match s.parent.find? t with
  | some p => pathTo s root p (t :: acc) (fuel - 1)
  | none   => t :: acc

/-- Plain joined names: one deterministic line, no width-driven wrapping. -/
def render (ns : List Name) : String := ", ".intercalate (ns.map toString)

def hasSub (m : Name) (sub : String) : Bool := ((toString m).splitOn sub).length > 1

/-- The three Siegel-zero-theory names the certificate excludes. -/
def targets : List Name :=
  [``Salt.SW.siegel_theorem, ``Salt.SW.siegel_L_one_exceptional, ``Salt.SW.L1_lower_siegel]

def closureOf (root : Name) : CommandElabM St := do
  let env ← getEnv
  let ((), s) := ((walk root none).run env).run {}
  return s

def resolve (id : Ident) : CommandElabM Name := do
  let cs ← liftCoreM <| realizeGlobalConstWithInfos id
  match cs with
  | [c] => pure c
  | _ => throwError "StandoffCert: {id} does not resolve to exactly one constant"

elab "#assert_targets_exist" : command => do
  let env ← getEnv
  for t in targets do
    match env.find? t with
    | some _ => logInfo m!"CERT T  target present: {t}"
    | none   => logError m!"CERT T  INVALID — target ABSENT from this environment: {t}"

elab "#assert_reaches " r:ident t:ident : command => do
  let root ← resolve r
  let tgt ← resolve t
  let s ← closureOf root
  if s.visited.contains tgt then
    let p := pathTo s root tgt
    logInfo m!"CERT P+ {root} REACHES {tgt} — path ({p.length} nodes): {render p}"
  else
    logError (m!"CERT P+ FAILED: {root} does NOT reach {tgt} (closure {s.count})"
      ++ m!" — the positive control did not fire")

elab "#assert_not_reaches " r:ident t:ident : command => do
  let root ← resolve r
  let tgt ← resolve t
  let s ← closureOf root
  if s.visited.contains tgt then
    let p := pathTo s root tgt
    logError m!"CERT FAILED: {root} REACHES {tgt} — path ({p.length} nodes): {render p}"
  else
    let sorried := s.visited.contains ``sorryAx
    let tail : MessageData := if sorried then m!" — VACUOUS: a sorried proof" else m!""
    logInfo (m!"CERT OK: {root} does NOT reach {tgt} (closure {s.count}, {s.saltN} under Salt, "
      ++ m!"sorryAx: {sorried})" ++ tail)

/-- Strip `n` leading binders from `new`'s type; the remainder must be `old`'s type,
syntactically. -/
elab "#assert_conclusion_is " n:ident k:num o:ident : command => do
  let newN ← resolve n
  let oldN ← resolve o
  let env ← getEnv
  let some ni := env.find? newN | throwError "no {newN}"
  let some oi := env.find? oldN | throwError "no {oldN}"
  let ok ← liftTermElabM <| forallBoundedTelescope ni.type (some k.getNat) fun xs body => do
    if xs.size != k.getNat then return false
    return body == oi.type
  if ok then
    logInfo m!"CERT CONCLUSION OK: type({newN}) minus {k.getNat} binders == type({oldN}), as Exprs"
  else
    logError (m!"CERT CONCLUSION FAILED: type({newN}) minus {k.getNat} binders"
      ++ m!" ≠ type({oldN}) (syntactic)")

elab "#closure_report " r:ident : command => do
  let root ← resolve r
  let env ← getEnv
  let s ← closureOf root
  let mut mods : NameSet := {}
  for x in s.visited.toList do
    if (`Salt).isPrefixOf x then
      if let some m := env.getModuleFor? x then mods := mods.insert m
  let modList := mods.toList.toArray.qsort Name.lt
  let siegelish := modList.filter fun m => hasSub m "Siegel" || hasSub m "DHCore" || hasSub m "Page"
  let mut hits : Array Name := #[]
  for x in s.visited.toList do
    if (`Salt).isPrefixOf x then
      if let some m := env.getModuleFor? x then
        if hasSub m "Siegel" || hasSub m "DHCore" || hasSub m "Page" then hits := hits.push x
  let hitsSorted := hits.qsort Name.lt
  logInfo (m!"CERT REPORT {root}: closure {s.count} ({s.saltN} under Salt, "
    ++ m!"{modList.size} Salt modules), sorryAx: {s.visited.contains ``sorryAx}; "
    ++ m!"Siegel/DHCore/Page-named modules: {siegelish.size} [{render siegelish.toList}]; "
    ++ m!"constants from them ({hitsSorted.size}): {render hitsSorted.toList}")
  for t in targets do
    if s.visited.contains t then
      logInfo m!"CERT REPORT   {root} reaches {t} — path: {render (pathTo s root t)}"
    else
      logInfo m!"CERT REPORT   {root} does not reach {t}"

end Salt.SW.StandoffCert

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see): the direct consumer at
-- Fold.lean:167 and the proof-only consumer at Gate.lean:154.
#assert_reaches Salt.SW.psi1AP_main_bound Salt.SW.siegel_theorem
#assert_reaches Salt.SW.siegelWalfisz_holds Salt.SW.siegel_theorem

-- THE CERTIFICATE: the standoff route excludes all three, at both levels.
#assert_not_reaches Salt.SW.psi1AP_main_bound_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.SW.psi1AP_main_bound_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.SW.psi1AP_main_bound_of_standoff Salt.SW.L1_lower_siegel
#assert_not_reaches Salt.SW.siegelWalfisz_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.SW.siegelWalfisz_of_standoff Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.SW.siegelWalfisz_of_standoff Salt.SW.L1_lower_siegel

-- TOKEN CHECKS (order clause 7): the conclusions ARE the landed statements.
#assert_conclusion_is Salt.SW.psi1AP_main_bound_of_standoff 3 Salt.SW.psi1AP_main_bound
#assert_conclusion_is Salt.SW.siegelWalfisz_of_standoff 3 Salt.SW.siegelWalfisz_holds

-- REPORTS (no assertion): the full census of each frozen name and of the ¬F horn.
#closure_report Salt.SW.NoSiegelZerosAt
#closure_report Salt.SW.psi1AP_main_bound_of_standoff
#closure_report Salt.SW.siegelWalfisz_of_standoff
#closure_report Salt.SW.not_fulcrum_siegelFree_SW
