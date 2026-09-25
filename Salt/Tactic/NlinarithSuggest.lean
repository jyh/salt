/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Tactic.AuditAxioms

/-!
# `nlinarith?` — certificate replay for `nlinarith` (ledger T3, second cut; O15)

`nlinarith` multiplies every pair of comparisons in the context before it searches, so a context
of ninety comparisons hands the oracle four thousand facts for a certificate that uses five.  The
O15 census measured one ladder module at 408.7 s of `nlinarith` in 441 s of tactic time, and the
price brief measured two calls of the heaviest theorem at 280–380 k heartbeats each — for
certificates of two and five facts — with the same goals closing by name in a fraction of that.

`nlinarith?` runs the search ONCE and prints the call that replays its certificate:

* **L1** `nlinarith only [h₁, …, hₖ]` — the base hypotheses the certificate used, directly or as
  product factors (plus any square / cast-nonnegativity facts it used, as explicit terms);
* **L2** `linarith only [h₁, …, mul_nonneg_of_nonpos_of_nonpos (sub_nonpos_of_le hᵢ) (…), …]` —
  the exact products the certificate used, so no product is regrown at all.

Both are VERIFIED by re-running them before they are printed; L2 is offered only when every used
factor is printable (a named hypothesis, a passed term, a square or a cast fact — never the
negated goal), and the tool closes the goal with the strongest suggestion that verified.

## Why it owns its provenance

`Linarith.preprocess` carries none: `filterComparisons` drops entries, `natToInt` PREPENDS
nonnegativity facts, `nlinarithExtras` returns `squares ++ originals ++ products`.  So this file
runs the default chain itself over `(proof, tag)` pairs, re-implements the two `private` product
helpers with tags, and maps `proveFalseByLinarith`'s certificate indices back through them.

## Declared limits (they ride with the verdict, in the tool's own error text)

`splitNe` is refused; a certificate whose products touch the negated goal gets L1 only, with the
reason printed; hypotheses that are negations or that `cancelDenoms` rescaled print by name at L1
and may fail L2's verification, in which case L2 is withheld; the tool costs one full search plus
one or two verification runs at conversion time — it is an executor-time instrument, and the
saving is at every later build.  Nothing here bears on twin primes.
-/

namespace Salt.Tactic.NlinarithSuggest

open Lean Elab Tactic Meta
open Mathlib Mathlib.Tactic Mathlib.Tactic.Linarith

/-- Where a preprocessed fact came from. -/
inductive Prov where
  /-- the negated goal (`applyContrLemma`'s new hypothesis) — not printable -/
  | goal
  /-- a named local hypothesis -/
  | hyp (fv : FVarId)
  /-- the `i`-th term passed in `[...]` (printable by its own syntax) -/
  | term (i : Nat)
  /-- a nonnegativity fact a global preprocessor added; `ty` is its statement -/
  | aux (ty : Expr)
  /-- `sq_nonneg e` (`isSq`) or `mul_self_nonneg e` -/
  | sq (e : Expr) (isSq : Bool)
  /-- a product of pre-product facts `i` and `j` -/
  | prod (i j : Nat)
  deriving Inhabited

/-- Run a per-hypothesis preprocessor, each output inheriting its input's tag. -/
def runPerHyp (pp : Preprocessor) (l : List (Expr × Prov)) : MetaM (List (Expr × Prov)) :=
  l.foldrM (fun (e, p) acc => do return ((← pp.transform e).map (·, p)) ++ acc) []

/-- Run a global preprocessor whose output is `aux ++ image`, the image 1:1 with the input
(`natToInt`, `nnrealToReal`): the suffix keeps the input tags, the prefix is tagged `aux`. -/
def runGlobalPrefix (out : List Expr) (l : List (Expr × Prov)) : MetaM (List (Expr × Prov)) := do
  let n := l.length
  if out.length < n then throwError "nlinarith?: a global preprocessor shrank its input"
  let k := out.length - n
  let pre ← (out.take k).mapM fun e => return (e, Prov.aux (← inferType e))
  return pre ++ (out.drop k).zipWith (fun e (_, p) => (e, p)) l

/-- The default chain with tags: `splitConjunctions` · `filterComparisons` · `nnrealToReal` ·
`natToInt` · `strengthenStrictInt` · `compWithZero` · `cancelDenoms`. -/
def preprocessTagged (cfg : LinarithConfig) (g : MVarId) (l : List (Expr × Prov)) :
    MetaM (List (Expr × Prov)) := g.withContext do
  let mut l := l
  if cfg.splitHypotheses then l ← runPerHyp splitConjunctions l
  l ← runPerHyp filterComparisons l
  l ← runGlobalPrefix (← nnrealToReal.transform (l.map Prod.fst)) l
  let [(_, out)] ← natToInt.transform g (l.map Prod.fst)
    | throwError "nlinarith?: natToInt branched"
  l ← runGlobalPrefix out l
  l ← runPerHyp strengthenStrictInt l
  l ← runPerHyp compWithZero l
  l ← runPerHyp cancelDenoms l
  return l

/-- Square facts, tagged (`nlinarithGetSquareProofs`, re-implemented). -/
def squaresTagged (ls : List Expr) : MetaM (List (Expr × Prov)) := do
  let s ← AtomM.run .reducible do
    let si ← ls.foldrM (fun h s' => do findSquares s' (← instantiateMVars (← inferType h))) ∅
    si.toList.mapM fun (i, isSq) => return ((← get).atoms[i]!, isSq)
  s.foldrM (init := []) fun (e, isSq) acc => do
    match ← observing? (mkAppM (if isSq then ``sq_nonneg else ``mul_self_nonneg) #[e]) with
    | none => return acc
    | some pf => return ((← compWithZero.transform pf).map (·, Prov.sq e isSq)) ++ acc

/-- The comparison kind of a preprocessed fact `t R 0` (`lt` if unparsable, as the source does). -/
def kindOf (e : Expr) : MetaM Ineq := do
  try return (← parseCompAndExpr (← inferType e)).1 catch _ => return Ineq.lt

/-- One product proof, exactly as `nlinarithGetProductsProofs` builds it. -/
def productProof? (pa : Ineq) (a : Expr) (pb : Ineq) (b : Expr) : MetaM (Option Expr) :=
  try
    some <$> match pa, pb with
      | Ineq.eq, _ => mkAppM ``zero_mul_eq #[a, b]
      | _, Ineq.eq => mkAppM ``mul_zero_eq #[a, b]
      | Ineq.lt, Ineq.lt => mkAppM ``mul_pos_of_neg_of_neg #[a, b]
      | Ineq.lt, Ineq.le => do
          mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[← mkAppM ``le_of_lt #[a], b]
      | Ineq.le, Ineq.lt => do
          mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, ← mkAppM ``le_of_lt #[b]]
      | Ineq.le, Ineq.le => mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, b]
  catch _ => return none

/-- Products over the upper triangle, tagged by the indices of their factors in `pre`. -/
def productsTagged (pre : Array (Expr × Prov)) : MetaM (List (Expr × Prov)) := do
  let kinds ← pre.mapM fun (e, _) => kindOf e
  let mut out : Array (Expr × Prov) := #[]
  for i in [:pre.size] do
    for j in [i:pre.size] do
      if let some pf ← productProof? kinds[i]! pre[i]!.1 kinds[j]! pre[j]!.1 then
        for e in ← compWithZero.transform pf do
          out := out.push (e, Prov.prod i j)
  return out.toList

/-- The base hypotheses and printable facts behind a set of used tags; `goalUsed` says whether the
negated goal was a product factor (then L2 is withheld). -/
structure Used where
  hyps : Array FVarId := #[]
  terms : Array Nat := #[]
  auxs : Array Expr := #[]
  sqs : Array (Expr × Bool) := #[]
  goalUsedAsFactor : Bool := false
  /-- the used products as (kindᵢ, tagᵢ, kindⱼ, tagⱼ) -/
  prods : Array (Ineq × Prov × Ineq × Prov) := #[]

/-- The elaborator's core: returns the printable pieces of the certificate. -/
def analyze (cfg : LinarithConfig) (onlyOn : Bool) (args : Array Expr) (g : MVarId) :
    MetaM Used := do
  if (← whnfR (← instantiateMVars (← g.getType))).isEq then
    throwError "nlinarith?: an equality goal is not supported (declared limit) — prove the two \
      inequalities separately"
  let (ctr?, g) ← applyContrLemma g
  let (prefType, newVar) : Option Expr × Option Expr := match ctr? with
    | some (t, v) => (some t, some v)
    | none => (none, none)
  let g ← if prefType.isNone && cfg.exfalso then g.exfalso else pure g
  g.withContext do
    let locals ← if onlyOn then pure #[] else getLocalHyps
    let mut base : List (Expr × Prov) := []
    for h in locals do
      if newVar == some h then base := base ++ [(h, Prov.goal)]
      else base := base ++ [(h, Prov.hyp h.fvarId!)]
    if onlyOn then
      if let some nv := newVar then base := [(nv, Prov.goal)]
    for i in [:args.size] do base := base ++ [(args[i]!, Prov.term i)]
    let pre ← preprocessTagged cfg g base
    let sqs ← squaresTagged (pre.map Prod.fst)
    let preAll := (sqs ++ pre).toArray
    let prods ← productsTagged preAll
    let facts := preAll.toList ++ prods
    let factsIdx := (facts.map Prod.fst).zipIdx
    let classes ← partitionByTypeIdx factsIdx
    -- the preferred class first (the goal's type), then the rest, as `runLinarith` does
    let ordered : List (List (Expr × Nat)) ← do
      match prefType with
      | some t =>
        let (i, vs) ← classes.find t
        let rest := (classes.eraseIdxIfInBounds i).toList.map Prod.snd
        pure (vs :: rest)
      | none => pure (classes.toList.map Prod.snd)
    let mut result? : Option (List Nat) := none
    for cls in ordered do
      if result?.isSome then break
      if cls.isEmpty then continue
      try
        let (_, idxs) ← proveFalseByLinarith cfg.transparency cfg.oracle cfg.discharger g
          (cls.map Prod.fst)
        result? := some (idxs.map fun i => cls[i]!.2)
      catch _ => pure ()
    let some usedIdx := result? | throwError "nlinarith? failed to find a contradiction"
    let factArr := facts.toArray
    let kindArr ← factArr.mapM fun (e, _) => kindOf e
    let mut u : Used := {}
    let mark (u : Used) (p : Prov) : Used :=
      match p with
      | .goal => { u with goalUsedAsFactor := true }
      | .hyp fv => if u.hyps.contains fv then u else { u with hyps := u.hyps.push fv }
      | .term i => if u.terms.contains i then u else { u with terms := u.terms.push i }
      | .aux ty => { u with auxs := u.auxs.push ty }
      | .sq e b => { u with sqs := u.sqs.push (e, b) }
      | .prod _ _ => u
    for i in usedIdx do
      match factArr[i]!.2 with
      | .prod a b =>
        let (pa, pb) := (preAll[a]!.2, preAll[b]!.2)
        u := mark (mark u pa) pb
        -- the negated goal used directly is fine (linarith re-adds it); as a FACTOR it is
        -- not printable
        u := { u with prods := u.prods.push (kindArr[a]!, pa, kindArr[b]!, pb) }
        if pa matches .goal || pb matches .goal then u := { u with goalUsedAsFactor := true }
      | .goal => pure ()
      | p => u := mark u p
    return u

/-- An identifier without hygiene marks, so a printed suggestion pastes back verbatim. -/
def cid (n : Name) : Term := mkIdent n

/-- Print one base fact as a term. -/
def factTerm (argStxs : Array Term) : Prov → MetaM (Option Term)
  | .hyp fv => return some (mkIdent (← fv.getUserName))
  | .term i => return argStxs[i]?
  | .aux ty => do
    let tyS ← PrettyPrinter.delab ty
    return some (← `(($(cid ``Nat.cast_nonneg) _ : $tyS)))
  | .sq e true => do
    let eS ← PrettyPrinter.delab e; return some (← `($(cid ``sq_nonneg) $eS))
  | .sq e false => do
    let eS ← PrettyPrinter.delab e; return some (← `($(cid ``mul_self_nonneg) $eS))
  | _ => return none

/-- Wrap a printable fact into its `_ R 0` form, as `compWithZero` does. -/
def wrapZero (k : Ineq) (t : Term) : MetaM Term :=
  match k with
  | .le => `($(cid ``Mathlib.Tactic.Linarith.sub_nonpos_of_le) $t)
  | .lt => `($(cid ``Mathlib.Tactic.Linarith.sub_neg_of_lt) $t)
  | .eq => `($(cid ``sub_eq_zero_of_eq) $t)

/-- Print one used product exactly as it was built. -/
def prodTerm (argStxs : Array Term) (pa : Ineq) (a : Prov) (pb : Ineq) (b : Prov) :
    MetaM (Option Term) := do
  let some ta ← factTerm argStxs a | return none
  let some tb ← factTerm argStxs b | return none
  let (wa, wb) := (← wrapZero pa ta, ← wrapZero pb tb)
  let mnn := cid ``mul_nonneg_of_nonpos_of_nonpos
  let lol := cid ``le_of_lt
  match pa, pb with
  | .eq, _ => return some (← `($(cid ``Mathlib.Tactic.Linarith.zero_mul_eq) $wa $wb))
  | _, .eq => return some (← `($(cid ``Mathlib.Tactic.Linarith.mul_zero_eq) $wa $wb))
  | .lt, .lt => return some (← `($(cid ``mul_pos_of_neg_of_neg) $wa $wb))
  | .lt, .le => return some (← `($mnn ($lol $wa) $wb))
  | .le, .lt => return some (← `($mnn $wa ($lol $wb)))
  | .le, .le => return some (← `($mnn $wa $wb))

/-- The L1 and (optional) L2 suggestions from a `Used` record. -/
def suggestions (argStxs : Array Term) (u : Used) :
    MetaM (TSyntax `tactic × Option (TSyntax `tactic)) := do
  let mut baseTerms : Array Term := #[]
  for fv in u.hyps do baseTerms := baseTerms.push (mkIdent (← fv.getUserName))
  for i in u.terms do if let some t := argStxs[i]? then baseTerms := baseTerms.push t
  for ty in u.auxs do
    if let some t ← factTerm argStxs (.aux ty) then baseTerms := baseTerms.push t
  for (e, b) in u.sqs do
    if let some t ← factTerm argStxs (.sq e b) then baseTerms := baseTerms.push t
  let l1 ← `(tactic| nlinarith only [$baseTerms,*])
  if u.goalUsedAsFactor then return (l1, none)
  let mut prodTerms : Array Term := #[]
  for (pa, a, pb, b) in u.prods do
    let some t ← prodTerm argStxs pa a pb b | return (l1, none)
    prodTerms := prodTerms.push t
  let allTerms := baseTerms ++ prodTerms
  let l2 ← `(tactic| linarith only [$allTerms,*])
  return (l1, some l2)

/-- Run a candidate tactic from a saved state and report whether it closed the goal. -/
def verifies (st : Tactic.SavedState) (stx : TSyntax `tactic) : TacticM Bool := do
  st.restore
  try
    evalTactic stx
    let ok := (← getUnsolvedGoals).isEmpty
    return ok
  catch _ => return false

syntax (name := nlinarithSuggest) "nlinarith?" "!"? Mathlib.Tactic.linarithArgsRest : tactic

elab_rules : tactic
  | `(tactic| nlinarith?%$tk $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) =>
    withMainContext do
      let argStxs : Array Term := (args.map (Syntax.TSepArray.getElems)).getD #[]
      let argExprs ← argStxs.mapM (elabTermWithoutNewMVars `nlinarith?)
      let cfg := (← Mathlib.Tactic.elabLinarithConfig cfg).updateReducibility bang.isSome
      if cfg.splitNe then throwError "nlinarith?: `splitNe` is not supported (declared limit)"
      let g ← getMainGoal
      let st ← saveState
      let used ← try analyze cfg o.isSome argExprs g
        catch e => st.restore; throw e
      st.restore
      let (l1, l2?) ← suggestions argStxs used
      let l1ok ← verifies st l1
      let l2ok ← match l2? with | some l2 => verifies st l2 | none => pure false
      st.restore
      let l1note := if used.goalUsedAsFactor then
        "; L2 withheld: the negated goal was a product factor" else ""
      match l2?, l2ok, l1ok with
      | some l2, true, true =>
        evalTactic l2
        Lean.Meta.Tactic.TryThis.addSuggestions tk #[l2, l1]
          (header := "Try these (L2 exact products, then L1):")
      | some l2, true, false =>
        evalTactic l2
        Lean.Meta.Tactic.TryThis.addSuggestion tk l2 (header := "Try this (L2; L1 did not verify):")
      | _, _, true =>
        evalTactic l1
        Lean.Meta.Tactic.TryThis.addSuggestion tk l1 (header := s!"Try this (L1{l1note}):")
      | _, _, false =>
        throwError "nlinarith?: found a certificate but its replay did not verify — L1 was\n  {l1}\
          \n(this is a refusal, not a proof; run `nlinarith` at this site and report the case)"

end Salt.Tactic.NlinarithSuggest

/-! ## Self-tests (red-first; the mutant drive is in the seat record) -/

section Tests

/-- info: Try these (L2 exact products, then L1):
  [apply] linarith only [ha, hb,
    mul_nonneg_of_nonpos_of_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le ha)
      (Mathlib.Tactic.Linarith.sub_nonpos_of_le hb)]
  [apply] nlinarith only [ha, hb]
-/
#guard_msgs (whitespace := lax) in
-- A1: a product of two named hypotheses — both levels print
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by nlinarith?

/-- info: Try these (L2 exact products, then L1):
  [apply] linarith only [h, mul_self_nonneg x]
  [apply] nlinarith only [h, mul_self_nonneg x]
-/
#guard_msgs (whitespace := lax) in
-- A2: a square term the certificate needs (`mul_self_nonneg x`), printed as an explicit term
example (x y : ℝ) (h : x * x ≤ y) : 0 ≤ y := by nlinarith?

/-- info: Try this (L1):
  [apply] nlinarith only [h, (Nat.cast_nonneg _ : 0 ≤ ↑n)]
-/
#guard_msgs (whitespace := lax) in
-- A4: a nat-cast atom — the `natCast_nonneg` auxiliary is used and printed with its type; L2 is
-- withheld here because its replay did not verify (the aux fact's product), which is the design
example (n : ℕ) (x : ℝ) (h : x ≤ 0) : x * (n : ℝ) ≤ 0 := by nlinarith?

/-- info: Try these (L2 exact products, then L1):
  [apply] linarith only [h, hb,
    Mathlib.Tactic.Linarith.zero_mul_eq (sub_eq_zero_of_eq h) (Mathlib.Tactic.Linarith.sub_nonpos_of_le hb)]
  [apply] nlinarith only [h, hb]
-/
#guard_msgs (whitespace := lax) in
-- A5: an equality hypothesis as a product factor (`zero_mul_eq`)
example (a b : ℝ) (h : a = 0) (hb : 0 ≤ b) : a * b ≤ 0 := by nlinarith?

/-- info: Try these (L2 exact products, then L1):
  [apply] linarith only [ha, hb,
    mul_nonneg_of_nonpos_of_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le ha)
      (Mathlib.Tactic.Linarith.sub_nonpos_of_le hb)]
  [apply] nlinarith only [ha, hb]
-/
#guard_msgs (whitespace := lax) in
-- D1 (math's non-author read of #178, 2026-09-24 19:11): A1 with a DISTRACTOR hypothesis. The
-- suggestion must OMIT `_hc` — a distractor is the tool's whole use case (five facts of ninety) and
-- no earlier arm had one, so a mutant that marks every hypothesis as used survived them all; it reds
-- here and only here. Named `_hc` because `#guard_msgs` also captures the unused-variable lint.
example (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : c ≤ 5) : 0 ≤ a * b := by nlinarith?

-- A6: a goal `nlinarith` cannot close — the tool REFUSES (no suggestion, no proof)
example (a : ℝ) (_h : 0 ≤ a) : a ≤ 1 ∨ True := by
  fail_if_success (left; nlinarith?)
  right; trivial
-- A8: an equality GOAL is a declared limit — refused with its own message
example (x : ℝ) (h : x ≤ 0) (h' : 0 ≤ x) : x = 0 := by
  fail_if_success nlinarith?
  linarith

/-! The pasted suggestions, as NAMED theorems so `#audit_axioms` can read them: each is the text
printed above, pasted verbatim. -/

theorem pasted_A1 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  linarith only [ha, hb,
    mul_nonneg_of_nonpos_of_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le ha)
      (Mathlib.Tactic.Linarith.sub_nonpos_of_le hb)]
theorem pasted_A2 (x y : ℝ) (h : x * x ≤ y) : 0 ≤ y := by
  linarith only [h, mul_self_nonneg x]
theorem pasted_A4 (n : ℕ) (x : ℝ) (h : x ≤ 0) : x * (n : ℝ) ≤ 0 := by
  nlinarith only [h, (Nat.cast_nonneg _ : 0 ≤ ↑n)]
theorem pasted_A5 (a b : ℝ) (h : a = 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  linarith only [h, hb,
    Mathlib.Tactic.Linarith.zero_mul_eq (sub_eq_zero_of_eq h)
      (Mathlib.Tactic.Linarith.sub_nonpos_of_le hb)]

#audit_axioms pasted_A1 pasted_A2 pasted_A4 pasted_A5

end Tests
