#!/usr/bin/env python3
"""THE O13 REACH CENSUS, AS A COMMITTED INSTRUMENT (objective O13, STATUS row 44).

The rung-4 census (docs/exploration/o13-rung4-census-2026-10-24.md) ran from an uncommitted Lean
scratch with its roots typed by hand and one twin test, a NAME heuristic: a constant whose name
extends the root's with `standoff` or `sevenEighths`. Addendum 4 found three twins that heuristic
misses (`siegelWalfisz_holds` -> `siegelWalfisz_of_standoff` and two more), and at main 91c92dc0 it
also over-matches: a prefix collision credits superseded `logChowla2_ineffective` with
`logChowla2_ineffective_v7_of_standoff`, a twin of another statement. This script makes the census
reproducible, reads the twins RESULTS already records, and narrows the name test to the exact
suffixes `<root>_of_standoff` / `<root>_of_sevenEighths`:

  gen    read docs/RESULTS.md and write a Lean scratch: every table row's Lean name is a root, its
         File:line column gives the import, and RESULTS §10's "the conclusion of `X`" pairs each
         §10 row with the root `X` it twins. Extra roots (a paper's citations) come from --names.
  parse  read the saltbuild log of that scratch and print the classes and totals. Exit 0 only if
         every REACHES row is by design; exit 1 on an owed row; exit 2 if the log is not a clean
         run of THIS scratch (no `saltbuild EXIT=0` / `o13-ci EXIT=0`, a tagged error, a control that did not print,
         a count that does not match the manifest).

The build between them is `../saltbuild.sh <scratch>` (never bare lake, never piped). A scratch run cannot
build its dependencies, so build the scratch's imports first, through the build arm in the same tree
(`../saltbuild.sh <every module the scratch imports>`):
  python3 scripts/o13_census.py gen [--names FILE --import MOD ...] [--out Scratch.lean]
  ../saltbuild.sh Scratch.lean > census.log 2>&1
  python3 scripts/o13_census.py parse census.log [--manifest Scratch.lean.json]
  python3 scripts/o13_census.py texnames papers/witness/main.tex > names.txt   (read it, then --names)
  python3 scripts/o13_census.py --self-test
In CI (.github/workflows/reach_census.yml) the scratch runs under `lake env lean` and the step appends
its own exit line, `o13-ci EXIT=<rc>`, which parse reads exactly as it reads the wrapper's. The
red-first plant is `gen --drop-by-design NAME`: that BY_DESIGN row is left out of the scratch, so the
run must read it REACHES-OWED (rc 1); parse prints the plant above the verdict so a planted red is
never read as a real one.

Classes, per root (the walk is `Salt.SW.StandoffCert.closureOf`, the relation behind
`#assert_not_reaches`; the targets are its three Siegel names):
  FREE                the closure contains none of the three targets
  TWIN-EXISTS         it reaches one, and a twin's closure contains none of them and no sorryAx;
                      the twin's source is printed: (§10) from the RESULTS map, (name) from the heuristic
  REACHES-BY-DESIGN   it reaches one, no twin, and the row is [SUPERSEDED] or in BY_DESIGN below
  REACHES-OWED        it reaches one, no twin, and nothing above explains it
  MISSING             the root (or a §10 twin) is not in the environment the scratch built

LIMITS, printed with every verdict:
  - The roots are RESULTS's table rows (and --names); a result with no row is not walked. An
    undotted name resolves only to constants declared in a Salt/SaltC1/Keller module, so a bare
    binder or an undotted core axiom (`propext`) named in prose reads UNRESOLVED rather than walking
    a foreign constant; a dotted one (`Classical.choice`, `Quot.sound`) resolves and is walked.
  - "Reaches" is constant reference over types and values, the relation `#print axioms` uses. FREE
    means free of the three names only, not of any other hypothesis, and says nothing on effectivity.
  - `L1_lower_siegel` is effective; a REACHES row is not by itself a claim of ineffectivity.
  - A FREE root whose closure holds `sorryAx` is reported (SORRY) and read as owed.
  - A §10 twin is matched by its row's words; a row that names its source differently is missed and
    the root reads REACHES. A (name) twin is matched by the exact suffix only, and its STATEMENT is
    not compared with the root's (the §10 rows' `#assert_conclusion_is` certificates do that for
    §10 twins); every claimed twin's closure is walked.
"""
from __future__ import annotations

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(ROOT, "docs", "RESULTS.md")

# REACHES rows left by design, with the record that leaves them (census addenda 4 and 6).
BY_DESIGN = {
    "Salt.SW.dh_repulsion_ordered":
        "Deuring-Heilbronn: a standoff form assumes away its subject (census addendum 6)",
    "Salt.HB.dh_repulsion_tall_at":
        "Deuring-Heilbronn: a standoff form assumes away its subject (census addendum 6)",
    "Salt.SW.dh_repulsion_tall":
        "Deuring-Heilbronn, the flagship paper's Theorem rep: as dh_repulsion_tall_at (addenda 6, 7, 10)",
    "Salt.HB.heathBrownDichotomy_of_N7":
        "the crown dichotomy, satisfied through its Siegel arm (O76; census addendum 4)",
}

# The control the item exists for: the twin the name heuristic missed must be found through §10.
CONTROL_TWIN = ("Salt.SW.siegelWalfisz_holds", "Salt.SW.siegelWalfisz_of_standoff")

CELL = re.compile(r"(?<!\\)\|")  # a cell boundary; `\|` inside a cell is the table's escaped pipe
CONCL = re.compile(r"the conclusion of `([^`]+)`")
PATH = re.compile(r"^((?:Salt|SaltC1|Keller)[A-Za-z0-9_/]*)\.lean:\d+$")


def parse_results(text: str):
    """Rows of every RESULTS table: (name, section, superseded, module, statement)."""
    rows, section = [], ""
    for line in text.splitlines():
        if line.startswith("## "):
            section = line[3:].split(" ", 1)[0].rstrip(".")
            continue
        if not line.startswith("| `"):
            continue
        cells = CELL.split(line)
        if len(cells) < 5:
            continue
        name, stmt, path = cells[1].split("`")[1], cells[2], cells[3]
        pm = PATH.match(path.strip())
        rows.append({
            "name": name,
            "section": section,
            "superseded": "[SUPERSEDED" in stmt,
            "module": pm.group(1).replace("/", ".") if pm else None,
            "statement": stmt,
        })
    return rows


def twin_map(rows):
    """§10's map, unconditional root -> [twin], and the §10 rows whose source did not resolve."""
    names = [r["name"] for r in rows]
    tm, unresolved = {}, []
    for r in rows:
        if r["section"] != "10":
            continue
        m = CONCL.search(r["statement"])
        if not m:
            continue
        x = m.group(1)
        cands = [n for n in names if n == x or n.endswith("." + x)]
        cands = [n for n in cands if n != r["name"]]
        if len(cands) != 1:
            # not a RESULTS row (or ambiguous): Lean matches it by the root's last component
            unresolved.append((r["name"], x, cands))
            tm.setdefault(x, []).append(r["name"])
            continue
        tm.setdefault(cands[0], []).append(r["name"])
    return tm, unresolved


def lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


ELAB = r'''
open Lean Elab Command Salt.SW.StandoffCert

elab "#o13_census" : command => do
  let env ← getEnv
  let all : Array Name := env.constants.fold (init := #[]) fun acc n _ => acc.push n
  let ownMod (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => let m := env.header.moduleNames[i.toNat]!
                (`Salt).isPrefixOf m || (`SaltC1).isPrefixOf m || (`Keller).isPrefixOf m
    | none => false
  let resolveS (s : String) : List Name :=
    if s.contains '.' then
      let n := s.toName
      if (env.find? n).isSome then [n] else []
    else
      -- an undotted name resolves only to a constant DECLARED in this repository's modules
      -- (never a Mathlib or core constant that happens to share the last component)
      (all.filter fun n => (match n with
        | .str _ t => t == s
        | _ => false) && !n.isInternal && ownMod n).toList
  let nameTwins (root : Name) : List Name := Id.run do
    let L := root.getString!
    let mut r : List Name := []
    for n in all do
      match n with
      | .str _ s =>
        if s == L ++ "_of_standoff" || s == L ++ "_of_sevenEighths" then
          r := n :: r
      | _ => pure ()
    return r
  let isFree (t : Name) : CommandElabM Bool := do
    let st ← closureOf t
    return targets.all (!st.visited.contains ·) && !st.visited.contains ``sorryAx
  let mut nF : Nat := 0; let mut nT : Nat := 0; let mut nD : Nat := 0; let mut nO : Nat := 0
  let mut nM : Nat := 0; let mut nU : Nat := 0; let mut nEntries : Nat := 0
  let mut nRoots : Nat := 0  -- distinct constants walked; an entry resolving to nothing is not one
  let mut seen : NameSet := {}
  -- a RESULTS row marked SUPERSEDED is by design under any tag it is reached by
  let superseded : List Name := (o13Roots.filter fun (_, t) => (t.splitOn "SUPERSEDED").length > 1).map
    fun (s, _) => s.toName
  for (s, tag) in o13Roots do
    nEntries := nEntries + 1
    let hits := resolveS s
    if hits.isEmpty then
      if tag == "NAMES" then
        logInfo m!"O13 UNRESOLVED {s} [{tag}]"
        nU := nU + 1
      else
        logInfo m!"O13 MISSING {s} [{tag}]"
        nM := nM + 1
    for root in hits do
      if seen.contains root then
        continue
      seen := seen.insert root
      nRoots := nRoots + 1
      let st ← closureOf root
      let reached := targets.filter st.visited.contains
      let sorryIn := st.visited.contains ``sorryAx
      if reached.isEmpty then
        logInfo m!"O13 FREE {root} [{tag}] closure={st.count} sorryAx={sorryIn}"
        nF := nF + 1
        continue
      let keyHit (k : String) : Bool :=
        if k.contains '.' then k.toName == root else (match root with
          | .str _ t => t == k
          | _ => false)
      let pairs := o13TwinMap.filter (keyHit ·.1)
      let mut mapped : List Name := []
      for (_, ts) in pairs do
        let hs := resolveS ts
        if hs.isEmpty then
          logInfo m!"O13 MISSING-TWIN {ts} (§10, of {root})"
          nM := nM + 1
        mapped := mapped ++ hs
      let mut freeTw : List String := []
      for t in mapped do
        if ← isFree t then freeTw := freeTw ++ [s!"{t} (§10)"]
        else logInfo m!"O13 TWIN-REACHES {t} (§10, of {root})"
      for t in nameTwins root do
        if !mapped.contains t then
          if ← isFree t then freeTw := freeTw ++ [s!"{t} (name)"]
      let first := match reached with
        | t :: _ => render (pathTo st root t)
        | [] => "-"
      if !freeTw.isEmpty then
        logInfo m!"O13 TWIN-EXISTS {root} [{tag}] targets={render reached} twins={", ".intercalate freeTw}"
        nT := nT + 1
      else
        match o13ByDesign.find? (·.1.toName == root) with
        | some (_, why) =>
          logInfo m!"O13 REACHES-BY-DESIGN {root} [{tag}] targets={render reached} why={why} path={first}"
          nD := nD + 1
        | none =>
          if (tag.splitOn "SUPERSEDED").length > 1 || superseded.contains root then
            logInfo m!"O13 REACHES-BY-DESIGN {root} [{tag}] targets={render reached} why=superseded row path={first}"
            nD := nD + 1
          else
            logInfo m!"O13 REACHES-OWED {root} [{tag}] targets={render reached} sorryAx={sorryIn} path={first}"
            nO := nO + 1
  logInfo m!"O13 TOTAL entries={nEntries} roots={nRoots} FREE={nF} TWIN-EXISTS={nT} REACHES-BY-DESIGN={nD} REACHES-OWED={nO} MISSING={nM} UNRESOLVED={nU}"

#assert_targets_exist
#assert_reaches __CTRL_ROOT__ Salt.SW.siegel_theorem
#assert_not_reaches __CTRL_TWIN__ Salt.SW.siegel_theorem
#o13_census
'''


DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\s+"
                  r"([^\s:({\[]+)", re.M)


def decl_index():
    """Last name component -> the modules (Salt/, SaltC1/) whose source declares it."""
    idx = {}
    for top in ("Salt", "SaltC1"):
        for d, _, fs in os.walk(os.path.join(ROOT, top)):
            for f in fs:
                if not f.endswith(".lean"):
                    continue
                path = os.path.join(d, f)
                mod = os.path.relpath(path, ROOT)[:-5].replace(os.sep, ".")
                for m in DECL.finditer(open(path, encoding="utf-8", errors="replace").read()):
                    idx.setdefault(m.group(1).split(".")[-1], set()).add(mod)
    return idx


def drop_by_design(names):
    """BY_DESIGN without `names`; a name that is not a BY_DESIGN key is refused (a void plant)."""
    unknown = [n for n in names if n not in BY_DESIGN]
    if unknown:
        raise KeyError(f"not a BY_DESIGN row: {' '.join(unknown)}")
    return {k: v for k, v in BY_DESIGN.items() if k not in names}


def gen(args):
    out, names_file, imports, drops = "Scratch.lean", None, [], []
    i = 0
    while i < len(args):
        a = args[i]
        if a == "--out":
            out = args[i + 1]; i += 2
        elif a == "--names":
            names_file = args[i + 1]; i += 2
        elif a == "--import":
            imports.append(args[i + 1]); i += 2
        elif a == "--drop-by-design":
            drops.append(args[i + 1]); i += 2
        else:
            sys.exit(f"o13_census gen: unknown argument {a}")
    try:
        by_design = drop_by_design(drops)
    except KeyError as e:
        sys.exit(f"o13_census gen: --drop-by-design: {e.args[0]}")
    rows = parse_results(open(RESULTS, encoding="utf-8").read())
    tm, unresolved = twin_map(rows)
    mods = {r["module"] for r in rows if r["module"]} | set(imports) | {"Salt.SW.StandoffCert"}
    roots = [(r["name"], f"RESULTS §{r['section']}" + (" SUPERSEDED" if r["superseded"] else ""))
             for r in rows]
    unlocated = []
    if names_file:
        idx = decl_index()
        for line in open(names_file, encoding="utf-8"):
            n = line.split("#", 1)[0].strip()
            if not n:
                continue
            roots.append((n, "NAMES"))
            hit = idx.get(n.split(".")[-1])
            if hit:
                mods |= hit
            else:
                unlocated.append(n)
    mods = sorted(mods)
    pairs = [(k, t) for k, ts in sorted(tm.items()) for t in ts]
    L = [f"import {m}" for m in mods]
    L.append("")
    L.append("/-- Generated by scripts/o13_census.py gen; do not edit or commit. -/")
    L.append("def o13Roots : List (String × String) := [")
    L.append(",\n".join(f"  ({lean_str(n)}, {lean_str(t)})" for n, t in roots))
    L.append("]")
    L.append("def o13TwinMap : List (String × String) := [")
    L.append(",\n".join(f"  ({lean_str(k)}, {lean_str(t)})" for k, t in pairs))
    L.append("]")
    L.append("def o13ByDesign : List (String × String) := [")
    L.append(",\n".join(f"  ({lean_str(k)}, {lean_str(v)})" for k, v in sorted(by_design.items())))
    L.append("]")
    L.append(ELAB.replace("__CTRL_ROOT__", CONTROL_TWIN[0]).replace("__CTRL_TWIN__", CONTROL_TWIN[1]))
    with open(out, "w", encoding="utf-8") as f:
        f.write("\n".join(L))
    manifest = {"roots": len(roots), "results_rows": len(rows), "twin_pairs": len(pairs),
                "imports": len(mods), "unresolved_s10": unresolved,
                "control": list(CONTROL_TWIN), "dropped_by_design": drops}
    with open(out + ".json", "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=1)
    print(f"o13_census gen: {out}: {len(roots)} roots ({len(rows)} RESULTS rows), "
          f"{len(pairs)} §10 twin pairs, {len(mods)} imports")
    if unlocated:
        print(f"  --names with no declaring file found in source ({len(unlocated)}; they read UNRESOLVED "
              f"unless an import brings them): {' '.join(unlocated)}")
    for name, x, cands in unresolved:
        print(f"  §10 source not a RESULTS row: {name} names `{x}` (RESULTS matches {cands or 'none'}); "
              f"paired by the root's last component")
    if CONTROL_TWIN[1] not in tm.get(CONTROL_TWIN[0], []):
        print(f"  CONTROL ABSENT from the map: {CONTROL_TWIN[0]} -> {CONTROL_TWIN[1]}")
        return 2
    return 0


ERR = re.compile(r":[0-9]+:[0-9]+: error(\([^)]*\))?:|^error: .*:[0-9]+:[0-9]+:")
LINE = re.compile(r"O13 (FREE|TWIN-EXISTS|REACHES-BY-DESIGN|REACHES-OWED|MISSING|MISSING-TWIN|TWIN-REACHES|"
                  r"UNRESOLVED) ")
TOTAL = re.compile(r"O13 TOTAL entries=(\d+) roots=(\d+) FREE=(\d+) TWIN-EXISTS=(\d+) REACHES-BY-DESIGN=(\d+) "
                   r"REACHES-OWED=(\d+) MISSING=(\d+) UNRESOLVED=(\d+)")


def classify_log(text: str, manifest: dict):
    """(rc, report lines). rc 0 clean, 1 owed rows, 2 the log is not a clean run of this scratch."""
    out, bad = [], []
    exits = re.findall(r"^(?:saltbuild|o13-ci) EXIT=(\d+)$", text, re.M)
    if exits != ["0"]:
        bad.append(f"EXIT lines (saltbuild / o13-ci) {exits or 'none'}, want exactly one EXIT=0")
    for n in manifest.get("dropped_by_design", []):
        out.append(f"PLANT: {n} was dropped from BY_DESIGN for this run (red-first); its REACHES-OWED "
                   f"is the plant, not a finding")
    nerr = sum(1 for ln in text.splitlines() if ERR.search(ln))
    if nerr:
        bad.append(f"{nerr} tagged error line(s)")
    root, twin = manifest["control"]
    if f"CERT P+ {root} REACHES Salt.SW.siegel_theorem" not in text:
        bad.append(f"positive control did not print: {root} REACHES siegel_theorem")
    if f"CERT OK: {twin} does NOT reach Salt.SW.siegel_theorem" not in text:
        bad.append(f"control did not print: {twin} does NOT reach siegel_theorem")
    if text.count("CERT T  target present:") != 3:
        bad.append("the three targets were not all reported present")
    totals = TOTAL.findall(text)
    if len(totals) != 1:
        bad.append(f"{len(totals)} TOTAL lines, want 1")
    tw = [ln for ln in text.splitlines() if f"O13 TWIN-EXISTS {root} " in ln]
    if not (len(tw) == 1 and f"{twin} (§10)" in tw[0]):
        bad.append(f"map control: {root} did not class TWIN-EXISTS through {twin} (§10)")
    lines = [ln[ln.index("O13 "):] for ln in text.splitlines() if LINE.search(ln)]
    counts = {}
    for ln in lines:
        k = LINE.search(ln).group(1)
        counts[k] = counts.get(k, 0) + 1
    if totals:
        e, n, f, t, d, o, m, u = map(int, totals[0])
        if e != manifest["roots"]:
            bad.append(f"TOTAL entries={e}, manifest {manifest['roots']}")
        per = (counts.get("FREE", 0), counts.get("TWIN-EXISTS", 0),
               counts.get("REACHES-BY-DESIGN", 0), counts.get("REACHES-OWED", 0))
        if per != (f, t, d, o):
            bad.append(f"per-row counts {per} disagree with TOTAL {(f, t, d, o)}")
        out.append(f"TOTAL entries={e} roots={n} (distinct constants walked) FREE={f} TWIN-EXISTS={t} REACHES-BY-DESIGN={d} "
                   f"REACHES-OWED={o} MISSING={m} UNRESOLVED={u} (a --names entry that names no "
                   f"declaration: a binder, a namespace, a tool; read the list)")
    for k in ("REACHES-OWED", "MISSING", "MISSING-TWIN", "TWIN-REACHES", "UNRESOLVED",
              "REACHES-BY-DESIGN", "TWIN-EXISTS"):
        for ln in lines:
            if ln.startswith(f"O13 {k} "):
                out.append("  " + ln)
    out.append("LIMITS: roots are RESULTS rows and --names only; FREE = free of the three Siegel "
               "names only, not of other hypotheses, and silent on effectivity; L1_lower_siegel is "
               "effective; a §10 twin is matched by its row's words; a (name) twin is the exact suffix "
               "`<root>_of_standoff`/`_of_sevenEighths`, statement not compared.")
    if bad:
        return 2, ["NOT A CLEAN RUN: " + b for b in bad] + out
    # a FREE closure holding sorryAx certifies nothing (the twin test already demands no sorryAx)
    sorry_free = [ln for ln in lines if ln.startswith("O13 FREE ") and "sorryAx=true" in ln]
    for ln in sorry_free:
        out.insert(1, "  SORRY " + ln)
    owed = counts.get("REACHES-OWED", 0) + counts.get("MISSING", 0) \
        + counts.get("MISSING-TWIN", 0) + counts.get("TWIN-REACHES", 0) + len(sorry_free)
    return (1 if owed else 0), out


def parse(args):
    if not args:
        sys.exit("o13_census parse: LOG [--manifest FILE]")
    log, man = args[0], "Scratch.lean.json"
    if len(args) == 3 and args[1] == "--manifest":
        man = args[2]
    rc, lines = classify_log(open(log, encoding="utf-8", errors="replace").read(),
                             json.load(open(man, encoding="utf-8")))
    print("\n".join(lines))
    print(f"o13_census parse: rc {rc}")
    return rc


def self_test():
    rows = parse_results(
        "## 3. SW\n| T | S | F | D | C | A |\n|---|\n"
        "| `Salt.SW.siegelWalfisz_holds` | SW. | Salt/SW/A.lean:1 | d | c | 3 |\n"
        "| `Salt.X.old` | [SUPERSEDED → new] old. | Salt/X.lean:2 | d | c | 3 |\n"
        "## 10. ladder\n| T | S | F | D | C | A |\n|---|\n"
        "| `Salt.SW.siegelWalfisz_of_standoff` | Under h, with `\\|q − p\\| ≤ C`: the conclusion of "
        "`siegelWalfisz_holds`. "
        "| Salt/SW/B.lean:3 | d | c | 3 |\n"
        "| `Salt.SW.lost_of_standoff` | Under h: the conclusion of `nowhere`. | Salt/SW/B.lean:9 | d | c | 3 |\n")
    ok = True

    def check(what, cond):
        nonlocal ok
        print(f"  {'ok ' if cond else 'BAD'} {what}")
        ok = ok and cond

    check("four rows parsed", len(rows) == 4)
    check("SUPERSEDED read from the statement", rows[1]["superseded"])
    check("module from File:line", rows[0]["module"] == "Salt.SW.A")
    check("an escaped pipe stays inside its cell", rows[2]["module"] == "Salt.SW.B")
    tm, unres = twin_map(rows)
    check("§10 map pairs the control", tm.get(CONTROL_TWIN[0]) == [CONTROL_TWIN[1]])
    check("an unresolvable §10 source is reported", [u[1] for u in unres] == ["nowhere"])
    check("... and still paired, by its short name", tm.get("nowhere") == ["Salt.SW.lost_of_standoff"])
    man = {"roots": 3, "control": list(CONTROL_TWIN)}
    good = ("CERT T  target present: a\nCERT T  target present: b\nCERT T  target present: c\n"
            f"CERT P+ {CONTROL_TWIN[0]} REACHES Salt.SW.siegel_theorem — path\n"
            f"CERT OK: {CONTROL_TWIN[1]} does NOT reach Salt.SW.siegel_theorem (closure 9)\n"
            "x.lean:1:0: info: O13 FREE Salt.A.a [RESULTS §1] closure=3 sorryAx=false\n"
            f"x.lean:1:0: info: O13 TWIN-EXISTS {CONTROL_TWIN[0]} [RESULTS §3] targets=t "
            f"twins={CONTROL_TWIN[1]} (§10)\n"
            "x.lean:1:0: info: O13 REACHES-BY-DESIGN Salt.X.old [RESULTS §8 SUPERSEDED] why=superseded row\n"
            "x.lean:1:0: info: O13 TOTAL entries=3 roots=3 FREE=1 TWIN-EXISTS=1 REACHES-BY-DESIGN=1 "
            "REACHES-OWED=0 MISSING=0 UNRESOLVED=0\nsaltbuild EXIT=0\n")
    check("a clean log reads rc 0", classify_log(good, man)[0] == 0)
    owed = good.replace("REACHES-BY-DESIGN Salt.X.old", "REACHES-OWED Salt.X.old").replace(
        "REACHES-BY-DESIGN=1 REACHES-OWED=0", "REACHES-BY-DESIGN=0 REACHES-OWED=1")
    check("an owed row reads rc 1", classify_log(owed, man)[0] == 1)
    check("a FREE root holding sorryAx reads rc 1",
          classify_log(good.replace("closure=3 sorryAx=false", "closure=3 sorryAx=true"), man)[0] == 1)
    for what, mut in [
        ("EXIT=1 reads rc 2", good.replace("EXIT=0", "EXIT=1")),
        ("a tagged error reads rc 2", good + "x.lean:3:4: error(lean.unknownIdentifier): no\n"),
        ("a lake-order error reads rc 2", good + "error: x.lean:3:4: no\n"),
        ("a missing positive control reads rc 2", good.replace("CERT P+", "CERT P-")),
        ("the control found by name only reads rc 2", good.replace(" (§10)", " (name)")),
        ("an entry count off the manifest reads rc 2", good.replace("entries=3", "entries=4")),
        ("per-row counts off the TOTAL read rc 2", good.replace("O13 FREE Salt.A.a", "O13 FREEX")),
    ]:
        check(what, classify_log(mut, man)[0] == 2)
    ci = good.replace("saltbuild EXIT=0", "o13-ci EXIT=0")
    check("the CI exit line reads as the wrapper's (rc 0)", classify_log(ci, man)[0] == 0)
    check("a CI EXIT=1 reads rc 2", classify_log(ci.replace("EXIT=0", "EXIT=1"), man)[0] == 2)
    check("two exit lines read rc 2", classify_log(good + "o13-ci EXIT=0\n", man)[0] == 2)
    check("an exit line quoted mid-line is not an exit line",
          classify_log(good.replace("saltbuild EXIT=0", "said saltbuild EXIT=0"), man)[0] == 2)
    prc, pout = classify_log(owed, dict(man, dropped_by_design=["Salt.X.old"]))
    check("a planted owed row reads rc 1 and prints the plant",
          prc == 1 and any(ln.startswith("PLANT: Salt.X.old") for ln in pout))
    k0 = sorted(BY_DESIGN)[0]
    check("a plant drops exactly its row",
          k0 not in drop_by_design([k0]) and len(drop_by_design([k0])) == len(BY_DESIGN) - 1)
    try:
        drop_by_design(["Salt.not_by_design"]); refused = False
    except KeyError:
        refused = True
    check("a plant naming no BY_DESIGN row is refused", refused)
    print("o13_census self-test:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


TEXMACRO = re.compile(r"\\(?:leaninline|leanname)\{((?:[^{}]|\{[^{}]*\})*)\}")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'₀-₉αβγδεζηθικλμνξπρστυφχψωΞΛΦΨΩ]*$")


def texnames(args):
    """Every identifier a .tex file cites in \\leaninline{} or \\leanname{}, one per line, deduped."""
    if len(args) != 1:
        sys.exit("o13_census texnames FILE.tex")
    text = open(args[0], encoding="utf-8").read()
    seen = []
    for m in TEXMACRO.finditer(text):
        body = re.sub(r"\\allowbreak\s*", "", m.group(1)).replace("\\_", "_")
        body = re.sub(r"\([^)]*\.lean[^)]*\)", " ", body)
        for tok in re.split(r"[\s,]+", body):
            if IDENT.match(tok) and tok not in seen:
                seen.append(tok)
    print("\n".join(seen))
    print(f"# texnames: {len(seen)} identifiers from {len(TEXMACRO.findall(text))} macros in {args[0]}; "
          "an identifier outside the two macros is not read", file=sys.stderr)
    return 0


def main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        return 0
    if argv[0] == "--self-test":
        return self_test()
    if argv[0] == "gen":
        return gen(argv[1:])
    if argv[0] == "parse":
        return parse(argv[1:])
    if argv[0] == "texnames":
        return texnames(argv[1:])
    sys.exit(f"o13_census: unknown command {argv[0]}")


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
