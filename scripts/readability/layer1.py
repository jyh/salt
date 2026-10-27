#!/usr/bin/env python3
"""layer1.py — the LAYER-1 readability script (O83 item 1).

WHAT IT MEASURES
----------------
Six mechanical shadows of "can a mathematician read this and learn from it", over a Lean file,
a directory of Lean files, or several of either (one POPULATION; references across its files
count). Every number is a property of the source text; none is a property of the mathematics.

  depth          the longest chain of population declarations a reader must follow down from the
                 top result: A uses B uses C ... (each link a reference to a population name).
  fan-out        distinct population declarations one declaration references, max and mean:
                 the lemmas a reader holds at once to follow one proof.
  prose/formal   prose characters (module docs, docstrings, comments; the copyright block
                 excluded) over formal characters (non-blank code).
  defs-first     (a) the share of DEFINITIONS (def/abbrev/structure/inductive/class) that carry a
                 docstring, and (b) forward prose references: a backticked population name in a
                 DECLARATION docstring that is declared LATER in the population (the module
                 header is a roadmap and is excluded on purpose). "Later" is IMPORT order across
                 the population's files, then position within a file.
  role lines     the share of THEOREMS/LEMMAS that carry a docstring.
  hidden steps   automation tactics (simp family, omega, decide, norm_num, linarith family,
                 positivity, ring family, aesop, grind, ...) per declaration, and separately the
                 KERNEL-COMPUTATION count (decide / native_decide / rfl-by-evaluation shapes),
                 the signature of a certificate.

and one declared extra, outside the six: numeral density (literals of >= 3 digits per 100 formal
tokens), because certificate data lives there.

WHAT IT DOES NOT MEASURE
------------------------
Whether the prose is TRUE of the code, whether the order is the order a reader needs, whether a
docstring says anything. A file of docstrings reading "lemma." scores perfectly on role lines.
Layer 2 (a non-author reader reconstructing the skeleton) is the instrument for those; this one
only narrows. Names are matched as TOKENS against the population's declared names (full and last
component), so a local variable that shares a declaration's name counts as a reference: an
over-count, declared here.

USAGE
-----
  python3 scripts/readability/layer1.py PATH [PATH ...] [--label NAME] [--json]
  python3 scripts/readability/layer1.py --selftest

The selftest is a mutation suite: every metric is driven by a fixture and a mutant of it, and the
expected direction is derived from the mutation, never typed. Nine arms (2026-10-17) are properties of
the SCANNER itself — prose, strings, comments, attributes, `example`, distinct references, cycles —
each shown red against a mutant of the scanner before it was added.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys

DECL_KW = ("theorem", "lemma", "def", "abbrev", "instance", "structure", "inductive", "class",
           "example", "opaque", "axiom")
THM_KW = {"theorem", "lemma"}
DEF_KW = {"def", "abbrev", "structure", "inductive", "class", "opaque"}
MODIFIERS = ("private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "scoped")

AUTOMATION = ("simp", "simp_all", "simpa", "dsimp", "simp_arith", "norm_num", "omega", "decide",
              "native_decide", "linarith", "nlinarith", "polyrith", "positivity", "ring", "ring_nf",
              "field_simp", "aesop", "grind", "tauto", "norm_cast", "push_cast", "exact_mod_cast",
              "gcongr", "bound", "fin_cases", "interval_cases", "linear_combination")
KERNEL_COMP = ("decide", "native_decide")

IDENT = re.compile(r"[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_'!?.₀-₉α-ωΑ-Ω]*")


def split_source(src: str):
    """Split Lean source into a CODE text (prose blanked, positions kept) and a list of prose spans
    (kind, start, end, text). Kinds: copyright · module · doc · comment. Block comments nest."""
    code = list(src)
    spans = []
    i, n = 0, len(src)
    seen_code = False
    while i < n:
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            spans.append(("comment", i, j, src[i:j]))
            for k in range(i, j):
                code[k] = " "
            i = j
            continue
        if src.startswith("/-", i):
            kind = "doc" if src.startswith("/--", i) else "module" if src.startswith("/-!", i) else "comment"
            depth, j = 0, i
            while j < n:
                if src.startswith("/-", j):
                    depth += 1; j += 2; continue
                if src.startswith("-/", j):
                    depth -= 1; j += 2
                    if depth == 0:
                        break
                    continue
                j += 1
            text = src[i:j]
            if kind == "comment" and not seen_code and "Copyright" in text:
                kind = "copyright"
            spans.append((kind, i, j, text))
            for k in range(i, j):
                if code[k] != "\n":
                    code[k] = " "
            i = j
            continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            # a string literal's CONTENT is not code: blank it (newlines kept, so line starts inside
            # a multi-line literal cannot read as declarations), keep the quotes
            for k in range(i + 1, min(j, n)):
                if code[k] != "\n":
                    code[k] = " "
            i = j + 1
            seen_code = True
            continue
        if not src[i].isspace():
            seen_code = True
        i += 1
    return "".join(code), spans


DECL_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t\n]*)*(?:(?:" + "|".join(MODIFIERS) + r")[ \t]+)*("
    + "|".join(DECL_KW) + r")\b[ \t]*([^\s:({\[]*)", re.M)
STOP_RE = re.compile(r"^(?:end|namespace|section|noncomputable section|open|variable|attribute|"
                     r"set_option|universe|#)\b", re.M)
AUTO_RE = re.compile(r"(?<![A-Za-z0-9_.'])(" + "|".join(sorted(AUTOMATION, key=len, reverse=True))
                     + r")(?![A-Za-z0-9_'])")
NUM_RE = re.compile(r"(?<![A-Za-z0-9_.])\d+(?![A-Za-z0-9_])")


def _nonblank(t: str) -> int:
    return sum(1 for c in t if not c.isspace())


def _module_of(path: str) -> str:
    """`Salt/Brun/M2.lean` -> `Salt.Brun.M2`; a bare `b.lean` -> `b`."""
    p = path[:-5] if path.endswith(".lean") else path
    return ".".join(x for x in p.split(os.sep) if x not in ("", "."))


def import_order(files: list[tuple[str, str]]) -> list[tuple[str, str]]:
    """Order a population so every file follows the population files it imports (path order breaks
    ties). A module name matches an import if one is a dotted suffix of the other, so a path given
    relative to the repo root or from inside it both resolve."""
    mods = [_module_of(f) for f, _ in files]

    def resolves(imp: str, mod: str) -> bool:
        return mod == imp or mod.endswith("." + imp) or imp.endswith("." + mod)

    deps = []
    for f, src in files:
        imps = re.findall(r"^import\s+(\S+)", src, flags=re.M)
        deps.append({j for j, m in enumerate(mods) for imp in imps if resolves(imp, m) and m != _module_of(f)})
    out, done = [], set()

    def visit(i, stack=()):
        if i in done or i in stack:
            return
        for j in sorted(deps[i]):
            visit(j, stack + (i,))
        done.add(i)
        out.append(files[i])

    for i in sorted(range(len(files)), key=lambda k: files[k][0]):
        visit(i)
    return out


def measure(files: list[tuple[str, str]]) -> dict:
    files = import_order(files)
    decls = []          # dict(kw, name, last, file, order, body, doc)
    prose_chars = formal_chars = 0
    automation = kernel_comp = 0
    num_tokens = big_numerals = 0
    order = 0
    for fname, src in files:
        code, spans = split_source(src)
        prose_chars += sum(_nonblank(t) for k, _, _, t in spans if k != "copyright")
        formal_chars += _nonblank(code)
        for m in AUTO_RE.finditer(code):
            automation += 1
            if m.group(1) in KERNEL_COMP:
                kernel_comp += 1
        for t in IDENT.findall(code) + NUM_RE.findall(code):
            num_tokens += 1
        big_numerals += sum(1 for t in NUM_RE.findall(code) if len(t) >= 3)
        starts = [(m.start(), m.end(), m.group(1), m.group(2)) for m in DECL_RE.finditer(code)]
        stops = [m.start() for m in STOP_RE.finditer(code)]
        docs = [(s, e, t) for k, s, e, t in spans if k == "doc"]
        for idx, (s, e, kw, name) in enumerate(starts):
            nxt = starts[idx + 1][0] if idx + 1 < len(starts) else len(code)
            nxt = min([nxt] + [p for p in stops if p > e])
            doc = None
            for ds, de, dt in docs:
                gap = src[de:s]
                if de <= s and re.fullmatch(r"\s*(?:@\[[^\]]*\]\s*)*", gap):
                    doc = dt
            decls.append({"kw": kw, "name": name, "last": name.split(".")[-1] if name else "",
                          "file": fname, "order": order, "body": code[e:nxt], "doc": doc})
            order += 1
    by_last: dict[str, list[int]] = {}
    for i, d in enumerate(decls):
        if d["last"]:
            by_last.setdefault(d["last"], []).append(i)

    def refs_of(text: str, self_i: int | None) -> set[int]:
        out = set()
        for t in IDENT.findall(text):
            for j in by_last.get(t.split(".")[-1], []):
                if j != self_i:
                    out.add(j)
        return out

    edges = [refs_of(d["body"], i) for i, d in enumerate(decls)]
    memo: dict[int, int] = {}
    onstack: set[int] = set()

    def chain(i: int) -> int:
        if i in memo:
            return memo[i]
        onstack.add(i)
        best = 0
        for j in edges[i]:
            if j not in onstack:
                best = max(best, chain(j))
        onstack.discard(i)
        memo[i] = best + 1
        return memo[i]

    depth = max((chain(i) for i in range(len(decls))), default=0)
    fan = [len(e) for e in edges]
    forward = 0
    for i, d in enumerate(decls):
        if not d["doc"]:
            continue
        named = set()
        for span in re.findall(r"`([^`]+)`", d["doc"]):
            named |= refs_of(span, i)
        forward += sum(1 for j in named if decls[j]["order"] > d["order"])
    thms = [d for d in decls if d["kw"] in THM_KW]
    defs = [d for d in decls if d["kw"] in DEF_KW]

    def share(xs):
        # None, not 0.0, on an empty population: 0 of 0 is no share at all, and a 0.0 here
        # would read as "nothing documented" for a file with no definitions (or no theorems).
        return round(sum(1 for d in xs if d["doc"]) / len(xs), 4) if xs else None

    return {"files": len(files), "decls": len(decls), "theorems": len(thms), "definitions": len(defs),
            "depth": depth, "fanout_max": max(fan, default=0),
            "fanout_mean": round(sum(fan) / len(fan), 3) if fan else 0.0,
            "prose_chars": prose_chars, "formal_chars": formal_chars,
            "prose_formal": round(prose_chars / formal_chars, 4) if formal_chars else 0.0,
            "defs_documented": share(defs), "forward_prose_refs": forward,
            "role_lines": share(thms), "automation": automation,
            "automation_per_decl": round(automation / len(decls), 3) if decls else 0.0,
            "kernel_comp": kernel_comp,
            "numeral_density": round(100 * big_numerals / num_tokens, 3) if num_tokens else 0.0}


# ───────────────────────────── selftest ─────────────────────────────

FIX_READABLE = '''/-
Copyright (c) 2026 Someone. All rights reserved.
-/
import Mathlib

/-!
# A readable fixture

We prove `top` from `mid`, which rests on `base`, after defining `sq`.
-/

/-- The square of a natural number. -/
def sq (n : Nat) : Nat := n * n

/-- `sq` is monotone: the base step. -/
theorem base (a b : Nat) (h : a ≤ b) : sq a ≤ sq b := Nat.mul_le_mul h h

/-- The middle step, from `base`. -/
theorem mid (a : Nat) : sq a ≤ sq (a + 1) := base a (a + 1) (Nat.le_succ a)

/-- The top result, from `mid` and `base`. -/
theorem top (a : Nat) : sq a ≤ sq (a + 2) :=
  Nat.le_trans (mid a) (base (a + 1) (a + 2) (Nat.le_succ _))
'''


def _strip_docstrings(src: str) -> str:
    return re.sub(r"/--.*?-/\n", "", src, flags=re.S)


def selftest() -> int:
    fails = []

    def check(name, cond, detail):
        print(("PASS " if cond else "FAIL ") + name + "  " + detail)
        if not cond:
            fails.append(name)

    base = measure([("r.lean", FIX_READABLE)])

    # population: derived from the fixture's own bytes
    n_decl = len(re.findall(r"^(?:theorem|def) ", FIX_READABLE, flags=re.M))
    check("decls-counted", base["decls"] == n_decl, f"{base['decls']} vs {n_decl} from the bytes")

    # depth: add one more link above top ⇒ depth grows by exactly one
    m = FIX_READABLE + '\n/-- One above. -/\ntheorem above (a : Nat) : sq a ≤ sq (a + 2) := top a\n'
    r = measure([("r.lean", m)])
    check("depth+1", r["depth"] == base["depth"] + 1 and base["depth"] > 0,
          f"{base['depth']} -> {r['depth']}")

    # fan-out: a declaration referencing all four earlier names ⇒ fan-out max >= 4
    m = FIX_READABLE + ('\n/-- All four. -/\ntheorem wide (a : Nat) : True := by\n'
                        '  have := sq a; have := base a a le_rfl; have := mid a; have := top a; trivial\n')
    r = measure([("r.lean", m)])
    check("fanout-max", r["fanout_max"] >= 4 and r["fanout_max"] > base["fanout_max"],
          f"{base['fanout_max']} -> {r['fanout_max']}")

    # role lines + prose: strip every declaration docstring ⇒ role 0, defs 0, prose falls
    r = measure([("r.lean", _strip_docstrings(FIX_READABLE))])
    check("role-lines", base["role_lines"] == 1.0 and r["role_lines"] == 0.0,
          f"{base['role_lines']} -> {r['role_lines']}")
    check("defs-documented", base["defs_documented"] == 1.0 and r["defs_documented"] == 0.0,
          f"{base['defs_documented']} -> {r['defs_documented']}")
    check("prose-falls", 0 < r["prose_formal"] < base["prose_formal"],
          f"{base['prose_formal']:.3f} -> {r['prose_formal']:.3f}")

    # copyright block is NOT prose: adding lines to it changes nothing
    m = FIX_READABLE.replace("All rights reserved.", "All rights reserved. " + "x" * 500)
    r = measure([("r.lean", m)])
    check("copyright-excluded", r["prose_chars"] == base["prose_chars"],
          f"{base['prose_chars']} vs {r['prose_chars']}")

    # forward prose ref: base's docstring names `top`, declared later ⇒ +1; the header does not count
    check("forward-zero", base["forward_prose_refs"] == 0, str(base["forward_prose_refs"]))
    m = FIX_READABLE.replace("the base step. -/", "the base step, used by `top`. -/")
    r = measure([("r.lean", m)])
    check("forward+1", r["forward_prose_refs"] == 1, str(r["forward_prose_refs"]))

    # hidden steps: replace a term proof by `by decide` ⇒ automation +1, kernel_comp +1
    m = FIX_READABLE.replace(":= Nat.mul_le_mul h h", ":= by decide")
    r = measure([("r.lean", m)])
    check("automation+1", r["automation"] == base["automation"] + 1, f"{base['automation']} -> {r['automation']}")
    check("kernel+1", r["kernel_comp"] == base["kernel_comp"] + 1, f"{base['kernel_comp']} -> {r['kernel_comp']}")
    # a tactic name inside a COMMENT or a docstring is not a step
    m = FIX_READABLE.replace("The middle step", "The middle step (no simp, no decide)")
    r = measure([("r.lean", m)])
    check("prose-tactic-ignored", r["automation"] == base["automation"], f"{r['automation']}")

    # numerals: a long literal raises density
    m = FIX_READABLE + '\n/-- Data. -/\ndef big : Nat := 123456789 + 987654321\n'
    r = measure([("r.lean", m)])
    check("numerals", r["numeral_density"] > base["numeral_density"],
          f"{base['numeral_density']:.2f} -> {r['numeral_density']:.2f}")

    # cross-file population: a reference into another file of the population is a link
    other = '/-- Uses top. -/\ntheorem far (a : Nat) : sq a ≤ sq (a + 2) := top a\n'
    r = measure([("r.lean", FIX_READABLE), ("s.lean", other)])
    check("cross-file-depth", r["depth"] == base["depth"] + 1, f"{base['depth']} -> {r['depth']}")

    # import order, not path order: b.lean is imported by a.lean, so `base` in a's prose is NOT forward
    fb = '/-- The base. -/\ntheorem base2 : True := trivial\n'
    fa = 'import b\n/-- From `base2`. -/\ntheorem top2 : True := base2\n'
    r = measure([("a.lean", fa), ("b.lean", fb)])
    check("import-order", r["forward_prose_refs"] == 0, str(r["forward_prose_refs"]))


    # ── nine arms added 2026-10-17 (O83 item 5a, a non-author's), each driven RED first against a mutant of
    #    the scanner that lacks the property (the matrix is in the record). An arm that RAISES is red.
    def arm(name, fn):
        try:
            cond, detail = fn()
        except BaseException as e:  # a RecursionError without the cycle guard IS the failure, not a skip
            cond, detail = False, f"RAISED {type(e).__name__}"
        check(name, cond, detail)

    # a declaration keyword at a LINE START inside a docstring is not a declaration
    def _prose_decl():
        m = FIX_READABLE.replace("/-- The middle step, from `base`. -/",
                                 "/-- The middle step, from `base`.\ntheorem fake : True := trivial\n-/")
        r = measure([("r.lean", m)])
        return (r["decls"] == base["decls"] and r["theorems"] == base["theorems"],
                f"decls {base['decls']} -> {r['decls']}")
    arm("prose-decl-ignored", _prose_decl)

    # ... nor inside a multi-line STRING LITERAL (the scanner counted this one until the literal's content
    # was blanked; the live population in salt was 0 declarations, measured)
    def _string_decl():
        m = FIX_READABLE + '\n/-- A string. -/\ndef s : String := "x\ntheorem ghost : True := trivial\n"\n'
        r = measure([("r.lean", m)])
        return (r["decls"] == base["decls"] + 1 and r["theorems"] == base["theorems"],
                f"decls {base['decls']} -> {r['decls']} (one for `s`), theorems {base['theorems']} -> {r['theorems']}")
    arm("string-decl-ignored", _string_decl)

    # an attribute and a modifier between the docstring and the keyword keep the role line
    def _attr_doc():
        m = FIX_READABLE.replace("/-- The top result, from `mid` and `base`. -/\ntheorem top",
                                 "/-- The top result, from `mid` and `base`. -/\n@[simp] private theorem top")
        r = measure([("r.lean", m)])
        return (r["theorems"] == base["theorems"] and r["role_lines"] == 1.0,
                f"theorems {r['theorems']} role {r['role_lines']}")
    arm("attr-modifier-doc-attached", _attr_doc)

    # an `example` is a declaration but not a theorem: role lines unmoved
    def _example():
        r = measure([("r.lean", FIX_READABLE + "\nexample : sq 2 = 4 := rfl\n")])
        return (r["decls"] == base["decls"] + 1 and r["theorems"] == base["theorems"]
                and r["role_lines"] == base["role_lines"],
                f"decls {r['decls']} theorems {r['theorems']} role {r['role_lines']}")
    arm("example-not-a-theorem", _example)

    # two-digit literals are not numerals (the >= 3-digit threshold)
    def _two_digit():
        r = measure([("r.lean", FIX_READABLE + "\n/-- Small. -/\ndef small : Nat := 12 + 99\n")])
        return (r["numeral_density"] == base["numeral_density"] == 0.0,
                f"{base['numeral_density']} -> {r['numeral_density']}")
    arm("two-digit-not-a-numeral", _two_digit)

    # fan-out counts DISTINCT references: `mid` twice and `sq` thrice is 2; the expected mean is derived
    def _fanout_distinct():
        m = FIX_READABLE + ("\n/-- Twice. -/\ntheorem twice (a : Nat) : sq a ≤ sq (a + 1) :=\n"
                            "  Nat.le_trans (mid a) (Nat.le_trans (mid a) (Nat.le_of_eq (congrArg sq rfl)))\n")
        r = measure([("r.lean", m)])
        n = base["decls"]
        expected = round((base["fanout_mean"] * n + 2) / (n + 1), 3)
        return r["fanout_mean"] == expected, f"mean {r['fanout_mean']} expected {expected}"
    arm("fanout-distinct", _fanout_distinct)

    # a reference cycle terminates with a finite depth
    def _cycle():
        r = measure([("c.lean", "theorem a1 : True := a2\ntheorem a2 : True := a1\n")])
        return r["depth"] >= 1, f"depth {r['depth']}"
    arm("cycle-terminates", _cycle)

    # a declaration's own name in its body is not a fan-out edge
    def _self_ref():
        r = measure([("d.lean", "def f : Nat → Nat\n  | 0 => 0\n  | n + 1 => f n\n")])
        return r["fanout_max"] == 0, f"fanout_max {r['fanout_max']}"
    arm("self-ref-not-an-edge", _self_ref)

    # a tactic name in a `--` line comment is not a hidden step
    def _line_comment():
        m = FIX_READABLE.replace("theorem top (a : Nat) : sq a ≤ sq (a + 2) :=",
                                 "theorem top (a : Nat) : sq a ≤ sq (a + 2) := -- no simp, no decide here")
        r = measure([("r.lean", m)])
        return (r["automation"] == base["automation"] and r["kernel_comp"] == base["kernel_comp"],
                f"automation {base['automation']} -> {r['automation']}")
    arm("line-comment-tactic-ignored", _line_comment)

    # an empty population has no share: 0 of 0 theorems is not "no role lines"
    def _empty_population():
        r1 = measure([("t.lean", "/-- Doc. -/\ntheorem t1 : True := trivial\n")])
        r2 = measure([("d.lean", "/-- Doc. -/\ndef d1 : Nat := 0\n")])
        return (r1["defs_documented"] is None and r2["role_lines"] is None
                and r1["role_lines"] == 1.0 and r2["defs_documented"] == 1.0,
                f"defs_documented(no defs) {r1['defs_documented']} · role_lines(no theorems) {r2['role_lines']}")
    arm("empty-population-is-none", _empty_population)

    print(f"selftest: {len(fails)} FAIL")
    return 1 if fails else 0


def collect(paths: list[str]) -> list[tuple[str, str]]:
    out = []
    for p in paths:
        if os.path.isdir(p):
            for root, _, fs in os.walk(p):
                for f in sorted(fs):
                    if f.endswith(".lean"):
                        q = os.path.join(root, f)
                        out.append((q, open(q, encoding="utf-8").read()))
        else:
            out.append((p, open(p, encoding="utf-8").read()))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("paths", nargs="*")
    ap.add_argument("--label", default=None)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if not a.paths:
        ap.error("give a path or --selftest")
    r = measure(collect(a.paths))
    r["label"] = a.label or " ".join(a.paths)
    if a.json:
        print(json.dumps(r, indent=1))
    else:
        for k, v in r.items():
            if v is None:
                print(f"  {k:22s} n/a (empty population)")
            else:
                print(f"  {k:22s} {v:.3f}" if isinstance(v, float) else f"  {k:22s} {v}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
