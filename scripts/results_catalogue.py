#!/usr/bin/env python3
"""THE RESULTS CATALOGUE, BY MACHINE (objective O13, item 1).

Reads every AUDITED name -- the arguments of `#audit_axioms` / `#print axioms` in the
ledgers `Salt/*/All.lean` -- resolves each to its declaration site, and classifies it:

  KIND (one per name), read off the STATEMENT by a binder walk, never off prose:
    infrastructure    non-Prop def/abbrev/structure/class/instance/inductive; plus
                      (HEURISTIC) a theorem whose conclusion is `=`/`↔` and whose proof
                      is rfl-shaped (`rfl`, `Iff.rfl`, `by rfl`, `by unfold/delta ...`)
    statement-only    a Prop-valued def/abbrev/structure/class/inductive: STATES, proves nothing
    conditional       a theorem/lemma with an explicit/instance binder (or a top-level
                      premise of its conclusion) whose TYPE's head symbol -- walked through
                      leading ∀ / → and through ∧ -- is a corpus-declared Prop-valued name
    unconditional     a theorem/lemma with no such binder
    unresolved        the audited name has no declaration site this parser can find

  OBJECT (one or more tags): from the declaration's PATH and from SYMBOLS in its statement,
  via the two data tables PATH_OBJECTS / SYMBOL_OBJECTS below (printed on the page).

Pure Python 3 stdlib. Source-level parse only -- NO Lean elaboration -- so every limit of
that is printed on the page beside the counts.

Usage (from anywhere):
  python3 scripts/results_catalogue.py              write docs/CATALOGUE.md
  python3 scripts/results_catalogue.py --stdout     print the page instead
  python3 scripts/results_catalogue.py --check      exit 1 if docs/CATALOGUE.md is stale
  python3 scripts/results_catalogue.py --self-test  run the fixtures and the per-arm mutants
"""
from __future__ import annotations

import hashlib
import os
import re
import subprocess
import sys
from collections import defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PAGE = os.path.join("docs", "CATALOGUE.md")
COMMAND = "python3 scripts/results_catalogue.py"

KINDS = ["unconditional", "conditional", "statement-only", "infrastructure", "unresolved"]
OBJECTS = ["zeros", "sieves", "characters", "entropy", "exponential sums", "other"]

# ---------------------------------------------------------------- the object map (DATA)
# A CHOICE, not a fact: printed verbatim in the page's LIMITS section.
# (path prefix or file-name substring) -> object tags. Prefix rules match the directory;
# the *substring* rules match the file's base name.
PATH_OBJECTS = [
    ("Salt/Entropy/", ["entropy"]),
    ("Salt/ExpSum/", ["exponential sums"]),
    ("Salt/Vk/", ["exponential sums", "zeros"]),
    ("Salt/Vmvt/", ["exponential sums"]),
    ("Salt/Weil/", ["exponential sums"]),
    ("Salt/Brun/", ["sieves"]),
    ("Salt/BrunLower/", ["sieves"]),
    ("Salt/Chen/", ["sieves"]),
    ("Salt/Maynard/", ["sieves"]),
    ("Salt/Parity/", ["sieves"]),
    ("Salt/LS/", ["sieves"]),
    ("Salt/BV/", ["sieves"]),
    ("Salt/SW/", ["sieves"]),
    ("Salt/Goldbach/", ["sieves"]),
    ("Salt/HardyLittlewood/", ["sieves"]),
    ("Salt/Twelve/", ["sieves"]),
    ("Salt/TwinBar/", ["sieves"]),
    ("Salt/Mertens/", ["sieves"]),
    ("Salt/HB/", ["characters"]),
    ("Salt/MR/", ["characters"]),
]
FILE_SUBSTRING_OBJECTS = [
    ("Zero", ["zeros"]), ("Zeta", ["zeros"]), ("ZFR", ["zeros"]), ("Littlewood", ["zeros"]),
    ("Sieve", ["sieves"]), ("Selberg", ["sieves"]),
    ("Char", ["characters"]), ("Dirichlet", ["characters"]), ("Liouville", ["characters"]),
    ("ExpSum", ["exponential sums"]), ("Weyl", ["exponential sums"]), ("VdC", ["exponential sums"]),
    ("Entropy", ["entropy"]),
]
# symbol (plain substring of the comment-stripped statement) -> object tags
SYMBOL_OBJECTS = [
    ("riemannZeta", ["zeros"]), ("LSeries", ["zeros"]), ("zeroFree", ["zeros"]),
    ("ZeroFree", ["zeros"]), ("zeroCount", ["zeros"]),
    ("DirichletCharacter", ["characters"]), ("MulChar", ["characters"]),
    ("legendreSym", ["characters"]), ("jacobiSym", ["characters"]),
    ("liouville", ["characters"]), ("moebius", ["characters"]), ("gaussSum", ["characters", "exponential sums"]),
    ("vonMangoldt", ["sieves"]), ("primeCounting", ["sieves"]), ("twinPrimeCounting", ["sieves"]),
    ("Sieve", ["sieves"]), ("sieve", ["sieves"]), ("Selberg", ["sieves"]),
    ("Complex.exp (2 * π * I", ["exponential sums"]), ("Complex.exp (2 * ↑π * I", ["exponential sums"]),
    ("Complex.exp (2 * Real.pi * Complex.I", ["exponential sums"]),
    ("AddChar", ["exponential sums"]), ("toCircle", ["exponential sums"]), ("fourier", ["exponential sums"]),
    ("expSum", ["exponential sums"]), ("ExpSum", ["exponential sums"]),
    ("entropy", ["entropy"]), ("Entropy", ["entropy"]), ("negMulLog", ["entropy"]), ("klFun", ["entropy"]),
]

DECL_KWS = ("theorem", "lemma", "def", "abbrev", "structure", "class", "instance", "inductive",
            "opaque", "irreducible_def")
MODIFIERS = ("private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "scoped", "local")
RELATIONS = ("=", "≠", "≤", "<", "≥", ">", "↔", "∣", "∈", "∉", "⊆", "⊂", "=O[", "=o[", "=ᶠ[", "≤ᶠ[", "~[")
MATHLIB_PROP_HEADS = {
    "Tendsto", "Filter.Tendsto", "Summable", "HasSum", "Continuous", "ContinuousOn", "ContinuousAt",
    "Differentiable", "DifferentiableAt", "DifferentiableOn", "HasDerivAt", "Integrable", "IntegrableOn",
    "IntervalIntegrable", "AnalyticAt", "Nat.Prime", "Prime", "Squarefree", "Asymptotics.IsBigO",
    "Asymptotics.IsLittleO", "IsBigO", "IsLittleO", "Monotone", "Antitone", "StrictMono", "MonotoneOn",
    "AntitoneOn", "MeasurableSet", "Measurable", "Set.Finite", "Set.Infinite", "Nonempty", "IsUnit", "Even",
    "Odd", "Nat.Coprime", "IsCoprime", "Irrational", "True", "False", "Filter.Eventually", "Filter.Frequently",
    "BddAbove", "BddBelow", "Disjoint", "Function.Injective", "Function.Surjective", "ContDiff", "ConvexOn",
    "ConcaveOn", "Fact", "Not", "Exists", "And", "Or", "Iff", "Eq", "Ne",
}

# ---------------------------------------------------------------- lexing helpers
IDENT_START = re.compile(r"[A-Za-z_À-ɏͰ-Ͽἀ-῿℀-⅏«]")
IDENT_RE = re.compile(r"(?:«[^»]*»|[A-Za-z_À-ɏͰ-Ͽἀ-῿℀-⅏]"
                      r"[A-Za-z0-9_'!?À-ɏͰ-Ͽἀ-῿₀-ₜᵢ-ᵪ℀-⅏]*)"
                      r"(?:\.(?:«[^»]*»|[A-Za-z_À-ɏͰ-Ͽἀ-῿℀-⅏]"
                      r"[A-Za-z0-9_'!?À-ɏͰ-Ͽἀ-῿₀-ₜᵢ-ᵪ℀-⅏]*))*")
KEYWORDS = {"theorem", "lemma", "def", "abbrev", "structure", "class", "instance", "inductive", "example",
            "namespace", "section", "end", "open", "variable", "import", "set_option", "noncomputable",
            "private", "protected", "attribute", "universe", "include", "omit", "mutual", "opaque", "axiom",
            "macro", "syntax", "elab", "notation", "infix", "infixl", "infixr", "prefix", "local", "scoped",
            "deriving", "export", "irreducible_def", "alias", "in", "where", "fun", "by", "at", "with",
            "public", "meta", "initialize"}
OPEN_BR = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
CLOSE_BR = set(OPEN_BR.values())


def strip_comments(src: str) -> str:
    """Blank out `--` line comments and nested `/- -/` blocks (docstrings included), and the
    contents of string literals, preserving every newline so line numbers survive."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1; out.append("  "); i += 2; continue
            if src.startswith("-/", i):
                depth -= 1; out.append("  "); i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if src.startswith("/-", i):
            depth = 1; out.append("  "); i += 2; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            seg = src[i:j + 1]
            out.append('"' + re.sub(r"[^\n]", " ", seg[1:-1]) + '"' if len(seg) >= 2 else seg)
            i = j + 1; continue
        if c == "'" and (i == 0 or not re.match(r"[\w'!?\u0080-￿]", src[i - 1])):
            m = re.match(r"'(?:\\.|[^\\'\n])'", src[i:])
            if m:
                out.append(" " * len(m.group(0))); i += len(m.group(0)); continue
        out.append(c); i += 1
    return "".join(out)


def split_top(s: str, sep: str) -> list[str]:
    """Split s at depth-0 occurrences of sep."""
    parts, depth, cur, i = [], 0, [], 0
    while i < len(s):
        ch = s[i]
        if ch in OPEN_BR:
            depth += 1
        elif ch in CLOSE_BR:
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            parts.append("".join(cur)); cur = []; i += len(sep); continue
        cur.append(ch); i += 1
    parts.append("".join(cur))
    return parts


def find_top(s: str, pred) -> int:
    """First depth-0 index i where pred(s, i) holds, else -1."""
    depth = 0
    for i, ch in enumerate(s):
        if ch in OPEN_BR:
            depth += 1; continue
        if ch in CLOSE_BR:
            depth -= 1; continue
        if depth == 0 and pred(s, i):
            return i
    return -1


def top_colon(s: str) -> int:
    return find_top(s, lambda t, i: t[i] == ":" and not t.startswith(":=", i)
                    and (i == 0 or t[i - 1] not in ":"))


def strip_parens(s: str) -> str:
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, ch in enumerate(s):
            if ch in OPEN_BR: depth += 1
            elif ch in CLOSE_BR: depth -= 1
            if depth == 0 and i < len(s) - 1:
                return s
        s = s[1:-1].strip()
    return s


# ---------------------------------------------------------------- statement parsing
def parse_binders(s: str):
    """Parse a leading run of bracketed binders. Returns (binders, rest) where each binder is
    (bracket, names, type)."""
    binders, i, s = [], 0, s
    while True:
        while i < len(s) and s[i].isspace():
            i += 1
        if i >= len(s) or s[i] not in OPEN_BR or s[i] == "⟨":
            return binders, s[i:]
        op, cl, depth, j = s[i], OPEN_BR[s[i]], 0, i
        while j < len(s):
            if s[j] in OPEN_BR: depth += 1
            elif s[j] in CLOSE_BR:
                depth -= 1
                if depth == 0: break
            j += 1
        inner = s[i + 1:j]
        k = top_colon(inner)
        if k >= 0:
            names = inner[:k].split()
            typ = inner[k + 1:]
            d = find_top(typ, lambda t, x: t.startswith(":=", x))
            if d >= 0: typ = typ[:d]
        else:
            names, typ = ([], inner) if op == "[" else (inner.split(), "")
        binders.append((op, names, typ.strip()))
        i = j + 1


def arrow_parts(t: str) -> list[str]:
    """Walk leading ∀-binders and → premises: return [premise..., conclusion]."""
    t = strip_parens(t)
    if t.startswith("∀") and not t.startswith("∀ᶠ"):
        c = find_top(t, lambda s, i: s[i] == ",")
        if c > 0:
            bnd = t[1:c]
            prem = []
            bs, _ = parse_binders(bnd.strip())
            for op, names, typ in bs:
                if typ: prem.append(typ)
            return prem + arrow_parts(t[c + 1:])
    parts = [p.strip() for p in split_top(t, "→")]
    if len(parts) > 1:
        return parts[:-1] + arrow_parts(parts[-1])
    return [t]


def heads(t: str) -> list[str]:
    """Head symbol(s) of a type, walking through ∀/→ to the conclusion and through ∧."""
    concl = strip_parens(arrow_parts(t)[-1])
    conj = split_top(concl, "∧")
    if len(conj) > 1:
        out = []
        for c in conj: out += heads(c)
        return out
    for rel in RELATIONS + ("∨", "¬", "∃"):
        if rel in ("¬", "∃"):
            if concl.startswith(rel): return [{"¬": "Not", "∃": "Exists"}[rel]]
        elif find_top(concl, lambda s, i, r=rel: s.startswith(r, i)) >= 0:
            return [rel]
    s = concl.lstrip("@").strip()
    m = IDENT_RE.match(s)
    return [m.group(0)] if m else []


class Scope:
    def __init__(self, kind, name, parts):
        self.kind, self.name, self.parts = kind, name, parts
        self.opens: list[str] = []
        self.vars: list = []
        self.includes: set[str] = set()


class Decl:
    def __init__(self, **kw): self.__dict__.update(kw)


def ns_of(stack):
    return [p for sc in stack for p in sc.parts]


def statement_end(text: str, start: int) -> int:
    """Index where the declaration's statement ends: depth-0 `:=`, ` where`, `|` at the
    start of a line, or the next column-0 command line."""
    depth, i, n = 0, start, len(text)
    while i < n:
        ch = text[i]
        if ch in OPEN_BR: depth += 1
        elif ch in CLOSE_BR: depth -= 1
        elif depth <= 0:
            if text.startswith(":=", i): return i
            if text.startswith("where", i) and not re.match(r"[\w']", text[i - 1]) \
                    and not re.match(r"[\w']", text[i + 5:i + 6] or " "): return i
            if ch == "|" and text[text.rfind("\n", 0, i) + 1:i].strip() == "": return i
            if ch == "\n" and i + 1 < n and text[i + 1] not in " \t\n" and i > start + 1:
                nxt = IDENT_RE.match(text, i + 1)
                if (nxt and nxt.group(0) in KEYWORDS) or text[i + 1] in "@#":
                    return i
        i += 1
    return n


def body_after(text: str, stop: int, limit: int = 400) -> str:
    """The first stretch of the proof/body after `:=` (for the rfl heuristic)."""
    if not text.startswith(":=", stop): return ""
    b = text[stop + 2:stop + 2 + limit]
    m = re.search(r"\n(?=\S)", b)
    return (b[:m.start()] if m else b).strip()


DECL_RE = re.compile(r"^[ \t]*((?:@\[[^\]\n]*\]\s*)*)((?:(?:%s)\s+)*)(%s)\b" %
                     ("|".join(MODIFIERS), "|".join(DECL_KWS)), re.M)


def index_file(path: str, raw: str, decls: dict, opens_by_file: dict):
    text = strip_comments(raw)
    stack: list[Scope] = [Scope("file", "", [])]
    line_starts = [0] + [m.end() for m in re.finditer("\n", text)]
    # command-level scope tracking, line by line, with declarations spliced in
    decl_iter = {m.start(3): m for m in DECL_RE.finditer(text)}
    lines = text.split("\n")
    pos = 0
    for lineno, line in enumerate(lines, 1):
        st = line.strip()
        if line[:1] not in (" ", "\t"):
            m = re.match(r"(?:noncomputable\s+|public\s+|@\[[^\]]*\]\s*)*section\b\s*(\S*)", st)
            if st.startswith("namespace "):
                name = st.split()[1]
                stack.append(Scope("namespace", name, name.split(".")))
            elif m:
                stack.append(Scope("section", m.group(1), []))
            elif st == "mutual":
                stack.append(Scope("mutual", "", []))
            elif re.match(r"end\b", st) and len(stack) > 1:
                stack.pop()
            elif re.match(r"open\b", st) and not re.search(r"\bin\s*$", st):
                toks = st[4:].split()
                for t in toks:
                    if t == "scoped": continue
                    if t.startswith("(") or t in ("hiding", "renaming", "in"): break
                    if IDENT_RE.fullmatch(t): stack[-1].opens.append(t)
            elif re.match(r"variable\b", st):
                seg = text[pos + line.find("variable") + len("variable"):]
                e = statement_end(seg, 0)
                bs, _ = parse_binders(seg[:e])
                stack[-1].vars.extend(bs)
            elif re.match(r"include\b", st):
                stack[-1].includes.update(st.split()[1:])
        # declarations starting on this line
        for off in range(len(line)):
            m = decl_iter.get(pos + off)
            if m is None: continue
            kw = m.group(3)
            after = text[m.end(3):]
            mname = re.match(r"\s+(\([^)]*\)\s*)?(" + IDENT_RE.pattern + ")", after)
            if not mname or (kw == "instance" and mname.group(2) in (":",)):
                continue
            short = mname.group(2)
            if short in KEYWORDS: continue
            head_start = m.end(3) + mname.end(0)
            head_start += len(re.match(r"\.\{[^}]*\}", text[head_start:]).group(0)) \
                if re.match(r"\.\{[^}]*\}", text[head_start:]) else 0
            stop = statement_end(text, head_start)
            stmt = text[head_start:stop]
            ns = ns_of(stack)
            full = short[len("_root_."):] if short.startswith("_root_.") else ".".join(ns + [short])
            opens = [o for sc in stack for o in sc.opens]
            vars_ = [b for sc in stack for b in sc.vars]
            incl = set().union(*[sc.includes for sc in stack])
            d = Decl(name=full, short=short, kw=kw, path=path, line=lineno, stmt=stmt,
                     body=body_after(text, stop), ns=ns, opens=opens, vars=vars_, includes=incl,
                     attrs=m.group(1) or "", text_tail=text[stop:stop + 4000])
            decls.setdefault(full, d)
        pos += len(line) + 1
    opens_by_file[path] = None


# ---------------------------------------------------------------- classification
def resolve(ident: str, ns: list[str], opens: list[str], universe) -> str | None:
    ident = ident.lstrip("@")
    if ident.startswith("_root_."): ident = ident[7:]
    cands = []
    for k in range(len(ns), -1, -1):
        cands.append(".".join(ns[:k] + [ident]))
    for o in opens:
        for k in range(len(ns), -1, -1):
            cands.append(".".join(ns[:k] + [o, ident]))
    for c in cands:
        if c in universe: return c
    return None


def split_decl(d):
    """(binders, conclusion-type or None)."""
    bs, rest = parse_binders(d.stmt)
    rest = rest.strip()
    if rest.startswith(":"):
        return bs, rest[1:].strip()
    k = top_colon(rest)
    return bs, (rest[k + 1:].strip() if k >= 0 else None)


def structure_fields(d) -> list[str]:
    t = d.text_tail
    if not t.startswith("where"): return []
    lines = t[5:].split("\n")
    fields, cur, ind = [], None, None
    for ln in lines[1:] if lines and not lines[0].strip() else lines:
        if ln.strip() == "":
            continue
        if ln[:1] not in (" ", "\t"): break
        li = len(ln) - len(ln.lstrip())
        if ind is None: ind = li
        if li == ind and re.match(r"\s*[\w'.«»]+\s*(\(|\{|\[|⦃|:[^=])", ln) and "::" not in ln:
            if cur is not None: fields.append(cur)
            cur = ln
        elif li == ind and "::" in ln:
            continue
        elif cur is not None:
            cur += " " + ln
    if cur is not None: fields.append(cur)
    out = []
    for f in fields:
        bs, rest = parse_binders(f.strip().split(None, 1)[1] if len(f.split()) > 1 else "")
        rest = rest.strip()
        if rest.startswith(":"):
            typ = rest[1:]
            e = find_top(typ, lambda s, i: s.startswith(":=", i))
            out.append(typ[:e] if e >= 0 else typ)
    return out


def prop_shaped(typ: str, ns, opens, propdefs) -> bool:
    for h in heads(typ):
        if h in RELATIONS or h in ("∨", "Not", "Exists") or h in MATHLIB_PROP_HEADS:
            return True
        if resolve(h, ns, opens, propdefs): return True
    return False


def build_propdefs(decls: dict) -> set[str]:
    """Every corpus-declared Prop-valued name (whole tree, not only the audited ones)."""
    props: set[str] = set()
    for _ in range(3):  # fixpoint for structures of Props / defs of Prop-defs
        for name, d in decls.items():
            if name in props or d.kw in ("theorem", "lemma", "instance"): continue
            bs, concl = split_decl(d)
            if concl is not None:
                final = strip_parens(arrow_parts(concl)[-1])
                if final == "Prop" or re.fullmatch(r"Prop\s*", final):
                    props.add(name); continue
            if d.kw in ("structure", "class") and concl is None:
                fs = structure_fields(d)
                if fs and all(prop_shaped(f, d.ns, d.opens, props) for f in fs):
                    props.add(name); continue
            if d.kw in ("def", "abbrev") and concl is None:
                b = d.body
                if b.startswith(("∀", "∃")) or (b and prop_shaped(b.split("\n")[0], d.ns, d.opens, props)
                                                  and not b.startswith(("fun", "λ", "by", "⟨", "{"))):
                    props.add(name)
    return props


RFL_RE = re.compile(r"^(rfl|Iff\.rfl|Eq\.refl\b.*|by\s+(rfl|unfold\b.*|delta\b.*|exact\s+rfl|exact\s+Iff\.rfl))\s*$",
                    re.S)


def classify(d, propdefs):
    """Returns (kind, hypothesis-name list, statement text used)."""
    bs, concl = split_decl(d)
    if d.kw in ("def", "abbrev", "structure", "class", "inductive", "opaque", "irreducible_def"):
        if d.name in propdefs: return "statement-only", []
        if d.kw in ("def", "abbrev", "opaque", "irreducible_def") and concl is not None \
                and prop_shaped(concl, d.ns, d.opens, propdefs) \
                and strip_parens(arrow_parts(concl)[-1]) != "Prop":
            pass  # a def whose TYPE is a proposition proves something: treated as a theorem
        else:
            return "infrastructure", []
    if d.kw == "instance" and not (concl and prop_shaped(concl, d.ns, d.opens, propdefs)):
        return "infrastructure", []
    if concl is not None and d.kw in ("theorem", "lemma"):
        final = strip_parens(arrow_parts(concl)[-1])
        if (find_top(final, lambda s, i: s.startswith("↔", i)) >= 0
                or find_top(final, lambda s, i: s[i] == "=" and s[i - 1:i] not in ("≠", "≤", "≥", ":", "=")
                            and s[i + 1:i + 2] not in ("O", "o", "ᶠ", "=")) >= 0) \
                and RFL_RE.match(d.body or ""):
            return "infrastructure", []
    # the binder walk
    stmt_tokens = set(IDENT_RE.findall(d.stmt))
    used_vars = [b for b in d.vars
                 if (b[0] == "(" or b[0] == "[") and b[1] and
                 any(n in stmt_tokens or n in d.includes for n in b[1])]
    types = [typ for op, names, typ in used_vars + bs if op in ("(", "[") and typ]
    if concl is not None:
        types += arrow_parts(concl)[:-1]
    hyps = []
    for t in types:
        for h in heads(t):
            r = resolve(h, d.ns, d.opens, propdefs)
            if r and r not in hyps: hyps.append(r)
    return ("conditional" if hyps else "unconditional"), hyps


def objects_for(path: str, stmt: str) -> list[str]:
    tags = set()
    for pre, ts in PATH_OBJECTS:
        if path.startswith(pre): tags.update(ts)
    base = os.path.basename(path)
    for sub, ts in FILE_SUBSTRING_OBJECTS:
        if sub in base: tags.update(ts)
    for sym, ts in SYMBOL_OBJECTS:
        if sym in stmt: tags.update(ts)
    return [o for o in OBJECTS if o in tags] or ["other"]


# ---------------------------------------------------------------- the ledgers
AUDIT_RE = re.compile(r"#audit_axioms\b|#print\s+axioms\b")


def parse_ledger(raw: str):
    """Audited names, with the ledger's namespace/open context at each command.
    Returns list of (name, line, ns, opens)."""
    text = strip_comments(raw)
    out = []
    stack = [Scope("file", "", [])]
    lines = text.split("\n")
    offsets = [0]
    for ln in lines: offsets.append(offsets[-1] + len(ln) + 1)
    events = []
    for i, ln in enumerate(lines):
        st = ln.strip()
        if ln[:1] in (" ", "\t"): continue
        if st.startswith("namespace "): events.append((offsets[i], "ns", st.split()[1]))
        elif re.match(r"(?:noncomputable\s+)?section\b", st): events.append((offsets[i], "sec", ""))
        elif re.match(r"end\b", st): events.append((offsets[i], "end", ""))
        elif re.match(r"open\b", st) and not re.search(r"\bin\s*$", st):
            events.append((offsets[i], "open", st[4:]))
    for m in AUDIT_RE.finditer(text):
        events.append((m.start(), "audit", m))
    events.sort(key=lambda e: e[0])
    for pos, kind, arg in events:
        if kind == "ns": stack.append(Scope("namespace", arg, arg.split(".")))
        elif kind == "sec": stack.append(Scope("section", "", []))
        elif kind == "end" and len(stack) > 1: stack.pop()
        elif kind == "open":
            for t in arg.split():
                if t == "scoped": continue
                if t.startswith("(") or t in ("hiding", "renaming"): break
                stack[-1].opens.append(t)
        elif kind == "audit":
            j = arg.end()
            while True:
                mm = re.compile(r"\s*(" + IDENT_RE.pattern + r")").match(text, j)
                if not mm or mm.group(1) in KEYWORDS: break
                # a token at column 0 that is not indented continuation is still part of ident+
                out.append((mm.group(1), text.count("\n", 0, mm.start(1)) + 1, ns_of(stack),
                            [o for sc in stack for o in sc.opens]))
                j = mm.end()
    return out


# ---------------------------------------------------------------- the build
def git(*args):
    return subprocess.run(["git", "-C", REPO] + list(args), capture_output=True, text=True).stdout.strip()


def build(files: dict[str, str], ledgers: list[str]):
    decls: dict = {}
    for p in sorted(files):
        index_file(p, files[p], decls, {})
    propdefs = build_propdefs(decls)
    audited = {}  # name -> (first ledger, line) ; plus ledgers list
    raw_count, per_ledger = 0, {}
    unresolved_ctx = {}
    for lp in ledgers:
        entries = parse_ledger(files[lp])
        per_ledger[lp] = len(entries)
        raw_count += len(entries)
        for ident, ln, ns, opens in entries:
            full = resolve(ident, ns, opens, decls)
            key = full or ident
            if key not in audited:
                audited[key] = {"ledgers": [], "resolved": full is not None}
            if lp not in audited[key]["ledgers"]:
                audited[key]["ledgers"].append(lp)
            if full is None: unresolved_ctx[key] = (lp, ln)
    rows = []
    for name in sorted(audited):
        a = audited[name]
        if not a["resolved"]:
            lp, ln = unresolved_ctx[name]
            rows.append(dict(name=name, kind="unresolved", path=lp, line=ln, hyps=[],
                             objects=objects_for(lp, "")))
            continue
        d = decls[name]
        kind, hyps = classify(d, propdefs)
        rows.append(dict(name=name, kind=kind, path=d.path, line=d.line, hyps=hyps,
                         objects=objects_for(d.path, d.stmt)))
    receipt = dict(ledgers=len(ledgers), with_commands=sum(1 for v in per_ledger.values() if v),
                   parsed=raw_count, distinct=len(audited),
                   resolved=sum(1 for r in rows if r["kind"] != "unresolved"),
                   unresolved=sum(1 for r in rows if r["kind"] == "unresolved"),
                   dup=sum(1 for a in audited.values() if len(a["ledgers"]) > 1),
                   repeats=raw_count - len(audited),
                   decls=len(decls), propdefs=len(propdefs))
    return rows, receipt


def md_escape(s: str) -> str:
    return s.replace("|", "\\|")


def render(rows, receipt, base_sha: str, digest: str) -> str:
    L = []
    L.append("# THE RESULTS CATALOGUE — by machine (O13 item 1)")
    L.append("")
    L.append("> **GENERATED — do not edit by hand.** Regenerate: `%s` · staleness gate: `%s --check`." % (COMMAND, COMMAND))
    L.append("> Base: last commit touching `Salt/` = `%s` · source digest `%s` (sha256 over every `Salt/**/*.lean`, "
             "sorted by path)." % (base_sha, digest))
    L.append("")
    L.append("## Population receipt")
    L.append("")
    L.append("| ledgers read | ledgers with audit commands | names parsed | distinct names | resolved | unresolved "
             "| audited in 2+ ledgers | repeat mentions folded |")
    L.append("|---|---|---|---|---|---|---|---|")
    r = receipt
    L.append("| %d | %d | %d | %d | %d | %d | %d | %d |" % (r["ledgers"], r["with_commands"], r["parsed"], r["distinct"],
             r["resolved"], r["unresolved"], r["dup"], r["repeats"]))
    L.append("")
    L.append("Declarations indexed across the tree: %d · corpus Prop-valued names (the hypothesis universe): %d."
             % (r["decls"], r["propdefs"]))
    L.append("")
    L.append("## KIND × OBJECT (counts; a name with several objects counts once in each object column)")
    L.append("")
    L.append("| kind | total | " + " | ".join(OBJECTS) + " |")
    L.append("|---|---|" + "---|" * len(OBJECTS))
    for k in KINDS:
        ks = [x for x in rows if x["kind"] == k]
        L.append("| %s | %d | " % (k, len(ks)) + " | ".join(str(sum(1 for x in ks if o in x["objects"])) for o in OBJECTS) + " |")
    L.append("| **all** | %d | " % len(rows) + " | ".join(str(sum(1 for x in rows if o in x["objects"])) for o in OBJECTS) + " |")
    L.append("")
    L.append("## LIMITS — read these beside every count above")
    L.append("")
    L.append("- **Source-level parse, no elaboration.** Names, binders and types are read from comment-stripped "
             "source text. Anything produced by macros, `alias`, `to_additive`, `@[simps]`, or elaboration-time "
             "notation is invisible; section `variable`s are attached only when their name occurs in the statement "
             "or is `include`d; implicit `{}`/`⦃⦄` binders are NOT walked.")
    L.append("- **Unresolved: %d.** A name the parser cannot find a declaration site for is listed in its own "
             "section, never dropped. Unresolved ≠ absent from Lean." % r["unresolved"])
    L.append("- **The conditional test** is the binder's HEAD SYMBOL (walked through leading `∀`/`→` and through `∧`) "
             "resolved against the corpus Prop-valued set; premises `A → …` at the top of the conclusion count as "
             "binders. A hypothesis whose head is a mathlib or infix Prop (`2 ≤ x`, `Tendsto …`, `Squarefree P`) "
             "does not make a result conditional. The Prop-valued set is itself heuristic: `: Prop` / `: … → Prop` "
             "ascriptions, structures/classes all of whose fields look Prop-shaped, and untyped defs whose body is "
             "`∀`/`∃`/relational.")
    L.append("- **Mixed data+Prop bundles are DATA.** A corpus structure carrying both data and Prop fields "
             "(e.g. `ChowlaRegime`, `HBForms`, `TruncSieve`) is not Prop-valued, so a binder of that type does "
             "NOT make a result conditional — the constraints inside a regime bundle are invisible to this column.")
    L.append("- **The infrastructure split for theorems is a HEURISTIC:** a theorem/lemma whose conclusion is `=`/`↔` "
             "and whose proof is `rfl`, `Iff.rfl`, `Eq.refl …`, `by rfl`, `by unfold …`, `by delta …` or `by exact rfl`. "
             "Every other identity lemma is classed by its binders.")
    L.append("- **A `def` whose type is a proposition** (not `Prop` itself) is classed as a theorem, by its binders.")
    L.append("- **The object map is a CHOICE**, reproduced verbatim below. `characters` includes multiplicative "
             "twists (`liouville`, `moebius`); symbol tags are plain substrings of the statement.")
    L.append("")
    L.append("<details><summary>Object map (data in the script)</summary>")
    L.append("")
    L.append("| rule | matches | objects |")
    L.append("|---|---|---|")
    for pre, ts in PATH_OBJECTS: L.append("| path prefix | `%s` | %s |" % (pre, ", ".join(ts)))
    for sub, ts in FILE_SUBSTRING_OBJECTS: L.append("| file-name substring | `%s` | %s |" % (sub, ", ".join(ts)))
    for sym, ts in SYMBOL_OBJECTS: L.append("| statement symbol | `%s` | %s |" % (md_escape(sym), ", ".join(ts)))
    L.append("| (none matched) | | other |")
    L.append("")
    L.append("</details>")
    L.append("")
    hyp_count = defaultdict(list)
    for x in rows:
        for h in x["hyps"]: hyp_count[h].append(x["name"])
    L.append("## Named hypotheses — how many conditional results hang on each (the O2 payoff table)")
    L.append("")
    L.append("| hypothesis | conditional results |")
    L.append("|---|---|")
    for h, ns in sorted(hyp_count.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        L.append("| `%s` | %d |" % (h, len(ns)))
    L.append("")
    for k in KINDS:
        ks = sorted((x for x in rows if x["kind"] == k), key=lambda x: (x["path"], x["line"], x["name"]))
        L.append("## %s (%d)" % (k, len(ks)))
        L.append("")
        if not ks:
            L.append("(none)"); L.append(""); continue
        if k == "conditional":
            L.append("| name | file:line | objects | hypotheses |"); L.append("|---|---|---|---|")
        else:
            L.append("| name | file:line | objects |"); L.append("|---|---|---|")
        for x in ks:
            loc = "%s:%d" % (x["path"], x["line"])
            if k == "unresolved": loc = "(audited at) " + loc
            row = "| `%s` | %s | %s |" % (md_escape(x["name"]), loc, ", ".join(x["objects"]))
            if k == "conditional": row += " %s |" % ", ".join("`%s`" % h for h in x["hyps"])
            L.append(row)
        L.append("")
    return "\n".join(L) + "\n"


def load_repo():
    paths = [p for p in git("ls-files").split("\n") if p.startswith("Salt/") and p.endswith(".lean")]
    files = {}
    h = hashlib.sha256()
    for p in sorted(paths):
        with open(os.path.join(REPO, p), "rb") as f:
            b = f.read()
        h.update(p.encode() + b"\0" + b)
        files[p] = b.decode("utf-8", "replace")
    ledgers = sorted(p for p in paths if re.search(r"(^|/)All\.lean$", p))
    return files, ledgers, h.hexdigest()[:16]


def generate():
    files, ledgers, digest = load_repo()
    rows, receipt = build(files, ledgers)
    base = git("log", "-1", "--format=%h", "--", "Salt") or "unknown"
    return render(rows, receipt, base, digest), rows, receipt


# ---------------------------------------------------------------- self-test
FIXTURE = {
    "Salt/Fx/Defs.lean": '''
namespace Salt.Fx
/-- a hypothesis: `SWHyp` states, proves nothing. -/
def SWHyp (q : ℕ) : Prop := ∀ a, a ≤ q
abbrev PairHyp : ℕ → ℕ → Prop := fun a b => a < b
structure Bundle where
  h1 : 1 ≤ 2
  h2 : SWHyp 3
structure Data where
  x : ℕ
  y : ℝ
def weight (n : ℕ) : ℝ := n
theorem weight_eq (n : ℕ) : weight n = n := rfl
end Salt.Fx
''',
    "Salt/Fx/Main.lean": '''
import Salt.Fx.Defs
namespace Salt.Fx
open Real
-- theorem fake_decl (h : SWHyp 1) : True  -- a comment must not be read
theorem cond_simple (h : SWHyp 5) (x : ℕ) (hx : 2 ≤ x) : x ≤ x := le_rfl
theorem cond_forall (hSW : ∀ q, 1 ≤ q → SWHyp q) : True := trivial
theorem cond_bundle [Bundle] : True := trivial
theorem uncond_named (hSW : 2 ≤ 3) (hzeta : Tendsto f atTop atTop) : True := trivial
theorem cond_premise : PairHyp 1 2 → True := fun _ => trivial
theorem uncond_plain (x : ℕ) : x + 0 = x := by simp
/-- docstring naming SWHyp must not matter -/
theorem ident_rfl (n : ℕ) : weight n = (n : ℝ) := rfl
end Salt.Fx
''',
    "Salt/Fx/All.lean": '''
import Salt.Fx.Main
/-! `#audit_axioms Salt.Fx.ghost` inside a doc comment is not a command -/
#audit_axioms Salt.Fx.SWHyp Salt.Fx.PairHyp
  Salt.Fx.Bundle Salt.Fx.Data
  Salt.Fx.weight
#audit_axioms Salt.Fx.cond_simple
#audit_axioms Salt.Fx.cond_forall Salt.Fx.cond_bundle Salt.Fx.cond_premise
#audit_axioms Salt.Fx.uncond_named Salt.Fx.uncond_plain Salt.Fx.ident_rfl
#audit_axioms Salt.Fx.weight_eq Salt.Fx.missing_name
namespace Salt.Fx
#print axioms cond_simple
end Salt.Fx
''',
}
EXPECT = {
    "Salt.Fx.SWHyp": "statement-only", "Salt.Fx.PairHyp": "statement-only", "Salt.Fx.Bundle": "statement-only",
    "Salt.Fx.Data": "infrastructure", "Salt.Fx.weight": "infrastructure", "Salt.Fx.weight_eq": "infrastructure",
    "Salt.Fx.ident_rfl": "infrastructure",
    "Salt.Fx.cond_simple": "conditional", "Salt.Fx.cond_forall": "conditional",
    "Salt.Fx.cond_bundle": "conditional", "Salt.Fx.cond_premise": "conditional",
    "Salt.Fx.uncond_named": "unconditional", "Salt.Fx.uncond_plain": "unconditional",
    "Salt.Fx.missing_name": "unresolved",
}
EXPECT_HYPS = {"Salt.Fx.cond_simple": ["Salt.Fx.SWHyp"], "Salt.Fx.cond_forall": ["Salt.Fx.SWHyp"],
               "Salt.Fx.cond_bundle": ["Salt.Fx.Bundle"], "Salt.Fx.cond_premise": ["Salt.Fx.PairHyp"]}


def check_fixture(fx) -> list[str]:
    ledgers = sorted(p for p in fx if p.endswith("All.lean"))
    rows, rc = build(fx, ledgers)
    got = {r["name"]: r for r in rows}
    errs = []
    for n, k in EXPECT.items():
        if n not in got: errs.append("missing %s" % n); continue
        if got[n]["kind"] != k: errs.append("%s: kind %s, want %s" % (n, got[n]["kind"], k))
    for n, hs in EXPECT_HYPS.items():
        if n in got and got[n]["hyps"] != hs: errs.append("%s: hyps %s, want %s" % (n, got[n]["hyps"], hs))
    extra = set(got) - set(EXPECT)
    if extra: errs.append("unexpected names %s" % sorted(extra))
    if rc["parsed"] != 15 or rc["distinct"] != 14 or rc["repeats"] != 1:
        errs.append("receipt %s" % {k: rc[k] for k in ("parsed", "distinct", "repeats")})
    if got.get("Salt.Fx.cond_simple", {}).get("line") != 6: errs.append("cond_simple line %s" %
                                                                         got.get("Salt.Fx.cond_simple", {}).get("line"))
    return errs


# one mutant per arm: each must make the fixture check FAIL (the arm is shown able to fail)
MUTANTS = [
    ("statement-only arm: SWHyp's `: Prop` removed", "Salt/Fx/Defs.lean",
     "def SWHyp (q : ℕ) : Prop := ∀ a, a ≤ q", "def SWHyp (q : ℕ) : ℕ := q"),
    ("statement-only arm (structure of Props): Bundle gains a data field", "Salt/Fx/Defs.lean",
     "  h2 : SWHyp 3\n", "  h2 : SWHyp 3\n  n : ℕ\n"),
    ("infrastructure arm: Data gains `: Prop`", "Salt/Fx/Defs.lean", "structure Data where",
     "structure Data : Prop where"),
    ("infrastructure heuristic: ident_rfl proof no longer rfl", "Salt/Fx/Main.lean",
     "(n : ℝ) := rfl", "(n : ℝ) := by simp [weight]"),
    ("conditional arm: cond_simple binder head becomes infix", "Salt/Fx/Main.lean",
     "(h : SWHyp 5)", "(h : 5 ≤ 6)"),
    ("conditional arm (∀/→ walk): cond_forall head replaced", "Salt/Fx/Main.lean",
     "1 ≤ q → SWHyp q", "1 ≤ q → q ≤ q"),
    ("conditional arm (premise): cond_premise premise dropped", "Salt/Fx/Main.lean",
     "PairHyp 1 2 → True := fun _ => trivial", "True := trivial"),
    ("unconditional arm: uncond_named gains a corpus hypothesis", "Salt/Fx/Main.lean",
     "(hSW : 2 ≤ 3)", "(hSW : SWHyp 3)"),
    ("unresolved arm: missing_name gets a declaration", "Salt/Fx/Main.lean",
     "end Salt.Fx", "theorem missing_name : True := trivial\nend Salt.Fx"),
    ("comment stripping: the commented decl is un-commented", "Salt/Fx/Main.lean",
     "-- theorem fake_decl (h : SWHyp 1) : True  -- a comment must not be read",
     "theorem uncond_plain (h : SWHyp 1) : True := trivial"),
    ("ledger parse: continuation line dropped", "Salt/Fx/All.lean", "  Salt.Fx.weight\n", "\n"),
    ("ledger parse: doc-comment audit un-commented", "Salt/Fx/All.lean",
     "/-! `#audit_axioms Salt.Fx.ghost` inside a doc comment is not a command -/",
     "#audit_axioms Salt.Fx.ghost"),
]


def self_test() -> int:
    errs = check_fixture(dict(FIXTURE))
    if errs:
        print("SELF-TEST FAIL (clean fixture):"); [print("  " + e) for e in errs]; return 1
    print("clean fixture: %d names, every KIND arm landed as expected" % len(EXPECT))
    killed = 0
    for label, f, old, new in MUTANTS:
        fx = dict(FIXTURE)
        assert old in fx[f], "mutant anchor missing: " + label
        fx[f] = fx[f].replace(old, new, 1)
        e = check_fixture(fx)
        status = "KILLED" if e else "SURVIVED"
        killed += bool(e)
        print("  mutant %-62s %s%s" % (label[:62], status, (" (" + e[0][:60] + ")") if e else ""))
    # object arm
    oerrs = []
    if objects_for("Salt/Entropy/X.lean", "") != ["entropy"]: oerrs.append("path entropy")
    if "zeros" not in objects_for("Salt/Fx/X.lean", "riemannZeta s = 0"): oerrs.append("symbol zeros")
    if objects_for("Salt/Fx/X.lean", "x ≤ y") != ["other"]: oerrs.append("fallback other")
    if "zeros" in objects_for("Salt/Fx/X.lean", "x ≤ y"): oerrs.append("object mutant: zeros from nothing")
    print("object arm: %s" % ("ok" if not oerrs else oerrs))
    print("mutants killed: %d / %d" % (killed, len(MUTANTS)))
    return 0 if killed == len(MUTANTS) and not oerrs else 1


def main(argv):
    if "--self-test" in argv: return self_test()
    page, rows, rc = generate()
    if "--check" in argv:
        try:
            cur = open(os.path.join(REPO, PAGE), encoding="utf-8").read()
        except OSError:
            cur = None
        if cur != page:
            print("STALE: %s differs from a fresh generation (%d names); run `%s`" % (PAGE, len(rows), COMMAND))
            return 1
        print("OK: %s is current (%d names)" % (PAGE, len(rows)))
        return 0
    if "--stdout" in argv:
        sys.stdout.write(page); return 0
    with open(os.path.join(REPO, PAGE), "w", encoding="utf-8") as f:
        f.write(page)
    print("wrote %s: %s" % (PAGE, " · ".join("%s %s" % (k, v) for k, v in rc.items())))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
