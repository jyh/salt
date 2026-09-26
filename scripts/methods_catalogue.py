#!/usr/bin/env python3
"""THE METHODS CATALOGUE + HYPOTHESIS STATUS, BY MACHINE (objective O13, item 2).

Built ON TOP of item 1 (`scripts/results_catalogue.py`): its parser, name index, binder walk,
Prop-valued set and KIND classifier are IMPORTED, never forked.

DELIVERABLE A -- HYPOTHESIS STATUS. For every corpus Prop-valued name P (item 1's set):
  DISCHARGED  some declaration anywhere in `Salt/` whose item-1 KIND is `unconditional` has a
              conclusion whose HEAD SYMBOL is P -- after walking leading ∀/→ and ONE level of
              top-level ∧ (`P`, `P args`, `∀ x, P x`, `P ∧ Q`). `↔` and definitional unfolding are
              NOT followed. A producer carrying non-corpus Prop premises (`2 ≤ q → P q`) is GUARDED.
  STRUCTURAL  (HEURISTIC, rule printed as data) P hangs as a binder head on >= 1 audited
              conditional result AND P's definition body passes STRUCTURAL_RULE.
  OPEN        neither.
DELIVERABLE B -- METHODS BY MACHINE. Each declaration's PROOF BODY (text after the statement,
up to the next command) is tokenised and every token that resolves in item 1's name index (with
item 1's namespace/open resolution) is a direct reference. Families are seeded by FAMILIES (data,
a CHOICE, printed on the page); family reach is propagated over the reference graph.

Usage:
  python3 scripts/methods_catalogue.py              write docs/METHODS-CATALOGUE.md + docs/methods-catalogue.tsv
  python3 scripts/methods_catalogue.py --stdout     print the page instead
  python3 scripts/methods_catalogue.py --check      exit 1 if either generated file is stale
  python3 scripts/methods_catalogue.py --self-test  run the fixture and the per-arm mutants
"""
from __future__ import annotations

import os
import re
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import results_catalogue as rc  # noqa: E402  (item 1: the parser is reused, not forked)

REPO = rc.REPO
PAGE = os.path.join("docs", "METHODS-CATALOGUE.md")
TSV = os.path.join("docs", "methods-catalogue.tsv")
COMMAND = "python3 scripts/methods_catalogue.py"
STATUSES = ["DISCHARGED", "STRUCTURAL", "FRAME", "OPEN"]
RESULT_ROW_CAP = 300   # per-result rows on the page; the TSV carries all of them
REF_CAP_TSV = 8        # direct references listed per TSV row (the count is always full)

# item 1 strips comments inside index_file; memoise so this script strips each file once.
_strip_orig = rc.strip_comments
_strip_cache: dict = {}


def _strip_memo(src):
    k = hash(src), len(src)
    if k not in _strip_cache: _strip_cache[k] = _strip_orig(src)
    return _strip_cache[k]


rc.strip_comments = _strip_memo

# ---------------------------------------------------------------- METHOD FAMILIES (DATA -- A CHOICE)
# family -> rules. A declaration belongs to every family one of whose rules matches:
#   paths  : path prefix · files : base-name substring · ns : namespace prefix of the full name
#   names  : substring of the declaration's last name component · stmt : substring of its statement
FAMILIES = [
    ("circle method / Fourier", dict(files=["CircleMethod", "StrideCircle", "Fourier", "Parseval", "Dft"],
                                     names=["dft", "Dft", "parseval", "Parseval", "fourier", "Fourier",
                                            "circleMethod", "CircleMethod"])),
    ("entropy decrement", dict(paths=["Salt/Entropy/"], names=["condEntropy", "mutualInfo", "entropy", "Entropy"])),
    ("large sieve", dict(paths=["Salt/LS/"], files=["LargeSieve"], names=["largeSieve", "LargeSieve"])),
    ("Selberg/Brun sieve", dict(paths=["Salt/Brun/", "Salt/BrunLower/", "Salt/Chen/", "Salt/Maynard/", "Salt/Parity/"],
                                files=["Sieve", "Selberg"])),
    ("Bombieri-Vinogradov / Siegel-Walfisz", dict(paths=["Salt/BV/", "Salt/SW/"], files=["SiegelWalfisz"])),
    ("zero-density / zero-free regions", dict(paths=["Salt/Vk/", "Salt/Vmvt/"], files=["Zero", "Zeta", "ZFR"],
                                              names=["zeroFree", "ZeroFree", "zeroDensity", "ZeroDensity"])),
    ("character sums / L-functions", dict(paths=["Salt/HB/", "Salt/Weil/"], files=["Char", "LFunction", "Dirichlet"],
                                          stmt=["DirichletCharacter", "LSeries"])),
    ("exponential sums", dict(paths=["Salt/ExpSum/", "Salt/Weil/"], files=["ExpSum", "Weyl", "VdC", "Kloosterman"],
                              names=["expSum", "ExpSum", "weilSum", "WeilSum"])),
    ("Mertens / PNT-type", dict(paths=["Salt/Mertens/"], files=["Mertens", "PNT"], names=["mertens", "Mertens"])),
    ("certificates / explicit numerics", dict(paths=["Salt/Certs/"], files=["CertEval"], ns=["Salt.CertEval", "Salt.Certs"])),
    ("explog/lognum numeral tactic", dict(ns=["Salt.Tactic"])),
    ("Matomaki-Radziwill / Halasz (short intervals)", dict(paths=["Salt/MR/"], files=["Halasz"])),
]
FAMILY_NAMES = [f for f, _ in FAMILIES]

# ---------------------------------------------------------------- STRUCTURAL (DATA -- A HEURISTIC)
STRUCTURAL_RULE = dict(
    max_body_chars=600,
    allowed_heads=list(rc.RELATIONS) + ["∨", "Not", "Nat.Coprime", "Coprime", "IsCoprime", "Squarefree",
                                        "Nat.Prime", "Prime", "Even", "Odd", "Disjoint", "True", "False"],
    forbidden_substrings=["Tendsto", "atTop", "=O[", "=o[", "∫", "∑'", "tsum", "limsup", "liminf", "Summable",
                          "HasSum", "deriv", "Filter", "∀ᶠ", "∃ᶠ", "volume", "Measure", "Real.exp", "Real.log",
                          "∑", "∏"],
    quantifier_bounds=["∈", "<", "≤", "⊆", "∣", ": Fin "],
)
STRUCTURAL_TEXT = (
    "P is STRUCTURAL iff (i) P is a binder head of >= 1 audited conditional result; (ii) P has a readable "
    "definition body (def/abbrev body after any `fun … =>`, or a Prop structure's fields joined by ∧) of at most "
    "`max_body_chars` characters; (iii) the body contains none of `forbidden_substrings`; (iv) every ∀/∃ in it is "
    "BOUNDED (its binder text, up to the depth-0 comma, contains one of `quantifier_bounds`); (v) every head symbol of "
    "every ∀/→-part and ∧-conjunct of the body is in `allowed_heads` or is itself a STRUCTURAL corpus Prop (fixpoint); "
    "(vi) the body references NO corpus declaration other than a STRUCTURAL corpus Prop (so an estimate on a corpus "
    "function — a count, a weighted sum — is never STRUCTURAL: it is a hypothesis). "
    "DISCHARGED takes precedence over STRUCTURAL.")


# ---------------------------------------------------------------- the corpus
def family_of(d) -> frozenset:
    out = set()
    base = os.path.basename(d.path)
    last = d.name.rsplit(".", 1)[-1]
    for i, (_, r) in enumerate(FAMILIES):
        if any(d.path.startswith(p) for p in r.get("paths", ())) \
                or any(s in base for s in r.get("files", ())) \
                or any(d.name == n or d.name.startswith(n + ".") for n in r.get("ns", ())) \
                or any(s in last for s in r.get("names", ())) \
                or any(s in d.stmt for s in r.get("stmt", ())):
            out.add(i)
    return frozenset(out)


_BOUND_WORDS = sorted(k for k in rc.KEYWORDS if k not in ("in", "at", "with", "by", "fun", "where", "local",
                                                          "scoped", "public", "meta"))
BOUNDARY_RE = re.compile(r"\n(?=@\[|#|(?:%s)\b)" % "|".join(re.escape(k) for k in _BOUND_WORDS))


def attach_bodies(files: dict, decls: dict):
    """Give every indexed declaration `.proof` = its full body text (statement end -> next command)."""
    by_site = defaultdict(list)
    for d in decls.values(): by_site[(d.path, d.line)].append(d)
    for path in sorted(files):
        text = rc.strip_comments(files[path])
        ms = list(rc.DECL_RE.finditer(text))
        for k, m in enumerate(ms):
            line = text.count("\n", 0, m.start(3)) + 1 if k == 0 else None
            if k: line = prev_line + text.count("\n", ms[k - 1].start(3), m.start(3))
            prev_line = line
            mname = re.match(r"\s+(\([^)]*\)\s*)?(" + rc.IDENT_RE.pattern + ")", text[m.end(3):])
            if not mname: continue
            cand = [d for d in by_site.get((path, line), ()) if d.short == mname.group(2)]
            if not cand: continue
            head = m.end(3) + mname.end(0)
            mm = re.match(r"\.\{[^}]*\}", text[head:])
            if mm: head += len(mm.group(0))
            stop = rc.statement_end(text, head)
            nxt = ms[k + 1].start(0) if k + 1 < len(ms) else len(text)
            b = BOUNDARY_RE.search(text, stop, nxt)
            end = b.start() if b else nxt
            for d in cand:
                if not hasattr(d, "proof"): d.proof = text[stop:end]
    for d in decls.values():
        if not hasattr(d, "proof"): d.proof = ""


def direct_refs(d, decls, cache) -> list:
    out, seen = [], set()
    ctx = (tuple(d.ns), tuple(d.opens))
    for m in rc.IDENT_RE.finditer(d.proof):
        s = m.start()
        if s and d.proof[s - 1] in ".'_": continue          # field/dot notation: `h.foo`, `(x).bar`
        tok = m.group(0)
        if tok in rc.KEYWORDS: continue
        key = (tok,) + ctx
        if key not in cache: cache[key] = rc.resolve(tok, d.ns, d.opens, decls)
        r = cache[key]
        if r and r != d.name and r not in seen:
            seen.add(r); out.append(r)
    return out


def load_corpus(files: dict, ledgers: list):
    decls: dict = {}
    for p in sorted(files): rc.index_file(p, files[p], decls, {})
    props = rc.build_propdefs(decls)
    attach_bodies(files, decls)
    audited = {}
    for lp in ledgers:
        for ident, ln, ns, opens in rc.parse_ledger(files[lp]):
            full = rc.resolve(ident, ns, opens, decls)
            if full and full not in audited: audited[full] = None
    kinds, hyps = {}, {}
    for n in audited:
        kinds[n], hyps[n] = rc.classify(decls[n], props)
    return decls, props, audited, kinds, hyps


# ---------------------------------------------------------------- deliverable A
def producer_heads(d, props):
    """(corpus Prop names this declaration's conclusion produces, guarded?)."""
    bs, concl = rc.split_decl(d)
    if concl is None: return [], False
    parts = rc.arrow_parts(concl)
    guarded = any(op in ("(", "[") and t and rc.prop_shaped(t, d.ns, d.opens, props) for op, _, t in bs) \
        or len(parts) > 1
    final = rc.strip_parens(parts[-1])
    out = []
    if final.startswith(("∃", "¬")): return [], guarded       # head is ∃ / ¬, never P
    for c in rc.split_top(final, "∧"):                   # ONE level of conjunction
        cp = rc.arrow_parts(c)
        if len(cp) > 1:
            if any(rc.resolve(h, d.ns, d.opens, props) for t in cp[:-1] for h in rc.heads(t)): continue
            guarded = True
        s = rc.strip_parens(cp[-1])
        if s.startswith(("∃", "¬")): continue
        if rc.find_top(s, lambda t, i: t.startswith("∧", i)) >= 0: continue   # a deeper ∧: not walked
        hs = rc.heads(s)
        if len(hs) != 1: continue
        r = rc.resolve(hs[0], d.ns, d.opens, props)
        if r and r not in out: out.append(r)
    return out, guarded


def witness_heads(d, props):
    """Corpus Props P with a conclusion `∃ w, … ∧ P w ∧ …` (an ∃-WITNESS producer: NOT a discharge)."""
    bs, concl = rc.split_decl(d)
    if concl is None: return []
    final = rc.strip_parens(rc.arrow_parts(concl)[-1])
    if not final.startswith("∃"): return []
    c = rc.find_top(final, lambda t, i: t[i] == ",")
    if c < 0: return []
    out = []
    for part in rc.split_top(final[c + 1:], "∧"):
        hs = rc.heads(rc.strip_parens(part))
        r = rc.resolve(hs[0], d.ns, d.opens, props) if len(hs) == 1 else None
        if r and r not in out: out.append(r)
    return out


PRODUCER_KWS = ("theorem", "lemma", "def", "abbrev", "instance", "opaque", "irreducible_def")


def def_body(d, decls):
    if d.kw in ("structure", "class"):
        fs = rc.structure_fields(d)
        return " ∧ ".join("(%s)" % f.strip() for f in fs) if fs else ""
    b = d.proof.strip()
    if not b.startswith(":="): return ""
    b = b[2:].strip()
    while True:
        m = re.match(r"(?:fun|λ)\s[^=]*?=>\s*", b)
        if not m: break
        b = b[m.end():]
    return b.strip()


def structural_body_ok(d, decls, props, structural) -> bool:
    R = STRUCTURAL_RULE
    b = def_body(d, decls)
    if not b or len(b) > R["max_body_chars"]: return False
    if any(s in b for s in R["forbidden_substrings"]): return False
    for m in re.finditer(r"[∀∃]!?", b):
        rest = b[m.end():]
        c = rc.find_top(rest, lambda t, i: t[i] == ",")
        binder = rest[:c] if c >= 0 else rest
        if not any(q in binder for q in R["quantifier_bounds"]): return False
    for m in rc.IDENT_RE.finditer(b):
        if m.start() and b[m.start() - 1] in ".'_": continue
        r = rc.resolve(m.group(0), d.ns, d.opens, decls)
        if r and r != d.name and not (r in props and r in structural): return False
    parts = rc.arrow_parts(b)
    for t in parts:
        for h in rc.heads(t):
            if h in R["allowed_heads"]: continue
            r = rc.resolve(h, d.ns, d.opens, props)
            if r and r in structural and r != d.name: continue
            return False
    return True


# ---------------------------------------------------------------- FRAME (DATA -- A HEURISTIC, O13 pull 2)
FRAME_RULE = dict(
    relations=["≤", "<", "=", "≠", "≥", ">", "∣", "∈", "∉"],
    binder_types=["ℕ", "ℝ", "ℚ", "ℤ"],
    forbidden_substrings=["∃", "∨", "↔", "¬", "Tendsto", "atTop", "=O[", "=o[", "=ᶠ[", "≤ᶠ[", "~[", "∫", "∑", "∏",
                          "tsum", "limsup", "liminf", "Summable", "HasSum", "deriv", "Filter", "∀ᶠ", "∃ᶠ", "volume",
                          "Measure", "ℂ", "‖", "LFunction", "DirichletCharacter", "riemannZeta", "Complex"],
    # closed-form ℕ/ℝ-valued arithmetic in their own arguments (each body read at source, O13 pull 2):
    # no sum, no set, no ℂ, no corpus analytic object; each references only mathlib or this list.
    allowed_corpus_helpers=[
        "Salt.MR.calE", "Salt.MR.calP", "Salt.MR.calQK", "Salt.MR.s13GK", "Salt.MR.Adoor", "Salt.MR.AdoorL",
        "Salt.MR.doorRowFloor", "Salt.MR.theta293", "Salt.MR.rho293", "Salt.MR.s13Aexp", "Salt.MR.s13Eta",
        "Salt.MR.ramQbase", "Salt.MR.a2Level1", "Salt.MR.a2Level1_L", "Salt.MR.H1door", "Salt.MR.H1doorL",
        "Salt.MR.Q83", "Salt.MR.P83", "Salt.MR.H83", "Salt.MR.vkStripConst", "Salt.MR.s13Mr", "Salt.MR.calH",
        "Salt.MR.s13Lr", "Salt.MR.s13EpsD", "Salt.MR.mrAlpha", "Salt.MR.arcDen", "Salt.MR.s13BlockExp",
        "Salt.MR.s13BlockExp_gk", "Salt.MR.s13BlockFloor", "Salt.MR.s13BlockFloor_gk", "Salt.MR.Tstar",
        "Salt.MR.ballMertensThreshold", "Salt.MR.ramRbot", "Salt.MR.seamT0",
    ],
)
FRAME_TEXT = (
    "P is FRAME iff its readable definition body (def/abbrev body after any `fun … =>`, or a Prop structure's OWN "
    "fields joined by ∧) (i) contains none of `forbidden_substrings`; (ii) after walking leading ∀-binders — each "
    "binder's type in `binder_types`, untyped, or bounded by a relation (`n ∈ A`) — and → premises and top-level ∧, "
    "every atom is an ORDER RELATION (a depth-0 symbol from `relations`), `True`, or a FRAME corpus Prop (fixpoint); "
    "(iii) every token of the body that resolves to a corpus declaration is a FRAME corpus Prop or is in "
    "`allowed_corpus_helpers`. Mathlib functions (`Real.log`, `Real.exp`, `Nat.log`, casts) are outside the corpus and "
    "are not restricted beyond (i). Precedence: DISCHARGED, then STRUCTURAL (unchanged), then FRAME, then OPEN. "
    "A FRAME name is a bundle of range conditions on its own parameters: its negation is 'the parameters are out of "
    "range', never a fulcrum horn.")


def _frame_binder_ok(bnd: str) -> bool:
    R = FRAME_RULE
    bnd = bnd.strip()
    if any(rc.find_top(bnd, lambda t, i, r=r: t.startswith(r, i)) >= 0 for r in R["relations"]):
        return True                                           # a bounded binder: `n ∈ A`, `x ≤ y`
    bs, rest = rc.parse_binders(bnd)
    if bs:
        return not rest.strip() and all(t.strip() in R["binder_types"] for _, _, t in bs)
    k = rc.top_colon(bnd)
    return k < 0 or bnd[k + 1:].strip() in R["binder_types"]


def _frame_shape_ok(s: str, d, props, frame) -> bool:
    R = FRAME_RULE
    s = rc.strip_parens(s)
    if not s: return False
    if s.startswith("∀"):
        c = rc.find_top(s, lambda t, i: t[i] == ",")
        if c < 0 or not _frame_binder_ok(s[1:c]): return False
        return _frame_shape_ok(s[c + 1:], d, props, frame)
    parts = [p.strip() for p in rc.split_top(s, "→")]
    if len(parts) > 1: return all(_frame_shape_ok(p, d, props, frame) for p in parts)
    conj = rc.split_top(s, "∧")
    if len(conj) > 1: return all(_frame_shape_ok(c, d, props, frame) for c in conj)
    if s == "True": return True
    if any(rc.find_top(s, lambda t, i, r=r: t.startswith(r, i)) >= 0 for r in R["relations"]): return True
    m = rc.IDENT_RE.match(s.lstrip("@"))
    if not m: return False
    r = rc.resolve(m.group(0), d.ns, d.opens, props)
    return bool(r) and r != d.name and r in frame


def frame_body_ok(d, decls, props, frame) -> bool:
    R = FRAME_RULE
    b = def_body(d, decls)
    if not b or any(x in b for x in R["forbidden_substrings"]): return False
    for m in rc.IDENT_RE.finditer(b):
        if m.start() and b[m.start() - 1] in ".'_": continue
        r = rc.resolve(m.group(0), d.ns, d.opens, decls)
        if r and r != d.name and not (r in props and r in frame) and r not in R["allowed_corpus_helpers"]:
            return False
    return _frame_shape_ok(b, d, props, frame)


def frame_set(decls, props) -> set:
    """The FRAME rule's fixpoint over EVERY corpus Prop (status-blind; the status precedence is applied after)."""
    frame: set = set()
    for _ in range(12):
        new = {P for P in props if frame_body_ok(decls[P], decls, props, frame)}
        if new == frame: break
        frame = new
    return frame


def hypothesis_status(decls, props, audited, kinds, hyps):
    producers = defaultdict(list)     # P -> [(name, guarded)]
    cond_producers = defaultdict(list)
    witness = defaultdict(list)
    for n, d in decls.items():
        if d.kw not in PRODUCER_KWS: continue
        hs, guarded = producer_heads(d, props)
        ws = witness_heads(d, props)
        if not hs and not ws: continue
        k, _ = rc.classify(d, props)
        if k == "unconditional":
            for P in ws: witness[P].append(n)
        for P in hs:
            if P == n: continue
            if k == "unconditional": producers[P].append((n, guarded))
            elif k == "conditional": cond_producers[P].append(n)
    hang = defaultdict(list)
    for n in audited:
        for h in hyps[n]: hang[h].append(n)
    structural: set = set()
    for _ in range(4):                                     # fixpoint over Props built from Props
        new = {P for P in props if P in hang and P not in producers
               and structural_body_ok(decls[P], decls, props, structural)}
        if new == structural: break
        structural = new
    frame = frame_set(decls, props)
    status = {}
    for P in props:
        status[P] = "DISCHARGED" if producers.get(P) else ("STRUCTURAL" if P in structural else
                                                            ("FRAME" if P in frame else "OPEN"))
    return status, producers, cond_producers, hang, witness, frame


# ---------------------------------------------------------------- deliverable B
def build_graph(decls):
    cache: dict = {}
    names = sorted(decls)
    idx = {n: i for i, n in enumerate(names)}
    succ = [[idx[r] for r in direct_refs(decls[n], decls, cache)] for n in names]
    return names, idx, succ


def sccs(n, succ):
    """Iterative Tarjan; returns SCCs in reverse topological order (sinks first)."""
    index, low, on, st, out = [-1] * n, [0] * n, [False] * n, [], []
    counter = 0
    for root in range(n):
        if index[root] >= 0: continue
        work = [(root, 0)]
        while work:
            v, pi = work.pop()
            if pi == 0:
                index[v] = low[v] = counter; counter += 1; st.append(v); on[v] = True
            recursed = False
            for j in range(pi, len(succ[v])):
                w = succ[v][j]
                if index[w] < 0:
                    work.append((v, j + 1)); work.append((w, 0)); recursed = True; break
                if on[w]: low[v] = min(low[v], index[w])
            if recursed: continue
            if low[v] == index[v]:
                comp = []
                while True:
                    w = st.pop(); on[w] = False; comp.append(w)
                    if w == v: break
                out.append(comp)
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
    return out


def propagate(names, succ, fam, audited_idx):
    """reach[v]: family bitmask over v's STRICT transitive closure; anc[v]: bitset (over audited
    ordinal) of audited results that reach v strictly."""
    n = len(names)
    comps = sccs(n, succ)
    comp_of = [0] * n
    for ci, c in enumerate(comps):
        for v in c: comp_of[v] = ci
    famask = [sum(1 << f for f in fam[v]) for v in range(n)]
    reach = [0] * n
    for c in comps:                                        # sinks first
        m = 0
        for v in c:
            for w in succ[v]:
                m |= famask[w] | reach[w]
        for v in c: reach[v] = m
    pred = [[] for _ in range(n)]
    for v in range(n):
        for w in succ[v]: pred[w].append(v)
    abit = [(1 << audited_idx[v]) if v in audited_idx else 0 for v in range(n)]
    anc = [0] * n
    for c in reversed(comps):                              # sources first
        m = 0
        for v in c:
            for u in pred[v]:
                m |= abit[u] | anc[u]
        for v in c: anc[v] = m
    return reach, anc, famask


# ---------------------------------------------------------------- the build
def build(files: dict, ledgers: list, families=None):
    global FAMILIES
    saved = FAMILIES
    if families is not None: FAMILIES = families
    try:
        decls, props, audited, kinds, hyps = load_corpus(files, ledgers)
        status, producers, condp, hang, witness, frame = hypothesis_status(decls, props, audited, kinds, hyps)
        names, idx, succ = build_graph(decls)
        fam = [family_of(decls[nm]) for nm in names]
        aud_list = sorted(audited)
        audited_idx = {idx[a]: i for i, a in enumerate(aud_list)}
        reach, anc, famask = propagate(names, succ, fam, audited_idx)
        results = {}
        for a in aud_list:
            v = idx[a]
            dfam = 0
            for w in succ[v]: dfam |= famask[w]
            results[a] = dict(kind=kinds[a], path=decls[a].path, line=decls[a].line,
                              refs=[names[w] for w in succ[v]], own=famask[v], direct=dfam,
                              trans=reach[v], indeg=bin(anc[v]).count("1"))
        nfam = len(FAMILIES)
        fstats = []
        for f in range(nfam):
            bit = 1 << f
            members = [v for v in range(len(names)) if famask[v] & bit]
            amembers = [v for v in members if v in audited_idx]
            dep = 0
            for v in members: dep |= anc[v]
            own = 0
            for v in amembers: own |= 1 << audited_idx[v]
            by_kind = {k: sum(1 for a in aud_list if results[a]["trans"] & bit and results[a]["kind"] == k)
                       for k in rc.KINDS}
            top = sorted(amembers, key=lambda v: (-bin(anc[v]).count("1"), names[v]))[:10]
            fstats.append(dict(members=len(members), amembers=len(amembers), by_kind=by_kind,
                               dependents=bin(dep).count("1"), external=bin(dep & ~own).count("1"),
                               top=[(names[v], bin(anc[v]).count("1")) for v in top]))
        receipt = dict(decls=len(decls), props=len(props), audited=len(audited),
                       edges=sum(len(s) for s in succ), with_body=sum(1 for d in decls.values() if d.proof.strip()))
        return dict(decls=decls, props=props, status=status, frame=frame, producers=producers, condp=condp, hang=hang, witness=witness,
                    results=results, fstats=fstats, receipt=receipt, audited=audited, families=list(FAMILIES))
    finally:
        FAMILIES = saved


def fams_str(mask, families, codes=False) -> str:
    sep = "," if codes else "; "
    return sep.join(("F%02d" % (i + 1)) if codes else families[i][0]
                    for i in range(len(families)) if mask >> i & 1) or "-"


# ---------------------------------------------------------------- render
CONTROLS = (("Salt.MR.FlatDoorAllGradesW", "DISCHARGED"), ("Salt.MR.MRTDoorAllGrades", "OPEN"),
            ("Salt.MR.DoorBaseFrame", "FRAME"), ("Salt.MR.DoorArithFrameRho_L", "FRAME"),
            ("Salt.MR.CofactorSocket", "OPEN"), ("Salt.Fulcrum.FulcrumQualityMin", "OPEN"))


def render(B, base: str, digest: str) -> tuple[str, str]:
    st, prod, condp, hang, res, fs, decls = (B["status"], B["producers"], B["condp"], B["hang"], B["results"],
                                             B["fstats"], B["decls"])
    families, audited, rcp = B["families"], B["audited"], B["receipt"]
    L = []
    L.append("# THE METHODS CATALOGUE + HYPOTHESIS STATUS — by machine (O13 item 2)")
    L.append("")
    L.append("> **GENERATED — do not edit by hand.** Regenerate: `%s` · staleness gate: `%s --check`." % (COMMAND, COMMAND))
    L.append("> Base: last commit touching `Salt/` = `%s` · source digest `%s` (the same digest as item 1's "
             "`docs/CATALOGUE.md`). Full per-result data: `%s`." % (base, digest, TSV))
    L.append("")
    L.append("## Receipt")
    L.append("")
    L.append("Declarations indexed: %d · with a proof/definition body: %d · direct corpus references (edges): %d · "
             "audited results: %d · corpus Prop-valued names: %d." % (rcp["decls"], rcp["with_body"], rcp["edges"],
                                                                     rcp["audited"], rcp["props"]))
    L.append("")
    L.append("## Hypothesis status (Deliverable A)")
    L.append("")
    hung = {P for P in st if hang.get(P)}
    guarded_only = {P for P in st if st[P] == "DISCHARGED" and all(g for _, g in prod[P])}
    L.append("| status | corpus Props | hung on >= 1 audited conditional result | audited conditional results hanging on them |")
    L.append("|---|---|---|---|")
    for s in STATUSES:
        ps = [P for P in st if st[P] == s]
        L.append("| %s | %d | %d | %d |" % (s, len(ps), sum(1 for P in ps if P in hung),
                                          len({r for P in ps for r in hang.get(P, [])})))
    L.append("| **all** | %d | %d | %d |" % (len(st), len(hung), len({r for P in st for r in hang.get(P, [])})))
    L.append("")
    L.append("Of the DISCHARGED, %d are discharged ONLY by GUARDED producers (the producer carries non-corpus Prop "
             "premises, e.g. `2 ≤ q → P q`, or instantiates P at specific arguments)." % len(guarded_only))
    L.append("")
    fr = B["frame"]
    L.append("FRAME overlap (the FRAME rule is evaluated on EVERY corpus Prop, status-blind; precedence then assigns one "
             "status): %d Props pass the FRAME rule — %d are DISCHARGED, %d are STRUCTURAL (STRUCTURAL kept, not "
             "re-labelled), %d carry status FRAME. STRUCTURAL Props that FAIL the FRAME rule: %d."
             % (len(fr), sum(1 for P in fr if st[P] == "DISCHARGED"), sum(1 for P in fr if st[P] == "STRUCTURAL"),
                sum(1 for P in fr if st[P] == "FRAME"), sum(1 for P in st if st[P] == "STRUCTURAL" and P not in fr)))
    L.append("")
    L.append("## LIMITS — read these beside every count above")
    L.append("")
    L.append("- **Everything item 1's LIMITS say applies** (source-level parse, no elaboration; macros/`alias`/"
             "`to_additive`/`simps` invisible; implicit binders not walked; the Prop-valued set is itself heuristic).")
    L.append("- **DISCHARGED is a SOURCE-LEVEL head match.** A producer's conclusion head (after ∀/→ and ONE level "
             "of top-level ∧) must resolve to P. `↔`, definitional unfolding, `.mp`/`.1` projections, anonymous "
             "`instance : P`, and producers generated by macros are NOT seen — so OPEN may over-count. `P args` counts: "
             "a producer at SPECIFIC arguments (`theorem : P 3`) or under side conditions is marked GUARDED and still "
             "counts as DISCHARGED — read the producer before relying on it.")
    L.append("- **An `∃`-headed conclusion never discharges** (its head is `∃`); `∃ w, … ∧ P w` is reported as an "
             "∃-WITNESS producer beside the OPEN row instead. Whether it discharges a given consumer depends on how the "
             "consumer quantifies P's parameters — a question this parser does not answer.")
    L.append("- **A producer's own KIND is item 1's classifier:** a theorem with a corpus-Prop binder is conditional "
             "and does NOT discharge (it is listed as a conditional producer: a REDUCTION, not a proof).")
    L.append("- **STRUCTURAL is a HEURISTIC** (rule below, as data). It only separates benign predicates "
             "(bounded arithmetic / membership conditions) from unproved hypotheses; a STRUCTURAL name is not "
             "proved anywhere, its instances are expected to be produced by a proof step at the use site.")
    L.append("- **FRAME is a HEURISTIC** (rule below, as data): a bundle of order relations over the Prop's own "
             "parameters, built only from mathlib functions and a WRITTEN allow-list of corpus arithmetic helpers. It "
             "is not proved anywhere; it is separated from OPEN because its negation is 'the parameters are out of "
             "range', never a fulcrum horn. A frame that references a corpus helper NOT on the allow-list stays OPEN "
             "(the rule errs toward OPEN); a local variable sharing a corpus name also keeps a Prop OPEN. A projection of "
             "a PARAMETER (`R.Hlo` for `R : ChowlaRegime`) is not a corpus token, so a range condition on a regime's "
             "fields can be FRAME even though the regime's type is a corpus structure.")
    L.append("- **Hang counts are over AUDITED conditional results only**, as in item 1's payoff table.")
    L.append("- **References are TOKENS in the proof body** that resolve in item 1's name index with item 1's "
             "namespace/`open` resolution. Dot/field notation (`h.foo`, `(x).bar`), notation, `simp` sets named by "
             "attribute, instance resolution and elaboration-time references are INVISIBLE; a local variable that "
             "shares a corpus declaration's name is a FALSE edge. mathlib is outside the graph.")
    L.append("- **Transitive closure is STRICT** (a result's own family is reported separately as `own`) and "
             "within the corpus only. The family map is a CHOICE (below); a declaration may sit in several families "
             "or none. Transitive in-degree = number of AUDITED results whose strict closure contains the declaration.")
    L.append("- **Per-result rows on this page are CAPPED at %d** (the most depended-upon audited results); every "
             "audited result is in `%s` (direct references listed up to %d per row, the count always full)."
             % (RESULT_ROW_CAP, TSV, REF_CAP_TSV))
    L.append("")
    L.append("<details><summary>STRUCTURAL rule (data in the script)</summary>")
    L.append("")
    L.append(STRUCTURAL_TEXT)
    L.append("")
    for k, v in STRUCTURAL_RULE.items():
        L.append("- `%s`: %s" % (k, rc.md_escape(", ".join("`%s`" % x for x in v) if isinstance(v, list) else str(v))))
    L.append("")
    L.append("</details>")
    L.append("")
    L.append("<details><summary>FRAME rule (data in the script)</summary>")
    L.append("")
    L.append(FRAME_TEXT)
    L.append("")
    for k, v in FRAME_RULE.items():
        L.append("- `%s`: %s" % (k, rc.md_escape(", ".join("`%s`" % x for x in v) if isinstance(v, list) else str(v))))
    L.append("")
    L.append("</details>")
    L.append("")
    L.append("<details><summary>Method family map — A CHOICE (data in the script)</summary>")
    L.append("")
    L.append("| family | rules |")
    L.append("|---|---|")
    for f, r in families:
        L.append("| %s | %s |" % (f, rc.md_escape(" · ".join("%s: %s" % (k, ", ".join("`%s`" % x for x in v))
                                                          for k, v in r.items()))))
    L.append("")
    L.append("</details>")
    L.append("")
    L.append("## Positive controls")
    L.append("")
    for P, want in CONTROLS:
        got = st.get(P, "ABSENT")
        pr = ", ".join("`%s`" % n for n, _ in prod.get(P, [])[:3]) or "none"
        L.append("- `%s`: **%s** (expected %s) · producers: %s · conditional producers: %d · hang count: %d"
                 % (P, got, want, pr, len(condp.get(P, [])), len(hang.get(P, []))))
    L.append("")

    def prod_cell(P):
        ps = prod.get(P, [])
        if not ps: return "—"
        out = []
        for n, g in ps[:3]:
            d = decls[n]
            out.append("`%s`%s%s (%s:%d)" % (n, " ✓audited" if n in audited else "", " GUARDED" if g else "",
                                             d.path, d.line))
        if len(ps) > 3: out.append("+%d" % (len(ps) - 3))
        return rc.md_escape(" · ".join(out))

    L.append("## THE O2 PAYOFF TABLE — OPEN hypotheses ranked by hang-count")
    L.append("")
    L.append("Which single unproved Prop, if proved, unlocks the most audited results. `cond. producers` = corpus "
             "theorems that REDUCE it to other hypotheses. `∃-witness producers` = unconditional theorems proving "
             "`∃ w, … P w …`: P holds at SOME parameter, which is not a discharge under the head rule — read them "
             "before ranking P as unproved.")
    L.append("")
    L.append("| rank | hypothesis | hang count | cond. producers | ∃-witness producers | defined at |")
    L.append("|---|---|---|---|---|---|")
    opens = sorted((P for P in st if st[P] == "OPEN" and hang.get(P)), key=lambda P: (-len(hang[P]), P))
    for i, P in enumerate(opens, 1):
        L.append("| %d | `%s` | %d | %d | %s | %s:%d |" % (
            i, rc.md_escape(P), len(hang[P]), len(condp.get(P, [])),
            rc.md_escape(", ".join("`%s`" % w for w in B["witness"].get(P, [])[:2])
                         + (" +%d" % (len(B["witness"][P]) - 2) if len(B["witness"].get(P, [])) > 2 else "")) or "—",
            decls[P].path, decls[P].line))
    L.append("")
    L.append("## Item 1's payoff table, re-ranked by status")
    L.append("")
    L.append("| hypothesis | status | hang count | producer(s) |")
    L.append("|---|---|---|---|")
    for P in sorted(hung, key=lambda P: (STATUSES.index(st[P]), -len(hang[P]), P)):
        L.append("| `%s` | %s | %d | %s |" % (rc.md_escape(P), st[P], len(hang[P]), prod_cell(P)))
    L.append("")
    L.append("## Every corpus Prop not hung on an audited result (%d)" % (len(st) - len(hung)))
    L.append("")
    L.append("| hypothesis | status | producer(s) |")
    L.append("|---|---|---|")
    for P in sorted((P for P in st if P not in hung), key=lambda P: (STATUSES.index(st[P]), P)):
        L.append("| `%s` | %s | %s |" % (rc.md_escape(P), st[P], prod_cell(P)))
    L.append("")
    L.append("## Families × KIND (Deliverable B) — audited results whose STRICT closure reaches the family")
    L.append("")
    L.append("| family | decls in family | audited in family | " + " | ".join(rc.KINDS) +
             " | audited dependents | external dependents |")
    L.append("|---|---|---|" + "---|" * len(rc.KINDS) + "---|---|")
    for i, f in enumerate(families):
        s = fs[i]
        L.append("| %s | %d | %d | " % (f[0], s["members"], s["amembers"]) +
                 " | ".join(str(s["by_kind"][k]) for k in rc.KINDS) + " | %d | %d |" % (s["dependents"], s["external"]))
    L.append("")
    L.append("`audited dependents` = audited results whose strict closure contains a member of the family; "
             "`external` excludes the family's own audited members.")
    L.append("")
    L.append("## The load-bearing methods — per family, top 10 audited members by transitive in-degree")
    L.append("")
    order = sorted(range(len(families)), key=lambda i: -fs[i]["external"])
    for i in order:
        L.append("### %s — %d external dependents" % (families[i][0], fs[i]["external"]))
        L.append("")
        if not fs[i]["top"]:
            L.append("(no audited member)"); L.append(""); continue
        L.append("| audited member | in-degree | file:line |")
        L.append("|---|---|---|")
        for n, c in fs[i]["top"]:
            L.append("| `%s` | %d | %s:%d |" % (rc.md_escape(n), c, decls[n].path, decls[n].line))
        L.append("")
    L.append("## Dormant machinery — families by fewest external dependents (candidates for the fulcrum-broadly item)")
    L.append("")
    L.append("| family | external dependents | audited members | decls |")
    L.append("|---|---|---|---|")
    for i in sorted(range(len(families)), key=lambda i: (fs[i]["external"], families[i][0])):
        L.append("| %s | %d | %d | %d |" % (families[i][0], fs[i]["external"], fs[i]["amembers"], fs[i]["members"]))
    L.append("")
    L.append("## Audited results — the %d most depended-upon (cap; all rows in `%s`)" % (RESULT_ROW_CAP, TSV))
    L.append("")
    L.append("| result | kind | in-degree | direct refs | own family | direct families | transitive families |")
    L.append("|---|---|---|---|---|---|---|")
    top = sorted(res, key=lambda a: (-res[a]["indeg"], a))[:RESULT_ROW_CAP]
    for a in top:
        r = res[a]
        L.append("| `%s` | %s | %d | %d | %s | %s | %s |" % (rc.md_escape(a), r["kind"], r["indeg"], len(r["refs"]),
                                                            fams_str(r["own"], families), fams_str(r["direct"], families),
                                                            fams_str(r["trans"], families)))
    L.append("")
    page = "\n".join(L) + "\n"
    T = ["# GENERATED by `%s` — base %s · digest %s. record=hyp: status/hang/producers (!g = GUARDED); "
         "record=result: methods. Family codes: %s" % (COMMAND, base, digest,
                                                     " · ".join("F%02d=%s" % (i + 1, f) for i, (f, _) in enumerate(families))),
         "record\tname\tstatus_or_kind\tfile:line\thang_or_indeg\tproducers_or_refcount\town\tdirect_families"
         "\ttransitive_families\trefs"]
    for P in sorted(st):
        T.append("hyp\t%s\t%s\t%s:%d\t%d\t%s\t\t\t\t" % (P, st[P], decls[P].path, decls[P].line, len(hang.get(P, [])),
                                                         ",".join(n + ("!g" if g else "") for n, g in prod.get(P, []))))
    for a in sorted(res):
        r = res[a]
        refs = r["refs"][:REF_CAP_TSV]
        more = len(r["refs"]) - len(refs)
        T.append("result\t%s\t%s\t%s:%d\t%d\t%d\t%s\t%s\t%s\t%s" % (
            a, r["kind"], r["path"], r["line"], r["indeg"], len(r["refs"]), fams_str(r["own"], families, True),
            fams_str(r["direct"], families, True), fams_str(r["trans"], families, True),
            ",".join(refs) + (",+%d" % more if more > 0 else "")))
    return page, "\n".join(T) + "\n"


def generate():
    files, ledgers, digest = rc.load_repo()
    B = build(files, ledgers)
    base = rc.git("log", "-1", "--format=%h", "--", "Salt") or "unknown"
    page, tsv = render(B, base, digest)
    return page, tsv, B


# ---------------------------------------------------------------- self-test
FIXTURE = {
    "Salt/Fx/Defs.lean": '''
namespace Salt.Fx
def HDis (n : ℕ) : Prop := ∀ m, m ≤ n → m ≤ n
def HConj : Prop := ∀ x : ℕ, x = x
def HIff : Prop := ∀ x : ℕ, x = x
def HCondProd : Prop := ∀ x : ℕ, 0 ≤ x
def HOpen : Prop := ∀ x : ℕ, ∃ y, x < y
def HStruct (q : ℕ) (A : Finset ℕ) : Prop :=
  ∀ n ∈ A, n ≠ 0 ∧ Nat.Coprime n q
def HNested : Prop := ∀ x : ℕ, x ≤ x + 1
def HWit (c : ℕ) : Prop := ∀ x : ℕ, x ≤ x + c
def fxw (n : ℕ) : ℕ := n
def HGate (x T : ℝ) : Prop := Real.exp (30 * Real.log x) ≤ T
structure HFrame (X j : ℕ) : Prop where
  X_three : (3 : ℝ) ≤ (X : ℝ)
  h_four : 4 ≤ 2 ^ j ∧ j ≠ 0
  gate : HGate (X : ℝ) (2 * (X : ℝ))
def HSock (b : ℕ → ℕ) (R : ℕ) : Prop := ∀ n : ℕ, n ≤ R → fxw (b n) ≤ R
end Salt.Fx
''',
    "Salt/LS/Fx.lean": '''
namespace Salt.LS
theorem ls_core : 1 ≤ 2 := by norm_num
end Salt.LS
''',
    "Salt/Entropy/Fx.lean": '''
namespace Salt.Entropy
theorem ent_core : 2 ≤ 3 := by norm_num
theorem ent_uses_ls : 1 ≤ 2 := Salt.LS.ls_core
end Salt.Entropy
''',
    "Salt/Fx/Main.lean": '''
import Salt.Fx.Defs
namespace Salt.Fx
open Salt.Entropy
theorem top_a : 1 ≤ 2 := by
  -- Salt.LS.ls_core in a comment must not count
  exact (ent_uses_ls)
theorem top_b : 2 ≤ 3 := Salt.Entropy.ent_core
theorem top_c (h : HStruct 3 ∅) : True := trivial
theorem top_d (h : HOpen) : True := trivial
theorem top_e (h : HOpen) (h2 : HNested) : True := trivial
theorem hdis_holds : ∀ n, HDis n := fun n m h => h
theorem conj_holds : HConj ∧ 1 ≤ 2 := ⟨fun x => rfl, by norm_num⟩
theorem iff_only : HIff ↔ True := by simp [HIff]
theorem cp (h : HOpen) : HCondProd := fun x => Nat.zero_le x
theorem wit : ∃ c : ℕ, 0 ≤ c ∧ HWit c := ⟨0, le_rfl, fun x => le_rfl⟩
theorem nested : (HNested ∧ True) ∧ True := ⟨⟨fun x => Nat.le_succ x, trivial⟩, trivial⟩
end Salt.Fx
''',
    "Salt/Fx/All.lean": '''
#audit_axioms Salt.Fx.top_a Salt.Fx.top_b Salt.Fx.top_c Salt.Fx.top_d Salt.Fx.top_e
#audit_axioms Salt.Entropy.ent_uses_ls Salt.LS.ls_core Salt.Entropy.ent_core Salt.Fx.hdis_holds
''',
}
EXPECT_STATUS = {"Salt.Fx.HDis": "DISCHARGED", "Salt.Fx.HConj": "DISCHARGED", "Salt.Fx.HIff": "FRAME",
                 "Salt.Fx.HCondProd": "FRAME", "Salt.Fx.HOpen": "OPEN", "Salt.Fx.HStruct": "STRUCTURAL",
                 "Salt.Fx.HNested": "FRAME", "Salt.Fx.HWit": "FRAME",
                 # FRAME (O13): a structure frame by fixpoint through a gate, and a socket that must NOT be FRAME
                 "Salt.Fx.HGate": "FRAME", "Salt.Fx.HFrame": "FRAME", "Salt.Fx.HSock": "OPEN"}
FI = {f: i for i, (f, _) in enumerate(FAMILIES)}
ENT, LS = 1 << FI["entropy decrement"], 1 << FI["large sieve"]
EXPECT_GRAPH = {  # name -> (direct family mask, transitive family mask, transitive in-degree)
    "Salt.Fx.top_a": (ENT, ENT | LS, 0), "Salt.Fx.top_b": (ENT, ENT, 0),
    "Salt.Entropy.ent_uses_ls": (LS, LS, 1), "Salt.LS.ls_core": (0, 0, 2), "Salt.Entropy.ent_core": (0, 0, 1),
}


def check_fixture(fx, families=None) -> list:
    ledgers = sorted(p for p in fx if p.endswith("All.lean"))
    B = build(fx, ledgers, families)
    errs = []
    for P, s in EXPECT_STATUS.items():
        if B["status"].get(P) != s: errs.append("%s: status %s, want %s" % (P, B["status"].get(P), s))
    if [n for n, _ in B["producers"].get("Salt.Fx.HDis", [])] != ["Salt.Fx.hdis_holds"]:
        errs.append("HDis producers %s" % B["producers"].get("Salt.Fx.HDis"))
    if B["condp"].get("Salt.Fx.HCondProd") != ["Salt.Fx.cp"]: errs.append("HCondProd cond producers")
    if B["witness"].get("Salt.Fx.HWit") != ["Salt.Fx.wit"]: errs.append("HWit witness %s" % B["witness"].get("Salt.Fx.HWit"))
    if len(B["hang"].get("Salt.Fx.HOpen", [])) != 2: errs.append("HOpen hang %s" % B["hang"].get("Salt.Fx.HOpen"))
    for n, (dm, tm, deg) in EXPECT_GRAPH.items():
        r = B["results"].get(n)
        if r is None: errs.append("missing %s" % n); continue
        if (r["direct"], r["trans"], r["indeg"]) != (dm, tm, deg):
            errs.append("%s: direct %d trans %d indeg %d, want %d %d %d" % (n, r["direct"], r["trans"], r["indeg"],
                                                                            dm, tm, deg))
    return errs


def _fam_without(fname, key, val):
    out = []
    for f, r in FAMILIES:
        r2 = {k: [x for x in v if not (f == fname and k == key and x == val)] for k, v in r.items()}
        out.append((f, r2))
    return out


# each mutant must make the fixture check FAIL (the arm is shown able to fail)
MUTANTS = [
    ("A DISCHARGED arm: producer gains a corpus binder", "Salt/Fx/Main.lean",
     "theorem hdis_holds : ∀ n, HDis n", "theorem hdis_holds (hh : HOpen) : ∀ n, HDis n", None),
    ("A ∀-walk arm: producer's ∀ body loses P", "Salt/Fx/Main.lean",
     "hdis_holds : ∀ n, HDis n", "hdis_holds : ∀ n, n ≤ n", None),
    ("A ∧ arm: conjunct producer loses P", "Salt/Fx/Main.lean",
     "conj_holds : HConj ∧ 1 ≤ 2", "conj_holds : 1 ≤ 1 ∧ 1 ≤ 2", None),
    ("A ↔ exclusion: iff producer becomes a direct producer", "Salt/Fx/Main.lean",
     "iff_only : HIff ↔ True := by simp [HIff]", "iff_only : HIff := fun x => rfl", None),
    ("A one-level ∧: nested producer flattened", "Salt/Fx/Main.lean",
     "(HNested ∧ True) ∧ True", "HNested ∧ True ∧ True", None),
    ("A conditional producer: its binder is dropped", "Salt/Fx/Main.lean",
     "cp (h : HOpen) : HCondProd", "cp : HCondProd", None),
    ("A OPEN arm: an unconditional producer appears", "Salt/Fx/Main.lean",
     "end Salt.Fx", "theorem hopen_holds : HOpen := fun x => ⟨x + 1, Nat.lt_succ_self x⟩\nend Salt.Fx", None),
    ("A STRUCTURAL body rule: quantifier unbounded", "Salt/Fx/Defs.lean",
     "∀ n ∈ A, n ≠ 0", "∀ n, n ∈ A → n ≠ 0 ∧ ∃ m, m < n", None),
    ("A ∃ exclusion: witness producer becomes direct", "Salt/Fx/Main.lean",
     "wit : ∃ c : ℕ, 0 ≤ c ∧ HWit c", "wit : HWit 0", None),
    ("A STRUCTURAL (vi): body calls a corpus function", "Salt/Fx/Defs.lean",
     "∀ n ∈ A, n ≠ 0", "∀ n ∈ A, fxw n ≠ 0", None),
    ("A STRUCTURAL use rule: its only user removed", "Salt/Fx/Main.lean",
     "theorem top_c (h : HStruct 3 ∅) : True", "theorem top_c : True", None),
    ("A FRAME (iii): a non-allow-listed corpus name enters the frame", "Salt/Fx/Defs.lean",
     "X_three : (3 : ℝ) ≤ (X : ℝ)", "X_three : (3 : ℝ) ≤ (fxw X : ℝ)", None),
    ("A FRAME fixpoint: the gate stops being a frame", "Salt/Fx/Defs.lean",
     "Real.exp (30 * Real.log x) ≤ T", "∃ y : ℝ, Real.exp (30 * Real.log x) ≤ y + T", None),
    ("A FRAME (ii): a field that is not an order relation", "Salt/Fx/Defs.lean",
     "4 ≤ 2 ^ j ∧ j ≠ 0", "4 ≤ 2 ^ j ∧ Nat.Prime j", None),
    ("A FRAME socket: its corpus call removed (becomes a frame)", "Salt/Fx/Defs.lean",
     "fxw (b n) ≤ R", "b n ≤ R", None),
    ("B direct-ref arm: top_b's reference removed", "Salt/Fx/Main.lean",
     "top_b : 2 ≤ 3 := Salt.Entropy.ent_core", "top_b : 2 ≤ 3 := by norm_num", None),
    ("B open-resolution arm: `open` dropped", "Salt/Fx/Main.lean", "open Salt.Entropy\n", "\n", None),
    ("B transitive arm: middle link cut", "Salt/Entropy/Fx.lean",
     "ent_uses_ls : 1 ≤ 2 := Salt.LS.ls_core", "ent_uses_ls : 1 ≤ 2 := by norm_num", None),
    ("B comment stripping: commented ref made live", "Salt/Fx/Main.lean",
     "  -- Salt.LS.ls_core in a comment must not count\n", "  have := Salt.LS.ls_core\n", None),
    ("B family map: entropy path rule removed", None, None, None,
     lambda: _fam_without("entropy decrement", "paths", "Salt/Entropy/")),
    ("B in-degree arm: an extra audited dependent", "Salt/Fx/Main.lean",
     "theorem top_d (h : HOpen) : True := trivial", "theorem top_d (h : HOpen) : True := (fun _ => trivial) Salt.LS.ls_core", None),
]


def self_test() -> int:
    errs = check_fixture(dict(FIXTURE))
    if errs:
        print("SELF-TEST FAIL (clean fixture):"); [print("  " + e) for e in errs]; return 1
    print("clean fixture: %d statuses + %d graph rows as expected" % (len(EXPECT_STATUS), len(EXPECT_GRAPH)))
    killed = 0
    for label, f, old, new, fam in MUTANTS:
        fx = dict(FIXTURE)
        if f:
            assert old in fx[f], "mutant anchor missing: " + label
            fx[f] = fx[f].replace(old, new, 1)
        e = check_fixture(fx, fam() if fam else None)
        killed += bool(e)
        print("  mutant %-56s %s%s" % (label[:56], "KILLED" if e else "SURVIVED", (" (" + e[0][:70] + ")") if e else ""))
    print("mutants killed: %d / %d" % (killed, len(MUTANTS)))
    return 0 if killed == len(MUTANTS) else 1


def main(argv):
    if "--self-test" in argv: return self_test()
    page, tsv, B = generate()
    if "--check" in argv:
        bad = []
        for P, want in CONTROLS:
            if B["status"].get(P) != want:
                bad.append("control %s is %s, want %s" % (P, B["status"].get(P), want))
        for p, want in ((PAGE, page), (TSV, tsv)):
            try:
                cur = open(os.path.join(REPO, p), encoding="utf-8").read()
            except OSError:
                cur = None
            if cur != want: bad.append(p)
        if bad:
            print("STALE: %s differ(s) from a fresh generation; run `%s`" % (", ".join(bad), COMMAND)); return 1
        print("OK: %s and %s are current" % (PAGE, TSV)); return 0
    if "--stdout" in argv:
        sys.stdout.write(page); return 0
    for p, t in ((PAGE, page), (TSV, tsv)):
        with open(os.path.join(REPO, p), "w", encoding="utf-8") as fh: fh.write(t)
    s = B["status"]
    print("wrote %s (%d B) + %s (%d B): %s · %s" % (PAGE, len(page.encode()), TSV, len(tsv.encode()),
                                                  " ".join("%s=%d" % (k, sum(1 for v in s.values() if v == k))
                                                           for k in STATUSES),
                                                  " ".join("%s=%s" % kv for kv in B["receipt"].items())))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
