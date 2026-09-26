#!/usr/bin/env python3
"""THE TACTICS CATALOGUE, BY MACHINE (objective O13, item 4).

Built ON TOP of items 1-2: item 1's parser (`results_catalogue`: comment stripping, the declaration
index, namespace/`open` resolution) and item 2's proof-body attachment and FAMILY map
(`methods_catalogue`) are IMPORTED, never forked. Source-level, stdlib only, no Lean.

PART 1 -- THE LEDGER'S STATUS BY MACHINE. For each candidate T1..T10 of `docs/blueprints/tactics.md`:
  ledger-says   the section's own words (LANDED / HARVESTED / PROBE RESULT / none), and the module
                paths it names;
  machine-says  which `Salt/Tactic/*.lean` modules exist and claim it (named by the ledger section,
                by the module's own header `ledger T<n>`, or by `Salt/Tactic/All.lean`'s docstring),
                their PUBLIC surface (non-private theorem/lemma/def/abbrev under `Salt.`, or, for a
                metaprogram module, its `macro`/`syntax`/`elab` keywords), and ADOPTION: the number
                of proof-body call sites of each surface name OUTSIDE `Salt/Tactic/`, with the form
                that reached it (qualified · namespace-relative · opened) and the files.
PART 2 -- TACTIC USAGE: the first token of each tactic line (inside a `by`, from a WHITELIST that is
          data), over the corpus and per method FAMILY (item 2's map).
PART 3 -- MACRO CANDIDATES: runs of >= 3 consecutive tactic lines, normalised (indentation stripped,
          local names -> $1,$2,... by first appearance, numerals -> #, lemma names kept), exact
          repeats counted; blocks repeated >= MIN_OCC times in >= MIN_FILES files, maximal only.

Usage:
  python3 scripts/tactics_catalogue.py              write docs/TACTICS-CATALOGUE.md
  python3 scripts/tactics_catalogue.py --stdout     print the page instead
  python3 scripts/tactics_catalogue.py --check      exit 1 if the page is stale or a control fails
  python3 scripts/tactics_catalogue.py --self-test  run the fixture and the per-arm mutants
"""
from __future__ import annotations

import os
import re
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import results_catalogue as rc  # noqa: E402  (item 1: the parser)
import methods_catalogue as mc  # noqa: E402  (item 2: proof bodies + the family map)

REPO = rc.REPO
PAGE = os.path.join("docs", "TACTICS-CATALOGUE.md")
LEDGER = os.path.join("docs", "blueprints", "tactics.md")
COMMAND = "python3 scripts/tactics_catalogue.py"
TAC_DIR = "Salt/Tactic/"

# ---------------------------------------------------------------- DATA (choices, printed on the page)
# metaprogram modules: their `def`s are implementation, the surface is the syntax they declare.
IMPL_ONLY = ("Salt/Tactic/AuditAxioms.lean", "Salt/Tactic/NlinarithSuggest.lean")
# the first-token whitelist that makes a line a TACTIC line (a line whose first token is not here is a
# term continuation, a pattern, or something this list does not know -- it is not counted).
TACTICS = sorted(set("""
simp simp_all simp_rw simpa dsimp simp? simpa? simp_arith norm_num norm_num1 linarith linarith! nlinarith
nlinarith! nlinarith? positivity omega field_simp ring ring_nf ring1 gcongr gcongr? exact_mod_cast push_cast
norm_cast assumption_mod_cast rw rwa erw rw? nth_rewrite nth_rw rewrite exact exacts exact? apply apply?
refine refine' intro intros rintro obtain rcases rsuffices have haveI show calc constructor use existsi
exists unfold unfold_let delta split_ifs split by_cases by_contra by_contra! push_neg contrapose contrapose!
exfalso induction induction' cases cases' interval_cases fin_cases decide rfl trivial tauto aesop
filter_upwards congr congr! congrm ext funext specialize set let letI generalize subst subst_vars convert
convert_to change apply_fun mono bound polyrith linear_combination abel group noncomm_ring zify qify lift
left right symm trans assumption contradiction absurd suffices clear rename_i next case all_goals any_goals
first try repeat iterate swap rotate_left pick_goal on_goal focus with_reducible apply_rules measurability
continuity fun_prop infer_instance classical rel choose wlog and_intros refine_lift cancel_denoms conv
conv_lhs conv_rhs mod_cast split_ands norm_num? sorry skip done stop native_decide exact_fun_prop
eventually_budget nlinarith? field_simp? positivity? unfold? bound? calc? gcongr_discharger
""".split()))
TACSET = frozenset(TACTICS)
MIN_BLOCK, MAX_BLOCK, MIN_OCC, MIN_FILES = 3, 20, 5, 3
TOP_KEYWORDS, TOP_FAMILY_KW, TOP_BLOCKS = 30, 8, 25

# positive controls (the seat's measurement at main 1a5e85e1: `git grep -c -F Salt.Tactic.<name>`
# outside Salt/Tactic, summed = 24). --check asserts each qualified count is >= 1 and the page prints
# the live numbers beside the base values; the self-test's fixture pins exact arithmetic.
CONTROLS_AT_BASE = (("Salt.Tactic.le_exp_nat_of_le_pow", 11), ("Salt.Tactic.exp_nat_le_of_pow_le", 4),
                    ("Salt.Tactic.log_le_nat_of_le_pow", 5), ("Salt.Tactic.nat_le_log_of_pow_le", 4))
AUDIT_FLOOR = 1000   # --check: `#audit_axioms` must audit at least this many identifiers in All.lean ledgers

TOKEN_RE = re.compile(r"(?:(?<![\w'!?.])(\d+(?:\.\d+)?)(?![\w.]))|(" + rc.IDENT_RE.pattern + ")")
FIRST_TOK_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")
SYNTAX_RE = re.compile(r"^(?:macro|syntax|elab)\b[^\"\n]*\"([^\"]+)\"", re.M)
HYP_RE = re.compile(r"^[hH][A-Za-z0-9_'₀-₉ₐ-ₜ]*$")
OPEN_IN_RE = re.compile(r"^open\s+(.*?)\s+in\s*$")
KEEP_WORDS = frozenset(rc.KEYWORDS) | TACSET | {"this", "only", "using", "at", "with", "fun", "by", "then",
                                                  "else", "if", "true", "false", "True", "False", "rfl", "ℝ", "ℕ", "ℤ", "ℚ", "ℂ", "_"}


# ---------------------------------------------------------------- corpus
def load(files: dict):
    decls: dict = {}
    for p in sorted(files): rc.index_file(p, files[p], decls, {})
    mc.attach_bodies(files, decls)
    stripped = {p: rc.strip_comments(files[p]) for p in files}
    # proof-body start line + `open … in` prefixes (item 1 skips `open … in`; the NEXT command sees it)
    for d in decls.values():
        text = stripped[d.path]
        lines = text.split("\n")
        k, extra = d.line - 2, []
        while k >= 0:
            st = lines[k].strip()
            m = OPEN_IN_RE.match(st)
            if m: extra.extend(t for t in m.group(1).split() if rc.IDENT_RE.fullmatch(t))
            elif not (st == "" or st.startswith("@[") or st.startswith("set_option")): break
            k -= 1
        d.opens_in = extra
        d.body_line = None
        if d.proof:
            off = sum(len(x) + 1 for x in lines[:d.line - 1])
            i = text.find(d.proof, off)
            if i >= 0: d.body_line = text.count("\n", 0, i) + 1
    return decls, stripped


def is_private(d, files) -> bool:
    ln = files[d.path].split("\n")[d.line - 1]
    return bool(re.search(r"\bprivate\b", ln[:ln.find(d.short)] if d.short in ln else ln))


# ---------------------------------------------------------------- PART 1: the ledger
def parse_ledger(md: str):
    """[(id, header-name, says, paths)] for every `## T<n>` / `### T<n>` section."""
    heads = list(re.finditer(r"^#{2,3}\s+(T\d+)\b(.*)$", md, re.M))
    out = []
    for i, m in enumerate(heads):
        end = heads[i + 1].start() if i + 1 < len(heads) else len(md)
        nxt = re.search(r"^#{2,3}\s+(?!T\d)", md[m.end():end], re.M)
        sec = md[m.start(): m.end() + nxt.start() if nxt else end]
        name = re.search(r"`([^`]+)`", m.group(2))
        says = [w for w in ("LANDED", "HARVESTED", "PROBE RESULT", "NOT USED", "NOT-YET") if w in sec]
        paths = sorted(set(re.findall(r"Salt/Tactic/\w+\.lean", sec)))
        bnames = re.findall(r"^- \*\*`([^`]+)`", sec, re.M)
        out.append((m.group(1), name.group(1) if name else "", says, paths, bnames))
    return out


def module_claims(files: dict, ledger_rows):
    """module path -> {T-id: set(sources)}."""
    mods = sorted(p for p in files if p.startswith(TAC_DIR) and p != TAC_DIR + "All.lean")
    claims = {p: defaultdict(set) for p in mods}
    for tid, _, _, paths, _ in ledger_rows:
        for p in paths:
            if p in claims: claims[p][tid].add("ledger")
    for p in mods:
        head = files[p][:4000]
        for t in re.findall(r"ledger\s+(T\d+)", head): claims[p][t].add("header")
    alltext = files.get(TAC_DIR + "All.lean", "")
    for p in mods:
        base = os.path.basename(p)[:-5]
        for m in re.finditer(r"`%s`\s*\(((?:T\d+)(?:/T\d+)*)" % re.escape(base), alltext):
            for t in m.group(1).split("/"): claims[p][t].add("All.lean")
    return claims


def surface(files, decls, path):
    """(names, syntax keywords) a consumer can call."""
    raw, st = files[path].split("\n"), rc.strip_comments(files[path]).split("\n")
    kws = [m.group(1) for i, ln in enumerate(raw) for m in [SYNTAX_RE.match(ln)]
           if m and re.match(r"(?:macro|syntax|elab)\b", st[i])]
    if path in IMPL_ONLY: return [], kws
    names = sorted(d.name for d in decls.values()
                   if d.path == path and d.name.startswith("Salt.") and ".Tests." not in d.name
                   and d.kw in ("theorem", "lemma", "def", "abbrev") and not is_private(d, files))
    return names, kws


def resolve_form(tok, d, universe):
    """(full name, form) or (None, None). Forms: qualified · namespace-relative · opened."""
    opens = list(d.opens) + list(d.opens_in)
    full = rc.resolve(tok, d.ns, opens, universe)
    if full is None: return None, None
    if tok == full: return full, "qualified"
    for k in range(len(d.ns), -1, -1):
        if ".".join(d.ns[:k] + [tok]) == full: return full, "namespace-relative"
    return full, "opened"


def adoption(decls, stripped, surf_names, surf_kws, resolve=None):
    """name -> {"sites": n, "forms": Counter, "files": Counter}; kw likewise; audit summary."""
    resolve = resolve or resolve_form
    shorts = defaultdict(set)
    for n in surf_names: shorts[n.rsplit(".", 1)[-1]].add(n)
    res = {n: dict(sites=0, forms=Counter(), files=Counter()) for n in list(surf_names) + list(surf_kws)}
    kwset = set(surf_kws) - {"#audit_axioms"}
    for d in decls.values():
        if d.path.startswith(TAC_DIR) or not d.proof: continue
        for m in rc.IDENT_RE.finditer(d.proof):
            tok = m.group(0)
            last = tok.rsplit(".", 1)[-1]
            if last in shorts:
                full, form = resolve(tok, d, decls)
                if full in res and full in surf_names:
                    r = res[full]; r["sites"] += 1; r["forms"][form] += 1; r["files"][d.path] += 1
            if kwset:
                for kw in kwset:
                    if tok == kw or (tok.startswith(kw) and tok[len(kw):] in ("!",)):
                        r = res[kw]; r["sites"] += 1; r["forms"]["syntax"] += 1; r["files"][d.path] += 1
    audit = dict(commands=0, idents=0, ledger_commands=0, ledger_idents=0, files=Counter())
    if "#audit_axioms" in surf_kws:
        for p, text in stripped.items():
            if p.startswith(TAC_DIR): continue
            for m in re.finditer(r"#audit_axioms\b", text):
                j, n = m.end(), 0
                while True:
                    mm = re.compile(r"\s*(" + rc.IDENT_RE.pattern + r")").match(text, j)
                    if not mm or mm.group(1) in rc.KEYWORDS or mm.group(1).startswith("#"): break
                    n += 1; j = mm.end()
                led = bool(re.search(r"(^|/)All\.lean$", p))
                audit["commands"] += 1; audit["idents"] += n; audit["files"][p] += 1
                if led: audit["ledger_commands"] += 1; audit["ledger_idents"] += n
        r = res["#audit_axioms"]
        r["sites"] = audit["commands"]; r["forms"]["command"] = audit["commands"]; r["files"] = audit["files"]
    return res, audit


# ---------------------------------------------------------------- PART 2 + 3: tactic lines
def tactic_lines(d):
    """[(file line, first token, stripped text)] for lines of d.proof from the first `by` on;
    first token None = not a tactic line; blank lines are skipped (they neither count nor break)."""
    if not d.proof or d.body_line is None: return []
    m = re.search(r"(?<![\w.])by\b", d.proof)
    if not m: return []
    out = []
    pre = d.proof[:m.start()].count("\n")
    seg = d.proof[m.end():]
    for i, raw in enumerate(seg.split("\n")):
        st = raw.strip()
        if not st: continue
        body = re.sub(r"^(?:[·.]\s*|<;>\s*)+", "", st)
        f = FIRST_TOK_RE.match(body)
        tok = f.group(0) if f and f.group(0) in TACSET else None
        out.append((d.body_line + pre + i, tok, st))
    return out


def local_names(d) -> set:
    loc = set()
    bs, _ = rc.parse_binders(d.stmt)
    for _, names, _ in bs + list(getattr(d, "vars", [])):
        loc.update(n for n in names if rc.IDENT_RE.fullmatch(n))
    body = d.proof or ""
    for m in re.finditer(r"\b(?:have|haveI|let|letI|set|generalize)\s+(" + rc.IDENT_RE.pattern + ")", body):
        loc.add(m.group(1))
    for m in re.finditer(r"\b(?:intro|intros|rintro|obtain|rcases|choose|rename_i|next|case|cases'|induction'"
                         r"|fun)\b([^\n:=]*)", body):
        for t in rc.IDENT_RE.findall(m.group(1)): loc.add(t)
    for m in re.finditer(r"\bwith\b([^\n]*)", body):
        for t in rc.IDENT_RE.findall(m.group(1)): loc.add(t)
    return loc - KEEP_WORDS


def norm_tokens(text, loc, universe):
    """[(kind, value)] with kind in {'lit','loc','num'}."""
    out, j = [], 0
    for m in TOKEN_RE.finditer(text):
        out.append(("lit", re.sub(r"\s+", " ", text[j:m.start()])))
        if m.group(1):
            out.append(("num", "#"))
        else:
            tok = m.group(2)
            head, _, rest = tok.partition(".")
            if head in KEEP_WORDS or tok in universe:
                out.append(("lit", tok))
            elif head in loc or (HYP_RE.match(head) and len(head) <= 12) or (len(head) <= 2 and "_" not in head):
                out.append(("loc", head)); out.append(("lit", ("." + rest) if rest else ""))
            else:
                out.append(("lit", tok))
        j = m.end()
    out.append(("lit", re.sub(r"\s+", " ", text[j:])))
    return out


def render_block(toklines, mapping):
    s = []
    for toks in toklines:
        parts = []
        for k, v in toks:
            if k == "loc":
                if v not in mapping: mapping[v] = "$%d" % (len(mapping) + 1)
                parts.append(mapping[v])
            else:
                parts.append(v)
        s.append("".join(parts).strip())
    return "\n".join(s)


def usage_and_blocks(decls, fams, universe):
    kw_all, kw_fam = Counter(), defaultdict(Counter)
    runs = []   # (path, [(line, toks)])
    for d in decls.values():
        tl = tactic_lines(d)
        if not tl: continue
        fset = fams(d)
        loc = None
        cur = []
        for ln, tok, st in tl:
            if tok is None:
                if len(cur) >= MIN_BLOCK: runs.append((d.path, cur))
                cur = []; continue
            kw_all[tok] += 1
            for f in (fset or (-1,)): kw_fam[f][tok] += 1
            if loc is None: loc = local_names(d)
            cur.append((ln, norm_tokens(st, loc, universe)))
        if len(cur) >= MIN_BLOCK: runs.append((d.path, cur))
    return kw_all, kw_fam, runs


def find_blocks(runs):
    """Maximal normalised blocks repeated >= MIN_OCC times in >= MIN_FILES files."""
    # level k: key -> [(run, start)] ; grow only from qualifying (k-1)-prefixes
    def qualifies(occ): return len(occ) >= MIN_OCC and len({runs[r][0] for r, _ in occ}) >= MIN_FILES

    def add(table, key, r, s, k, last):
        if last.get((key, r), -1) > s: return          # non-overlapping within one run
        table[key].append((r, s)); last[(key, r)] = s + k

    level, keyat, allq = {}, {}, {}
    table, last = defaultdict(list), {}
    for r, (_, lines) in enumerate(runs):
        for s in range(len(lines) - MIN_BLOCK + 1):
            key = render_block([t for _, t in lines[s:s + MIN_BLOCK]], {})
            add(table, key, r, s, MIN_BLOCK, last)
    level = {k: v for k, v in table.items() if qualifies(v)}
    k = MIN_BLOCK
    while level:
        for key, occ in level.items():
            allq[(key, k)] = occ
            for r, s in occ: keyat[(r, s, k)] = key
        if k == MAX_BLOCK: break
        k += 1
        table, last = defaultdict(list), {}
        for key, occ in level.items():
            for r, s in occ:
                lines = runs[r][1]
                if s + k > len(lines): continue
                nk = render_block([t for _, t in lines[s:s + k]], {})
                add(table, nk, r, s, k, last)
        level = {kk: v for kk, v in table.items() if qualifies(v)}
    subsumed = set()
    for (key, kk), occ in allq.items():
        if kk == MIN_BLOCK: continue
        for dl in (0, 1):   # right-trim (same start) / left-trim (start+1)
            subs = Counter(keyat.get((r, s + dl, kk - 1)) for r, s in occ)
            for sk, c in subs.items():
                if sk is not None and len(allq.get((sk, kk - 1), ())) == c: subsumed.add((sk, kk - 1))
    out = []
    for (key, kk), occ in allq.items():
        if (key, kk) in subsumed: continue
        files = sorted({runs[r][0] for r, _ in occ})
        ex = [(runs[r][0], runs[r][1][s][0]) for r, s in occ]
        ex = sorted(ex, key=lambda e: (e[0], e[1]))
        exs = [ex[0]] + [e for e in ex if e[0] != ex[0][0]][:1]
        cov = {(runs[r][0], runs[r][1][s + i][0]) for r, s in occ for i in range(kk)}
        out.append(dict(key=key, k=kk, occ=len(occ), files=len(files), save=(kk - 1) * len(occ), ex=exs, cov=cov))
    out.sort(key=lambda b: (-b["save"], -b["occ"], b["key"]))
    return out


# ---------------------------------------------------------------- build + render
def build(files: dict, ledger_md: str, fams=None, resolve=None):
    decls, stripped = load(files)
    fams = fams or (lambda d: mc.family_of(d))
    rows = parse_ledger(ledger_md)
    claims = module_claims(files, rows)
    surf = {p: surface(files, decls, p) for p in claims}
    all_names = [n for p in surf for n in surf[p][0]]
    all_kws = [k for p in surf for k in surf[p][1]]
    adopt, audit = adoption(decls, stripped, all_names, all_kws, resolve)
    header_found = {}
    alln = {d.short for d in decls.values()} | {d.name for d in decls.values()}
    mods = {os.path.basename(p)[:-5] for p in files if p.endswith(".lean")}
    for tid, hname, _, _, bnames in rows:
        for nm in ([hname] if hname else []) + bnames:
            header_found[nm] = (nm in alln or nm in all_kws or nm in mods
                                or nm[:1].upper() + nm[1:] in mods)
    kw_all, kw_fam, runs = usage_and_blocks(decls, fams, decls)
    blocks = find_blocks(runs)
    ntac = sum(kw_all.values())
    receipt = dict(files=len(files), decls=len(decls), with_body=sum(1 for d in decls.values() if d.proof.strip()),
                   tactic_lines=ntac, runs=len(runs), blocks=len(blocks))
    return dict(rows=rows, claims=claims, surf=surf, adopt=adopt, audit=audit, header_found=header_found,
                kw_all=kw_all, kw_fam=kw_fam, blocks=blocks, receipt=receipt, decls=decls)


def _files_str(c: Counter, cap=4):
    items = sorted(c.items(), key=lambda kv: (-kv[1], kv[0]))
    s = ", ".join("`%s` %d" % (p.replace("Salt/", "", 1), n) for p, n in items[:cap])
    return s + (" (+%d files)" % (len(items) - cap) if len(items) > cap else "") if items else "-"


def render(B, base: str, digest: str) -> str:
    L = []
    rcp = B["receipt"]
    L.append("# THE TACTICS CATALOGUE — by machine (O13 item 4)")
    L.append("")
    L.append("> **GENERATED — do not edit by hand.** Regenerate: `%s` · staleness gate: `%s --check`." % (COMMAND, COMMAND))
    L.append("> Base: last commit touching `Salt/` = `%s` · source digest `%s` (the same digest as items 1–3)." % (base, digest))
    L.append("> Receipt: %s." % " · ".join("%s %d" % kv for kv in rcp.items()))
    L.append("")
    L.append("## LIMITS (read before any number below)")
    L.append("")
    L.append("- **Source-level, no Lean.** Names are resolved by item 1's namespace/`open` rules plus the `open … in` lines "
             "directly above a declaration; `export`, `alias`, notation, `simp` sets and macro expansion are NOT followed. "
             "A call that reaches a lemma through another lemma, a `simp [..]` set built elsewhere, or a local `have` alias "
             "is not a site.")
    L.append("- **Adoption counts proof-body TOKENS** (item 2's body: statement end → next command), comments and strings "
             "stripped, OUTSIDE `Salt/Tactic/`. A statement that merely mentions a name is not a site; two uses on one line "
             "are two sites (a `git grep -c` counts lines, so the two can differ).")
    L.append("- **A tactic line is a line whose first token is in the WHITELIST below** (data, a choice), from the first "
             "`by` of a body onward. Term-mode continuation lines, `⟨…⟩` pieces and tactics absent from the list are not "
             "counted, so Part 2 is a LOWER bound per keyword and says nothing about tactics it does not list.")
    L.append("- **Macro candidates are PRICED AS AN UPPER BOUND.** Lines saved = (block lines − 1) × occurrences assumes "
             "every occurrence collapses to ONE line. A macro call is ≥ 1 line, a block whose placeholders bind "
             "differently at two sites may not share one macro, and a block of generic tactics (`norm_num`, `linarith`) may "
             "be cheaper to leave than to name (the O15 lesson: span-2 sites saved nothing). Local-name detection is "
             "heuristic (binders, `have/obtain/intro/…` patterns, `h…` names, ≤ 2-char names); a missed local makes two "
             "equal blocks look different (under-count), a lemma mistaken for a local merges two different blocks "
             "(over-count).")
    L.append("- **Candidates OVERLAP and their savings are NOT additive:** a region repeated at several lengths yields "
             "several maximal blocks (a longer block with fewer occurrences is a different candidate); each entry names "
             "the earlier entries it shares source lines with. Many top candidates are `have`-chains that NAME facts "
             "used later; a hygienic macro cannot introduce those names, so their natural capture is a LEMMA returning "
             "the facts (still ≥ 1 line plus a destructuring), not a tactic macro.")
    L.append("- Per-family numbers use item 2's FAMILY map (a CHOICE, printed on `docs/METHODS-CATALOGUE.md`); a "
             "declaration in several families counts in each, and `(no family)` collects the rest.")
    L.append("")

    # PART 1
    L.append("## 1. The ledger's status, by machine")
    L.append("")
    L.append("Ledger: `%s`. Module claims come from three sources: the ledger section naming the path (`ledger`), the "
             "module's own header `ledger T<n>` (`header`), and `Salt/Tactic/All.lean`'s docstring (`All.lean`)." % LEDGER)
    L.append("")
    L.append("| id | ledger names | ledger says | ledger's paths | machine: modules claiming it (sources) | machine: header name(s) present in `Salt/`? |")
    L.append("|---|---|---|---|---|---|")
    for tid, hname, says, paths, bnames in B["rows"]:
        mods = ["`%s` (%s)" % (p.replace(TAC_DIR, ""), ", ".join(sorted(B["claims"][p][tid])))
                for p in sorted(B["claims"]) if tid in B["claims"][p]]
        missing = [p for p in paths if p not in B["claims"]]
        names = ([hname] if hname else []) + bnames
        L.append("| %s | %s | %s | %s | %s | %s |" % (
            tid, ", ".join("`%s`" % n for n in names) or "-", " · ".join(says) or "(no status word)",
            ", ".join("`%s`%s" % (p.replace(TAC_DIR, ""), " ⛔ NOT ON DISK" if p in missing else "") for p in paths) or "-",
            "; ".join(mods) or "**none**",
            ", ".join("`%s` %s" % (n, "yes" if B["header_found"].get(n) else "**no**") for n in names) or "-"))
    L.append("")
    unclaimed = [p for p in sorted(B["claims"]) if not any("ledger" in s for s in B["claims"][p].values())]
    if unclaimed:
        L.append("⚠️ **Modules on disk that NO ledger section names by path:** %s — their T-id comes only from their own "
                 "header or `All.lean`." % ", ".join("`%s`" % p for p in unclaimed))
        L.append("")
    L.append("### Adoption per landed surface (call sites outside `Salt/Tactic/`)")
    L.append("")
    L.append("| module | T | surface name | sites | forms | files |")
    L.append("|---|---|---|---:|---|---|")
    zero = []
    for p in sorted(B["surf"]):
        names, kws = B["surf"][p]
        tids = ",".join(sorted(B["claims"][p])) or "-"
        for n in list(names) + list(kws):
            a = B["adopt"][n]
            if a["sites"] == 0: zero.append(n)
            forms = ", ".join("%s %d" % kv for kv in sorted(a["forms"].items())) or "-"
            L.append("| `%s` | %s | `%s` | %d | %s | %s |" % (p.replace(TAC_DIR, ""), tids, n, a["sites"], forms,
                                                           _files_str(a["files"])))
    L.append("")
    au = B["audit"]
    L.append("`#audit_axioms` in detail: **%d commands auditing %d identifiers** across %d files; in the `All.lean` "
             "ledgers **%d commands, %d identifiers**." % (au["commands"], au["idents"], len(au["files"]),
                                                            au["ledger_commands"], au["ledger_idents"]))
    L.append("")
    L.append("**Landed surface with ZERO call sites outside `Salt/Tactic/` (%d) — each is a finding, not a defect of the "
             "count:** %s" % (len(zero), ", ".join("`%s`" % z for z in zero) or "none"))
    L.append("")
    L.append("**Positive controls (the seat's measurement at main `1a5e85e1`: `git grep -c -F` per qualified name outside "
             "`Salt/Tactic`, summed = 24):**")
    L.append("")
    L.append("| name | at base (seat, lines) | here: qualified tokens | here: all forms |")
    L.append("|---|---:|---:|---:|")
    for n, want in CONTROLS_AT_BASE:
        a = B["adopt"].get(n, dict(sites=0, forms=Counter()))
        L.append("| `%s` | %d | %d | %d |" % (n, want, a["forms"].get("qualified", 0), a["sites"]))
    L.append("")

    # PART 2
    L.append("## 2. Tactic usage (first token of each tactic line)")
    L.append("")
    tot = sum(B["kw_all"].values())
    L.append("%d tactic lines. Top %d:" % (tot, TOP_KEYWORDS))
    L.append("")
    L.append("| # | tactic | lines | share |")
    L.append("|---:|---|---:|---:|")
    for i, (k, v) in enumerate(sorted(B["kw_all"].items(), key=lambda kv: (-kv[1], kv[0]))[:TOP_KEYWORDS], 1):
        L.append("| %d | `%s` | %d | %.1f%% |" % (i, k, v, 100.0 * v / tot if tot else 0))
    L.append("")
    L.append("### Per method family (top %d each)" % TOP_FAMILY_KW)
    L.append("")
    L.append("| family | tactic lines | top tactics |")
    L.append("|---|---:|---|")
    names = mc.FAMILY_NAMES
    for f in list(range(len(names))) + [-1]:
        c = B["kw_fam"].get(f, Counter())
        n = sum(c.values())
        top = ", ".join("`%s` %d" % kv for kv in sorted(c.items(), key=lambda kv: (-kv[1], kv[0]))[:TOP_FAMILY_KW])
        L.append("| %s | %d | %s |" % (names[f] if f >= 0 else "(no family)", n, top or "-"))
    L.append("")

    # PART 3
    L.append("## 3. Macro candidates (repeated normalised tactic blocks)")
    L.append("")
    L.append("Blocks of %d–%d consecutive tactic lines, repeated ≥ %d times (non-overlapping) in ≥ %d files, maximal "
             "only (a block is dropped when a one-line-longer block has exactly its occurrences). `$n` = a local name "
             "(numbered by first appearance, so equal blocks bind alike), `#` = a numeral. %d candidates; top %d by the "
             "UPPER-BOUND saving." % (MIN_BLOCK, MAX_BLOCK, MIN_OCC, MIN_FILES, len(B["blocks"]), TOP_BLOCKS))
    L.append("")
    L.append("⚠️ **Lines saved is an UPPER bound, never a price:** a macro call is ≥ 1 line; sites whose placeholders "
             "bind differently may not share a macro; generic blocks may cost more to name than to repeat.")
    L.append("")
    shown = B["blocks"][:TOP_BLOCKS]
    for i, b in enumerate(shown, 1):
        ov = [str(j) for j, c in enumerate(shown[:i - 1], 1) if b["cov"] & c["cov"]]
        L.append("**%d.** %d lines × %d occurrences in %d files · lines saved ≤ **%d** · e.g. %s%s" % (
            i, b["k"], b["occ"], b["files"], b["save"], " · ".join("`%s:%d`" % e for e in b["ex"]),
            (" · ⚠️ shares source lines with #%s" % ", #".join(ov)) if ov else ""))
        L.append("")
        L.append("```lean")
        for ln in b["key"].split("\n"): L.append(ln[:160])
        L.append("```")
        L.append("")
    L.append("## Whitelist (data)")
    L.append("")
    L.append(" ".join("`%s`" % t for t in TACTICS))
    L.append("")
    L.append("Metaprogram modules whose surface is their SYNTAX only (their `def`s are implementation): %s." %
             ", ".join("`%s`" % p for p in IMPL_ONLY))
    L.append("")
    return "\n".join(L)


def generate():
    files, _, digest = rc.load_repo()
    with open(os.path.join(REPO, LEDGER), encoding="utf-8") as fh: md = fh.read()
    B = build(files, md)
    base = rc.git("log", "-1", "--format=%h", "--", "Salt") or "unknown"
    return render(B, base, digest), B


# ---------------------------------------------------------------- self-test
FX_LEDGER = """# ledger
### T1 — `foo_tac`: a tactic
**STATUS: LANDED** (`Salt/Tactic/Foo.lean`)
### T2 — `bar_tac`: a candidate
nothing yet
## Other
"""
FX_TAC = '''
/-! header: ledger T1 -/
namespace Salt.Tactic
theorem foo_lemma (n : ℕ) : n ≤ n := le_refl n
private theorem hidden (n : ℕ) : n ≤ n := le_refl n
macro "foo_tac" : tactic => `(tactic| rfl)
elab "#audit_axioms" ids:ident+ : command => pure ()
end Salt.Tactic
'''
FX_A = '''
namespace Salt.A
theorem a1 (x : ℕ) (hx : 0 < x) : x ≤ x := by
  have h1 := Salt.Tactic.foo_lemma x
  -- Salt.Tactic.foo_lemma in a comment is not a site
  exact Salt.Tactic.foo_lemma x
open Salt.Tactic in
theorem a2 (y : ℕ) : y ≤ y := by
  simp only [foo_lemma]
  foo_tac
theorem a3 (z : ℕ) (hz : 0 < z) : z ≤ z + 1 := by
  norm_num
  linarith [hz]
  omega
  simp
theorem a4 (w : ℕ) (hw : 0 < w) : w ≤ w + 2 := by
  norm_num
  linarith [hw]
  omega
  simp
end Salt.A
'''
FX_B = '''
namespace Salt.B
theorem b1 (u : ℕ) (hu : 0 < u) : u ≤ u + 3 := by
  norm_num
  linarith [hu]
  omega
  ring
theorem b2 (v : ℕ) (hv : 0 < v) : v ≤ v + 4 := by
  norm_num
  linarith [hv]
  omega
  ring
end Salt.B
'''
FX_C = '''
namespace Salt.C
theorem c1 (s : ℕ) (hs : 0 < s) : s ≤ s + 5 := by
  norm_num
  linarith [hs]
  omega
#audit_axioms c1 Salt.C.c1
end Salt.C
'''
FIXTURE = {"Salt/Tactic/Foo.lean": FX_TAC, "Salt/A.lean": FX_A, "Salt/B.lean": FX_B, "Salt/C/All.lean": FX_C}
EXPECT = dict(foo_sites=3, foo_qualified=2, foo_opened=1, foo_tac_sites=1, norm_num=5, linarith=5, omega=5,
              simp=3, block_occ=5, block_files=3, block_k=3, surface=["Salt.Tactic.foo_lemma"])


def check_fixture(fx, ledger=FX_LEDGER, resolve=None, tweak=None) -> list:
    saved = {}
    if tweak:
        for k, v in tweak.items(): saved[k] = globals()[k]; globals()[k] = v
    try:
        B = build(fx, ledger, fams=lambda d: frozenset(), resolve=resolve)
    finally:
        for k, v in saved.items(): globals()[k] = v
    e = []
    a = B["adopt"].get("Salt.Tactic.foo_lemma", dict(sites=-1, forms=Counter()))
    got = dict(foo_sites=a["sites"], foo_qualified=a["forms"].get("qualified", 0), foo_opened=a["forms"].get("opened", 0),
               foo_tac_sites=B["adopt"].get("foo_tac", dict(sites=-1))["sites"],
               norm_num=B["kw_all"]["norm_num"], linarith=B["kw_all"]["linarith"], omega=B["kw_all"]["omega"],
               simp=B["kw_all"]["simp"], surface=B["surf"].get("Salt/Tactic/Foo.lean", ([], []))[0])
    top = B["blocks"][0] if B["blocks"] else dict(occ=0, files=0, k=0)
    got.update(block_occ=top["occ"], block_files=top["files"], block_k=top["k"])
    for k, v in EXPECT.items():
        if got.get(k) != v: e.append("%s = %r, want %r" % (k, got.get(k), v))
    if "T1" not in B["claims"].get("Salt/Tactic/Foo.lean", {}): e.append("ledger claim T1 missing")
    if B["audit"]["ledger_idents"] != 2: e.append("audit idents %d, want 2" % B["audit"]["ledger_idents"])
    return e


def _no_open_resolve(tok, d, universe):
    full = rc.resolve(tok, d.ns, [], universe)
    return (full, "qualified" if full == tok else "namespace-relative") if full else (None, None)


MUTANTS = [
    # (label, arm, fixture edit (file, old, new) or None, code mutant kwargs or None)
    ("adoption: a qualified call dropped", "adoption", ("Salt/A.lean", "exact Salt.Tactic.foo_lemma x", "exact le_refl x"), None),
    ("adoption: resolver ignores `open … in`", "adoption", None, dict(resolve=_no_open_resolve)),
    ("keywords: one `omega` becomes `decide`", "keywords", ("Salt/B.lean", "  omega\n  ring\nend", "  decide\n  ring\nend"), None),
    ("keywords: whitelist loses `linarith`", "keywords", None,
     dict(tweak=dict(TACSET=frozenset(t for t in TACTICS if t != "linarith")))),
    ("blocks: one site's numeral becomes a lemma", "blocks", ("Salt/C/All.lean", "linarith [hs]", "linarith [Nat.zero_le]"), None),
    ("blocks: placeholders disabled (locals kept literal)", "blocks", None,
     dict(tweak=dict(HYP_RE=re.compile(r"^\b$"), KEEP_WORDS=KEEP_WORDS | {"hu", "hv", "hs", "hz", "hw"}))),
]


def self_test() -> int:
    errs = check_fixture(dict(FIXTURE))
    if errs:
        print("SELF-TEST FAIL (clean fixture):"); [print("  " + e) for e in errs]; return 1
    print("clean fixture: %d expectations + ledger claim + audit count as expected" % len(EXPECT))
    killed = 0
    for label, arm, edit, code in MUTANTS:
        fx = dict(FIXTURE)
        if edit:
            f, old, new = edit
            assert old in fx[f], "mutant anchor missing: " + label
            fx[f] = fx[f].replace(old, new, 1)
        e = check_fixture(fx, **(code or {}))
        killed += bool(e)
        print("  [%-8s] mutant %-52s %s%s" % (arm, label[:52], "KILLED" if e else "SURVIVED",
                                             (" (" + e[0][:60] + ")") if e else ""))
    print("mutants killed: %d / %d" % (killed, len(MUTANTS)))
    return 0 if killed == len(MUTANTS) else 1


def main(argv):
    if "--self-test" in argv: return self_test()
    page, B = generate()
    if "--check" in argv:
        bad = []
        for n, _ in CONTROLS_AT_BASE:
            if B["adopt"].get(n, dict(forms=Counter()))["forms"].get("qualified", 0) < 1:
                bad.append("control %s has no qualified site" % n)
        if B["audit"]["ledger_idents"] < AUDIT_FLOOR:
            bad.append("#audit_axioms ledger idents %d < %d" % (B["audit"]["ledger_idents"], AUDIT_FLOOR))
        try:
            cur = open(os.path.join(REPO, PAGE), encoding="utf-8").read()
        except OSError:
            cur = None
        if cur != page: bad.append(PAGE)
        if bad:
            print("STALE/FAIL: %s; run `%s`" % ("; ".join(bad), COMMAND)); return 1
        print("OK: %s is current" % PAGE); return 0
    if "--stdout" in argv:
        sys.stdout.write(page); return 0
    with open(os.path.join(REPO, PAGE), "w", encoding="utf-8") as fh: fh.write(page)
    print("wrote %s (%d B): %s" % (PAGE, len(page.encode()), " · ".join("%s %d" % kv for kv in B["receipt"].items())))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
