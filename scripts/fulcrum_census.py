#!/usr/bin/env python3
"""THE FULCRUM-SHAPE CENSUS, BY MACHINE (objective O13, item 3, first cut).

Built ON TOP of items 1 and 2 (`scripts/results_catalogue.py`, `scripts/methods_catalogue.py`): the
parser, name index, Prop-valued set, binder walk, proof bodies and hypothesis STATUS are IMPORTED,
never forked. This script adds one thing: POLARITY. For every corpus Prop-valued name P (item 1's
set) it counts, over EVERY declaration in `Salt/` (not only audited ones):

  F-consumers     a result with a binder (explicit `( )` / instance `[ ]`, used section variable, or a
                  top-level premise of its conclusion) in which P occurs POSITIVELY:
                    direct  the binder's head is P                      `(h : P x)`, `P x → Q`
                    engine  P is a premise of a hypothesised implication `(hEngine : P x → Q)`
  ¬F-consumers    the same with P under `¬` / `Not` / `… → False`       `(h : ¬ P x)`, `(h : P x → False)`
  F-producers     item 2's producers of P, kinds kept apart: unconditional (DISCHARGED; `!g` = guarded),
                  conditional, ∃-witness
  ¬F-producers    a result concluding `¬ P …` (unconditional / conditional on another corpus Prop), or
                  concluding `False` with P among its premises (a refutation, `via False`)
  disjunction     a theorem whose conclusion is a top-level `∨` with P or ¬P as a disjunct, or a Prop
  sites           definition whose body is visibly such a disjunction (no unfolding at use sites); and
                  `by_cases` / `em` / `Classical.em` / `Decidable.em` / `Classical.byCases` on P in proofs

  FULCRUM-SHAPED  F-consumers >= 1 AND ¬F-consumers >= 1 (both horns deliver something)
  HALF-SHAPED     item 2 status OPEN, F-consumers >= 1, ¬F-consumers = 0 (the pull question: what would ¬P give?)
                  -- a SOCKET; the same shape at item 2 status FRAME is a HALF-SHAPED FRAME, counted and
                  listed but never ranked (¬P is "the parameters are out of range").

Pure Python 3 stdlib, source-level only -- every limit is printed at the TOP of the page.

Usage:
  python3 scripts/fulcrum_census.py              write docs/FULCRUM-CENSUS.md
  python3 scripts/fulcrum_census.py --stdout     print the page instead
  python3 scripts/fulcrum_census.py --check      exit 1 if docs/FULCRUM-CENSUS.md is stale
  python3 scripts/fulcrum_census.py --self-test  run the fixture and the per-arm mutants
"""
from __future__ import annotations

import os
import re
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import results_catalogue as rc  # noqa: E402  (item 1)
import methods_catalogue as mc  # noqa: E402  (item 2; also memoises item 1's comment stripper)

REPO = rc.REPO
PAGE = os.path.join("docs", "FULCRUM-CENSUS.md")
COMMAND = "python3 scripts/fulcrum_census.py"
HALF_TOP = 40
SITE_CAP = 400          # disjunction / case-split rows printed (the count is always full)
NEG_TABLE_CAP = 150     # rows of the ¬F-activity table
EX_CAP = 3              # example names per cell

CONSUMER_KWS = ("theorem", "lemma", "def", "abbrev", "instance", "opaque", "irreducible_def")
POS, NEG = "+", "-"


# ---------------------------------------------------------------- polarity walk
def neg_inner(s: str):
    """If s is `¬ X` or `Not X` (after stripping parens), return X, else None."""
    s = rc.strip_parens(s)
    if s.startswith("¬"): return s[1:].strip()
    m = re.match(r"Not\b\s*", s)
    if m and s[m.end():].strip(): return s[m.end():].strip()
    return None


def flip(p): return NEG if p == POS else POS


def occurrences(t: str, pol: str, mode: str, d, props, out: list):
    """Record (P, polarity, mode) for every corpus Prop P reachable in type t by the polarity walk:
    leading ∀/→ (premises of THIS type become `engine` occurrences at the same polarity), a final
    `False` (premises flip), `¬`/`Not` (flip), top-level `∧` (split); the head is resolved against P."""
    parts = rc.arrow_parts(t)
    final = rc.strip_parens(parts[-1])
    if final == "False" and len(parts) > 1:
        for p in parts[:-1]: occurrences(p, flip(pol), mode, d, props, out)
        return
    for p in parts[:-1]: occurrences(p, pol, "engine", d, props, out)
    inner = neg_inner(final)
    if inner is not None:
        occurrences(inner, flip(pol), mode, d, props, out); return
    conj = rc.split_top(final, "∧")
    if len(conj) > 1:
        for c in conj: occurrences(c, pol, mode, d, props, out)
        return
    hs = rc.heads(final)
    if len(hs) == 1:
        r = rc.resolve(hs[0], d.ns, d.opens, props)
        if r: out.append((r, pol, mode))


def binder_types(d):
    """Item 1's binder population: explicit/instance binders, used section variables, top-level premises."""
    bs, concl = rc.split_decl(d)
    toks = set(rc.IDENT_RE.findall(d.stmt))
    used = [b for b in d.vars if b[0] in ("(", "[") and b[1] and any(n in toks or n in d.includes for n in b[1])]
    types = [typ for op, _, typ in used + bs if op in ("(", "[") and typ]
    final = None
    if concl is not None:
        parts = rc.arrow_parts(concl)
        types += parts[:-1]
        final = rc.strip_parens(parts[-1])
    return types, final


PROP_ONLY_DISJ = "prop-def body"
THM_DISJ = "theorem conclusion"
SPLIT_RE = re.compile(r"(?<![\w.'])(by_cases|Classical\.byCases|Classical\.em|Decidable\.em|em)(?![\w'])")


def case_split_targets(d, props):
    """(P, polarity, token, line) for every by_cases/em in d's proof body whose target head is a corpus Prop."""
    out = []
    body = getattr(d, "proof", "")
    for m in SPLIT_RE.finditer(body):
        rest = body[m.end():m.end() + 300]
        if m.group(1) == "by_cases":
            mm = re.match(r"\s*(?:[\w'.₀-₉]+\s*:\s*)?", rest)
            rest = rest[mm.end():]
        pol = POS
        rest = rest.lstrip().lstrip("(").lstrip()
        while True:
            if rest.startswith("¬"): pol = flip(pol); rest = rest[1:].lstrip().lstrip("(").lstrip(); continue
            mm = re.match(r"Not\b\s*\(?\s*", rest)
            if mm: pol = flip(pol); rest = rest[mm.end():]; continue
            break
        mm = rc.IDENT_RE.match(rest.lstrip("@"))
        if not mm: continue
        r = rc.resolve(mm.group(0), d.ns, d.opens, props)
        if r:
            ln = d.line + d.stmt.count("\n") + body.count("\n", 0, m.start())
            out.append((r, pol, m.group(1), ln))
    return out


def _iff_top(s: str) -> bool:
    """`∨` binds tighter than `↔`/`=`: `A ↔ B ∨ C` is not a disjunction."""
    return rc.find_top(s, lambda t, i: t.startswith("↔", i) or (t[i] == "=" and t[i - 1:i] not in ("≠", "≤", "≥", ":", "=")
                                                                and t[i + 1:i + 2] not in ("=", ">"))) >= 0


def census(decls, props, status, prod, condp, witness):
    C = {P: dict(fcons_d=[], fcons_e=[], ncons_d=[], ncons_e=[], nprod_u=[], nprod_c=[], nprod_f=[],
                 disj=[], split=[]) for P in props}
    neg_binder_results = []     # results whose ONLY view of a corpus Prop is under ¬ (item 1 cannot see it)
    sites = []                  # (kind, name, path, line, [(P, pol)])
    for n in sorted(decls):
        d = decls[n]
        if d.kw in ("structure", "class", "inductive") or n in props:
            if n in props and d.kw in ("def", "abbrev"):
                b = mc.def_body(d, decls)
                ds = rc.split_top(rc.strip_parens(b), "∨") if b and not _iff_top(rc.strip_parens(b)) else []
                if len(ds) > 1:
                    hit = []
                    for x in ds:
                        inner = neg_inner(x)
                        hs = rc.heads(inner if inner is not None else x)
                        r = rc.resolve(hs[0], d.ns, d.opens, props) if len(hs) == 1 else None
                        if r: hit.append((r, NEG if inner is not None else POS))
                    if hit:
                        sites.append((PROP_ONLY_DISJ, n, d.path, d.line, hit))
                        for P, pol in hit: C[P]["disj"].append(n)
            continue
        if d.kw not in CONSUMER_KWS: continue
        types, final = binder_types(d)
        occ = []
        for t in types: occurrences(t, POS, "direct", d, props, occ)
        refutation = final == "False"
        pos_direct = {P for P, pol, m in occ if pol == POS and m == "direct"}
        seen = set()
        for P, pol, mode in occ:
            if P == n or (P, pol, mode) in seen: continue
            seen.add((P, pol, mode))
            if refutation and pol == POS and mode == "direct":
                C[P]["nprod_f"].append(n); continue
            key = ("fcons_" if pol == POS else "ncons_") + ("d" if mode == "direct" else "e")
            C[P][key].append(n)
        if occ and not pos_direct and any(pol == NEG for _, pol, _ in occ):
            neg_binder_results.append(n)
        if final is not None and not refutation:
            inner = neg_inner(final)
            if inner is not None:
                cur = []
                for c in rc.split_top(rc.strip_parens(inner), "∧") if not rc.strip_parens(inner).startswith("∃") else []:
                    hs = rc.heads(c)
                    r = rc.resolve(hs[0], d.ns, d.opens, props) if len(hs) == 1 else None
                    if r and r not in cur: cur.append(r)
                for P in cur:
                    C[P]["nprod_u" if not (pos_direct - {P}) else "nprod_c"].append(n)
            ds = rc.split_top(final, "∨") if not _iff_top(final) else [final]
            if len(ds) > 1 and d.kw in ("theorem", "lemma"):
                hit = []
                for x in ds:
                    xi = neg_inner(x)
                    hs = rc.heads(xi if xi is not None else x)
                    r = rc.resolve(hs[0], d.ns, d.opens, props) if len(hs) == 1 else None
                    if r: hit.append((r, NEG if xi is not None else POS))
                if hit:
                    sites.append((THM_DISJ, n, d.path, d.line, hit))
                    for P, pol in hit: C[P]["disj"].append(n)
        for P, pol, tok, ln in case_split_targets(d, props):
            sites.append(("case split `%s`" % tok, n, d.path, ln, [(P, pol)]))
            if n not in C[P]["split"]: C[P]["split"].append(n)
    rows = {}
    for P in props:
        c = C[P]
        fc = sorted(set(c["fcons_d"]) | set(c["fcons_e"]))
        nc = sorted(set(c["ncons_d"]) | set(c["ncons_e"]))
        cls = "FULCRUM" if fc and nc else ("HALF" if status[P] == "OPEN" and fc else
                                           ("FRAME" if status[P] == "FRAME" and fc else "-"))
        rows[P] = dict(c, fc=fc, nc=nc, cls=cls, status=status[P],
                       fprod_u=[(x, g) for x, g in prod.get(P, [])], fprod_c=list(condp.get(P, [])),
                       fprod_w=list(witness.get(P, [])))
    return rows, sites, neg_binder_results


def build(files, ledgers):
    decls, props, audited, kinds, hyps = mc.load_corpus(files, ledgers)
    status, prod, condp, hang, witness, frame = mc.hypothesis_status(decls, props, audited, kinds, hyps)
    rows, sites, negb = census(decls, props, status, prod, condp, witness)
    for P in rows: rows[P]["hang"] = len(hang.get(P, []))
    aud_uncond_neg = sorted(n for n in negb if n in audited and kinds.get(n) == "unconditional")
    receipt = dict(decls=len(decls), props=len(props), audited=len(audited),
                   consumers_scanned=sum(1 for n, d in decls.items() if d.kw in CONSUMER_KWS and n not in props))
    return dict(decls=decls, rows=rows, sites=sites, negb=negb, aud_uncond_neg=aud_uncond_neg, receipt=receipt,
                audited=audited)


# ---------------------------------------------------------------- render
def loc(decls, n):
    d = decls.get(n)
    return "%s:%d" % (d.path, d.line) if d else "?"


def ex(decls, names, cap=EX_CAP):
    names = list(names)
    s = ", ".join("`%s` (%s)" % (rc.md_escape(n), loc(decls, n)) for n in names[:cap])
    return s + (" +%d" % (len(names) - cap) if len(names) > cap else "") if names else "-"


def render(B, base: str, digest: str) -> str:
    R, D, S = B["rows"], B["decls"], B["sites"]
    L = []
    A = L.append
    A("# THE FULCRUM-SHAPE CENSUS — by machine (O13 item 3, first cut)")
    A("")
    A("> **GENERATED — do not edit by hand.** Regenerate: `%s` · staleness gate: `%s --check` · self-test: "
      "`%s --self-test`." % (COMMAND, COMMAND, COMMAND))
    A("> Base: last commit touching `Salt/` = `%s` · source digest `%s` (item 1's digest: sha256 over every "
      "`Salt/**/*.lean`, sorted by path). Built on `scripts/results_catalogue.py` + `scripts/methods_catalogue.py` "
      "(imported)." % (base, digest))
    A("")
    A("⚠️ **Nothing here bears on twin primes until it does.** This is a CENSUS of candidates for the fulcrum sweep "
      "(QUEUE item 15 lane (a)); the seat prices each by class (A–D) before any Lean. A shape is not a result.")
    A("")
    A("## LIMITS — read these before any count below")
    A("")
    A("- **Source-level parse, no elaboration** (item 1's limits all apply: macros, `alias`, `to_additive`, "
      "notation are invisible; implicit `{}`/`⦃⦄` binders are NOT walked; section `variable`s count only when "
      "named in the statement or `include`d).")
    A("- **Polarity is SYNTACTIC.** `¬`, `Not`, and `… → False` flip; nothing else does. A P reached only through "
      "an unfolded definition, `↔`, `≠`-style sugar, `∨` inside a binder, or a `∃` is NOT counted. `P x → False` in a "
      "BINDER is a ¬F-consumer; a declaration whose CONCLUSION is `False` is a refutation (¬F-producer `via False`) of "
      "the conjunction of its corpus premises, and its premises are not F-consumers.")
    A("- **Arrows under an `∃` are split as item 1 splits them:** a conclusion `∃ c, 0 < c ∧ ∀ x, A x → ¬ P x` "
      "is cut at its depth-0 `→`, so `A` counts as a premise (of the inner `∀`, which it is) and `¬ P` as the "
      "conclusion. Such a ¬F-producer is `conditional` whenever `A` is a corpus Prop, though the result proves the "
      "`∃` outright.")
    A("- **`engine` occurrences** are premises of a hypothesised implication (`hEngine : P → Q`), recorded at the "
      "binder's polarity. Nested implications deeper than one level are walked with the same rule and are "
      "imprecise (the polarity of `((P → Q) → R)` is not flipped).")
    A("- **Consumers are counted over EVERY declaration in `Salt/`** (theorem/lemma/def/abbrev/instance/opaque, "
      "not Prop-valued definitions themselves), not only audited results. Item 2's `hang` column (audited "
      "conditional results only) is carried beside it.")
    A("- **F-producers are item 2's, verbatim** (unconditional = DISCHARGED, `!g` guarded; conditional; ∃-witness). "
      "¬F-producers are this script's: `¬ P` conclusions (one level of `∧` under the `¬`), unconditional unless "
      "another corpus Prop sits as a direct positive binder.")
    A("- **Disjunction sites are VISIBLE ONLY:** a theorem conclusion that is a top-level `∨`, or a Prop-def body "
      "that is one. A theorem concluding a NAMED disjunction (e.g. `HeathBrownDichotomy`) is not unfolded — the "
      "Prop-def row carries it.")
    A("- **Case splits are a TOKEN SCAN** of proof bodies: `by_cases [h :] P`, `em P`, `Classical.em P`, "
      "`Decidable.em P`, `Classical.byCases P`, with P's head resolved against the corpus Prop set in the "
      "declaration's namespace/open context. A split on an unfolded or `have`-named proposition is invisible.")
    A("- **The classes are SHAPES, not verdicts.** FULCRUM-SHAPED says both polarities are consumed somewhere; it "
      "does not say the two horns are the SAME instance of P (arguments are not compared) nor that either horn "
      "is unconditional.")
    nb, au = B["negb"], B["aud_uncond_neg"]
    A("- **Regression guard on item 1's `¬`-binder walk:** %d declarations see a corpus Prop ONLY under `¬` "
      "in their binders; **%d of them are AUDITED results that item 1 classes `unconditional`** (this census found "
      "31 on 2026-09-26, when item 1's walk read `¬ P` as head `Not`; item 1 now records such a binder as the "
      "hypothesis `¬P`). The residue listed at the foot is expected to be binders of shape `¬ P → Q`, where `¬P` sits "
      "in the binder's ANTECEDENT and the hypothesis is on Q — item 1 reads those correctly and this census's "
      "positional polarity scan over-counts them (5 such at 2026-09-26, each read at source); a name of any "
      "other shape at the foot is a regression." % (len(nb), len(au)))
    A("")
    r = B["receipt"]
    cls_n = defaultdict(int)
    for x in R.values(): cls_n[x["cls"]] += 1
    A("## Population receipt")
    A("")
    A("| declarations indexed | corpus Prop-valued names | consumer declarations scanned | audited results "
      "| FULCRUM-SHAPED | HALF-SHAPED SOCKETS | HALF-SHAPED FRAMES | neither | disjunction/case-split sites |")
    A("|---|---|---|---|---|---|---|---|---|")
    A("| %d | %d | %d | %d | %d | %d | %d | %d | %d |" % (r["decls"], r["props"], r["consumers_scanned"], r["audited"],
                                                      cls_n["FULCRUM"], cls_n["HALF"], cls_n["FRAME"], cls_n["-"],
                                                      len(S)))
    A("")
    A("Per-polarity totals over the %d Props: with F-consumers %d · with ¬F-consumers %d · with F-producers "
      "(any kind) %d · with ¬F-producers (any kind) %d." % (
          len(R), sum(1 for x in R.values() if x["fc"]), sum(1 for x in R.values() if x["nc"]),
          sum(1 for x in R.values() if x["fprod_u"] or x["fprod_c"] or x["fprod_w"]),
          sum(1 for x in R.values() if x["nprod_u"] or x["nprod_c"] or x["nprod_f"])))
    A("")
    fl = sorted((P for P, x in R.items() if x["cls"] == "FULCRUM"), key=lambda P: (-len(R[P]["nc"]) - len(R[P]["fc"]), P))
    A("## FULCRUM-SHAPED (%d) — both polarities consumed" % len(fl))
    A("")
    A("Counts: F-cons = F-consumers (direct/engine) · ¬F-cons = ¬F-consumers (direct/engine) · F-prod = "
      "unconditional/conditional/∃-witness · ¬F-prod = unconditional/conditional/via False · sites = "
      "disjunction/case-split.")
    A("")
    A("| P | defined at | status | F-cons | ¬F-cons | F-prod | ¬F-prod | sites | ¬F-consumer examples | F-consumer examples |")
    A("|---|---|---|---|---|---|---|---|---|---|")
    for P in fl:
        x = R[P]
        A("| `%s` | %s | %s | %d (%d/%d) | %d (%d/%d) | %d/%d/%d | %d/%d/%d | %d/%d | %s | %s |" % (
            rc.md_escape(P), loc(D, P), x["status"], len(x["fc"]), len(set(x["fcons_d"])), len(set(x["fcons_e"])),
            len(x["nc"]), len(set(x["ncons_d"])), len(set(x["ncons_e"])),
            len(x["fprod_u"]), len(x["fprod_c"]), len(x["fprod_w"]),
            len(x["nprod_u"]), len(x["nprod_c"]), len(x["nprod_f"]), len(set(x["disj"])), len(x["split"]),
            ex(D, x["nc"]), ex(D, x["fc"])))
    A("")
    hl = sorted((P for P, x in R.items() if x["cls"] == "HALF"), key=lambda P: (-len(R[P]["fc"]), P))
    A("## HALF-SHAPED SOCKETS — top %d of %d by F-consumer count (status OPEN, not FRAME, no ¬F-consumer: "
      "*what would ¬P give?*)" % (min(HALF_TOP, len(hl)), len(hl)))
    A("")
    A("| # | P | defined at | status | F-cons (direct/engine) | audited hang (item 2) | ∃-witness producers "
      "| cond. producers | ¬F-prod | sites | F-consumer examples |")
    A("|---|---|---|---|---|---|---|---|---|---|---|")
    for i, P in enumerate(hl[:HALF_TOP], 1):
        x = R[P]
        A("| %d | `%s` | %s | %s | %d (%d/%d) | %d | %s | %d | %d | %d | %s |" % (
            i, rc.md_escape(P), loc(D, P), x["status"], len(x["fc"]), len(set(x["fcons_d"])), len(set(x["fcons_e"])),
            x["hang"], ex(D, x["fprod_w"], 2), len(x["fprod_c"]),
            len(x["nprod_u"]) + len(x["nprod_c"]) + len(x["nprod_f"]),
            len(set(x["disj"])) + len(x["split"]), ex(D, x["fc"])))
    A("")
    frl = sorted((P for P, x in R.items() if x["cls"] == "FRAME"), key=lambda P: (-len(R[P]["fc"]), P))
    A("## HALF-SHAPED FRAMES (%d) — status FRAME (item 2's parameter-frame rule), no ¬F-consumer" % len(frl))
    A("")
    A("A FRAME is a bundle of order relations over its own parameters; ¬P is 'the parameters are out of range', "
      "never a fulcrum horn, so these are listed and not ranked. Name (F-consumers):")
    A("")
    A(", ".join("`%s` (%d)" % (rc.md_escape(P), len(R[P]["fc"])) for P in frl) if frl else "(none)")
    A("")
    nl = sorted((P for P, x in R.items() if x["cls"] != "FULCRUM" and (x["nprod_u"] or x["nprod_c"] or x["nprod_f"])),
                key=lambda P: (-(len(R[P]["nprod_u"]) + len(R[P]["nprod_c"]) + len(R[P]["nprod_f"])), P))
    A("## ¬F-PRODUCED, NOT FULCRUM-SHAPED (%d; first %d) — a ¬P is proved somewhere but nothing consumes it as a binder"
      % (len(nl), min(NEG_TABLE_CAP, len(nl))))
    A("")
    A("| P | status | class | F-cons | ¬F-prod (u/c/via False) | examples |")
    A("|---|---|---|---|---|---|")
    for P in nl[:NEG_TABLE_CAP]:
        x = R[P]
        A("| `%s` | %s | %s | %d | %d/%d/%d | %s |" % (rc.md_escape(P), x["status"], x["cls"], len(x["fc"]),
                                                  len(x["nprod_u"]), len(x["nprod_c"]), len(x["nprod_f"]),
                                                  ex(D, x["nprod_u"] + x["nprod_c"] + x["nprod_f"], 2)))
    A("")
    A("## DISJUNCTION AND CASE-SPLIT SITES (%d; first %d, ordered by path)" % (len(S), min(SITE_CAP, len(S))))
    A("")
    kinds = defaultdict(int)
    for s in S: kinds[s[0]] += 1
    A("By kind: " + " · ".join("%s %d" % kv for kv in sorted(kinds.items())) + ".")
    A("")
    A("| kind | declaration | file:line | P (polarity) |")
    A("|---|---|---|---|")
    for k, n, p, ln, hit in sorted(S, key=lambda s: (s[2], s[3], s[1], s[0]))[:SITE_CAP]:
        A("| %s | `%s` | %s:%d | %s |" % (k, rc.md_escape(n), p, ln,
                                          ", ".join("`%s`%s" % (rc.md_escape(P), "" if pol == POS else " (¬)")
                                                    for P, pol in hit)))
    A("")
    A("## Audited results item 1 classes `unconditional` whose only corpus-Prop binder is under ¬ (%d)" % len(au))
    A("")
    for n in au:
        A("- `%s` (%s)" % (rc.md_escape(n), loc(D, n)))
    if not au: A("(none)")
    A("")
    return "\n".join(L) + "\n"


def generate():
    files, ledgers, digest = rc.load_repo()
    B = build(files, ledgers)
    base = rc.git("log", "-1", "--format=%h", "--", "Salt") or "unknown"
    return render(B, base, digest), B


# ---------------------------------------------------------------- self-test
FIXTURE = {
    "Salt/Fx/Defs.lean": '''
namespace Salt.Fx
def FQ (C : ℕ) : Prop := ∀ Q : ℕ, ∃ q, Q < q ∧ C ≤ q
def NSZ : Prop := ∀ x : ℕ, ∃ y, x < y
def TPC : Prop := ∀ n : ℕ, ∃ p, n < p
def HBD : Prop := TPC ∨ NSZ
def HOpen : Prop := ∀ x : ℕ, ∃ y, x ≤ y
def HA (n : ℕ) : Prop := ∀ x : ℕ, ∃ y, x + n ≤ y
def HP : Prop := ∀ x : ℕ, ∃ y, x + 1 ≤ y
def HN (n : ℕ) : Prop := ∀ x : ℕ, ∃ y, x + n < y
def HR : Prop := ∀ x : ℕ, ∃ y, x + 2 < y
def HFr (X j : ℕ) : Prop := 3 ≤ X ∧ 4 ≤ 2 ^ j
end Salt.Fx
''',
    "Salt/Fx/Main.lean": '''
import Salt.Fx.Defs
namespace Salt.Fx
-- theorem fake (h : ¬ HOpen) : True := trivial
theorem not_fq {C : ℕ} (hC : 0 < C) (hnF : ¬ FQ C) : NSZ := sorry
theorem dich {C : ℕ} (hC : 0 < C) (hEngine : FQ C → TPC) : HBD := by
  by_cases hF : FQ C
  · exact Or.inl (hEngine hF)
  · exact Or.inr (not_fq hC hF)
theorem uses_open (h : HOpen) : True := trivial
theorem uses_frame (h : HFr 5 2) : True := trivial
theorem uses_open2 (h : HOpen) (h2 : HA 1) : True := trivial
theorem neg_as_arrow (h : HA 1 → False) : True := trivial
theorem prem_neg : ¬ HP → True := fun _ => trivial
theorem prem_pos : HP → True := fun _ => trivial
theorem neg_prod : ¬ HN 3 := sorry
theorem refute (h : HR) : False := sorry
theorem disj : HOpen ∨ ¬ HA 2 := sorry
theorem iff_not_disj : HN 1 ↔ HOpen ∨ HP := sorry
theorem em_site : True := by
  rcases Classical.em (HOpen) with h | h <;> trivial
end Salt.Fx
''',
    "Salt/Fx/All.lean": '''
#audit_axioms Salt.Fx.not_fq Salt.Fx.dich Salt.Fx.uses_open
''',
}
# P -> (class, #F-cons, #¬F-cons, #¬F-prod, #disj sites, #case splits)
EXPECT = {
    "Salt.Fx.FQ": ("FULCRUM", 1, 1, 0, 0, 1),
    "Salt.Fx.HA": ("FULCRUM", 1, 1, 0, 1, 0),
    "Salt.Fx.HP": ("FULCRUM", 1, 1, 0, 0, 0),
    "Salt.Fx.HOpen": ("HALF", 2, 0, 0, 1, 1),
    "Salt.Fx.HN": ("-", 0, 0, 1, 0, 0),
    "Salt.Fx.HR": ("-", 0, 0, 1, 0, 0),
    "Salt.Fx.TPC": ("HALF", 1, 0, 0, 1, 0),
    "Salt.Fx.NSZ": ("-", 0, 0, 0, 1, 0),
    "Salt.Fx.HFr": ("FRAME", 1, 0, 0, 0, 0),
}
EXPECT_KINDS = {  # (P, key) -> names
    ("Salt.Fx.FQ", "ncons_d"): ["Salt.Fx.not_fq"], ("Salt.Fx.FQ", "fcons_e"): ["Salt.Fx.dich"],
    ("Salt.Fx.HA", "ncons_d"): ["Salt.Fx.neg_as_arrow"], ("Salt.Fx.HP", "ncons_d"): ["Salt.Fx.prem_neg"],
    ("Salt.Fx.HN", "nprod_u"): ["Salt.Fx.neg_prod"], ("Salt.Fx.HR", "nprod_f"): ["Salt.Fx.refute"],
}


def check_fixture(fx) -> list:
    ledgers = sorted(p for p in fx if p.endswith("All.lean"))
    B = build(fx, ledgers)
    R = B["rows"]
    errs = []
    for P, (cls, fc, nc, npd, dj, sp) in EXPECT.items():
        x = R.get(P)
        if x is None: errs.append("missing %s" % P); continue
        got = (x["cls"], len(x["fc"]), len(x["nc"]), len(x["nprod_u"]) + len(x["nprod_c"]) + len(x["nprod_f"]),
               len(set(x["disj"])), len(x["split"]))
        if got != (cls, fc, nc, npd, dj, sp): errs.append("%s: %s, want %s" % (P, got, (cls, fc, nc, npd, dj, sp)))
    for (P, k), ns in EXPECT_KINDS.items():
        if P in R and sorted(set(R[P][k])) != ns: errs.append("%s %s: %s, want %s" % (P, k, R[P][k], ns))
    if B["aud_uncond_neg"] != []: errs.append("aud_uncond_neg %s (item 1 ¬-walk regressed)" % B["aud_uncond_neg"])
    return errs


MUTANTS = [
    ("¬F-consumer arm (¬ binder): ¬ dropped", "Salt/Fx/Main.lean", "(hnF : ¬ FQ C)", "(hnF : FQ C)"),
    ("F-consumer arm (engine): premise dropped", "Salt/Fx/Main.lean", "(hEngine : FQ C → TPC)", "(hEngine : TPC)"),
    ("¬F-consumer arm (→ False binder)", "Salt/Fx/Main.lean", "(h : HA 1 → False)", "(h : HA 1 → True)"),
    ("¬F-consumer arm (conclusion premise)", "Salt/Fx/Main.lean", "prem_neg : ¬ HP → True", "prem_neg : HP → True"),
    ("F-consumer arm (conclusion premise)", "Salt/Fx/Main.lean", "prem_pos : HP → True", "prem_pos : True"),
    ("F-consumer arm (direct binder)", "Salt/Fx/Main.lean", "uses_open (h : HOpen)", "uses_open (h : 1 ≤ 2)"),
    ("¬F-producer arm (¬ conclusion)", "Salt/Fx/Main.lean", "neg_prod : ¬ HN 3", "neg_prod : HN 3"),
    ("¬F-producer arm (via False)", "Salt/Fx/Main.lean", "(h : HR) : False", "(h : HR) : True"),
    ("disjunction arm (theorem)", "Salt/Fx/Main.lean", "HOpen ∨ ¬ HA 2", "HOpen ∧ ¬ HA 2"),
    ("disjunction arm (↔ exclusion): iff becomes a disjunction", "Salt/Fx/Main.lean",
     "HN 1 ↔ HOpen ∨ HP", "HN 1 ∨ HOpen ∨ HP"),
    ("disjunction arm (Prop-def body)", "Salt/Fx/Defs.lean", "def HBD : Prop := TPC ∨ NSZ",
     "def HBD : Prop := TPC ∧ NSZ"),
    ("case-split arm (by_cases)", "Salt/Fx/Main.lean", "by_cases hF : FQ C", "by_cases hF : 1 ≤ C"),
    ("case-split arm (Classical.em)", "Salt/Fx/Main.lean", "Classical.em (HOpen)", "Classical.em (1 ≤ 2)"),
    ("HALF class: an unconditional producer appears", "Salt/Fx/Main.lean", "end Salt.Fx",
     "theorem hopen_holds : HOpen := fun x => ⟨x, le_rfl⟩\nend Salt.Fx"),
    ("FULCRUM class: HOpen gains a ¬ consumer", "Salt/Fx/Main.lean", "end Salt.Fx",
     "theorem neg_open (h : ¬ HOpen) : True := trivial\nend Salt.Fx"),
    ("FRAME split: the frame gains an ∃ (becomes a socket)", "Salt/Fx/Defs.lean",
     "3 ≤ X ∧ 4 ≤ 2 ^ j", "3 ≤ X ∧ ∃ k, 4 ≤ 2 ^ k"),
    ("comment stripping: commented ¬ consumer made live", "Salt/Fx/Main.lean",
     "-- theorem fake (h : ¬ HOpen) : True := trivial", "theorem fake (h : ¬ HOpen) : True := trivial"),
]


def self_test() -> int:
    errs = check_fixture(dict(FIXTURE))
    if errs:
        print("SELF-TEST FAIL (clean fixture):"); [print("  " + e) for e in errs]; return 1
    print("clean fixture: %d Props + %d kind cells as expected" % (len(EXPECT), len(EXPECT_KINDS)))
    killed = 0
    for label, f, old, new in MUTANTS:
        fx = dict(FIXTURE)
        assert old in fx[f], "mutant anchor missing: " + label
        fx[f] = fx[f].replace(old, new, 1)
        e = check_fixture(fx)
        killed += bool(e)
        print("  mutant %-52s %s%s" % (label[:52], "KILLED" if e else "SURVIVED", (" (" + e[0][:70] + ")") if e else ""))
    print("mutants killed: %d / %d" % (killed, len(MUTANTS)))
    return 0 if killed == len(MUTANTS) else 1


def main(argv):
    if "--self-test" in argv: return self_test()
    page, B = generate()
    if "--check" in argv:
        try:
            cur = open(os.path.join(REPO, PAGE), encoding="utf-8").read()
        except OSError:
            cur = None
        if cur != page:
            print("STALE: %s differs from a fresh generation; run `%s`" % (PAGE, COMMAND)); return 1
        print("OK: %s is current" % PAGE); return 0
    if "--stdout" in argv:
        sys.stdout.write(page); return 0
    with open(os.path.join(REPO, PAGE), "w", encoding="utf-8") as f:
        f.write(page)
    n = defaultdict(int)
    for x in B["rows"].values(): n[x["cls"]] += 1
    print("wrote %s (%d B): FULCRUM=%d HALF=%d FRAME=%d neither=%d sites=%d" % (PAGE, len(page.encode()), n["FULCRUM"],
                                                                     n["HALF"], n["FRAME"], n["-"], len(B["sites"])))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
