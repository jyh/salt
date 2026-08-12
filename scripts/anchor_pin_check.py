#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
anchor_pin_check.py — the cert-layer anchor table's derived facts, re-derived.

Checks docs/CERT-ANCHORS-0811.md against the two papers it pins.  Papers are
named BY PATH (M0): this house has more than one paper, and "the paper"
unqualified has already sent a seat searching the wrong file.

  ARM 1  PHRASE -> LINE.  "The phrase is the anchor; the line number is a HINT
         that rots."  For every quoted phrase, find where it ACTUALLY is in the
         paper that cell names, and compare against that paper's pins.

  ARM 2  LABEL -> LINE.  A cell may pin a LaTeX label (`thm:vmvt`) or a Lean
         declaration (`neutrality_rate`) instead of quoting prose.  Resolve it
         and check the pin the same way.

  ARM 3  DERIVED COUNTS.  Recompute LANDED/OPEN/ANCHORED/PARKED from the rows
         and check each count-shaped sentence BY LABEL.

  ARM 4  PINS IN PROSE.  Pins written in paragraphs, which ARM 1 (which walks
         table ROWS) structurally cannot see.  A green ARM 1 would otherwise
         license "the pins are swept" while a whole class went unread.

  ARM 5  ROW MARKS vs THE CORPUS.  ARM 3 derives its totals from the table's own
         ✅ marks, so it is internally consistent and can still be externally
         wrong -- three rows were marked open while their certs sat in
         Salt/Certs/, and ARM 3 reported clean.  This arm reads the corpus.
         It does NOT auto-correct: mention is not coverage (Chen.lean names
         chen_goldbach only to EXCLUDE it), so it prints the mentioning lines
         and a human records the resolution in the row as `ARM5-READ: ...`.

  ARM 6  EVERY QUOTED STRING IN EVERY CERTIFICATE, vs the papers.  Routed here
         by evidence: seals read ONE quote per cert, so most quoted strings had
         never been read by any seal.  Grades the salt population only -- the
         saltworks certs cite a brief and the bus, outside the paper set
         (compiler), and grading them here would manufacture MISSes.
         Diagnoses two classes the others cannot: an UNMARKED ELISION (words
         dropped under an em-dash, which reads as the source's own punctuation
         -- fragments split ONLY on an ellipsis, an omission marker the reader
         can see), and a HISTORICAL PIN (`<rev>^:main.tex:645`), which it
         verifies with `git show` rather than reporting a MISS it has not
         earned: today's file cannot refute a claim about yesterday's.

Five disciplines this script is built around, every one of them paid for:

  * NEVER A SILENT SKIP.  Everything extracted is printed with a verdict; what
    cannot be checked prints as SKIP **with its reason**.  The predecessor
    dropped 7 of 16 phrases silently and reported green.

  * PUNCTUATION IS NOT CONTENT.  The doc writes "Siegel-Walfisz" with U+2013,
    main.tex writes "Siegel--Walfisz"; the doc writes "Omega(...) <= 3" in
    Unicode, main.tex in LaTeX macros.  A literal grep of the doc's own phrase
    against its own paper returns ZERO in both cases.  Normalisation is
    load-bearing, so --show-normalised prints exactly what was compared.

  * NO ±1 TOLERANCE.  The rot this file exists to catch WAS +1 (one commit
    inserted a line above nine pins).  A tolerance that swallows the known
    failure mode is not a check.  Deltas are reported, never absorbed.

  * A NUMBER'S LABEL IS PART OF THE NUMBER.  Checking that the right *set* of
    numbers appears passes an inverted "5 LANDED / 7 OPEN" when the truth is
    7 and 5.  Counts are matched to their nouns.

  * A VERIFIED TOTAL OVER AN UNVERIFIED LIST is the same defect as a verified
    list under an unverified total, and reads as MORE trustworthy because it
    shows its work.  ARM 3 alone was exactly that; ARM 5 is why it isn't now.

  ARM 3's sentence hunt is a QUERY, not a RULE, so its list is a FLOOR: it
  prints every candidate line considered.  ARMs 1-2 are rules over table rows.

Usage:  python3 scripts/anchor_pin_check.py [--show-normalised] [--doc PATH]
Exit:   0 clean · 1 a drift or count mismatch · 2 could not run.
"""

from __future__ import annotations

import argparse
import re
import sys
import unicodedata
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_DOC = REPO / "docs" / "CERT-ANCHORS-0811.md"

PAPERS = {
    "Pi": REPO / "papers" / "flagship" / "main.tex",
    "Nature": REPO.parent / "seat" / "briefs" / "2026-08-11-nature-draft-v0.md",
}

MIN_PHRASE = 12      # below this, a match is coincidence, not evidence
MAX_WINDOW = 3       # papers hard-wrap; a sentence may span this many lines


# ---------------------------------------------------------------- normalising

# LaTeX macro -> the Unicode the anchor doc uses.  Longest first; the lookahead
# stops \le from firing inside \leaninline, and the leading backslash stops it
# from firing inside an escaped identifier like chen\_omega\_prod\_le\_three.
_MACRO = [
    (r"\\varepsilon", "epsilon"), (r"\\epsilon", "epsilon"),
    (r"\\Omega", "omega"), (r"\\omega", "omega"),
    (r"\\Lambda", "lambda"), (r"\\lambda", "lambda"),
    (r"\\varphi", "phi"), (r"\\phi", "phi"), (r"\\Phi", "phi"),
    (r"\\theta", "theta"), (r"\\Theta", "theta"),
    (r"\\alpha", "alpha"), (r"\\beta", "beta"), (r"\\gamma", "gamma"),
    (r"\\delta", "delta"), (r"\\Delta", "delta"), (r"\\sigma", "sigma"),
    (r"\\chi", "chi"), (r"\\psi", "psi"), (r"\\pi", "pi"), (r"\\rho", "rho"),
    (r"\\zeta", "zeta"), (r"\\mu", "mu"), (r"\\nu", "nu"), (r"\\tau", "tau"),
    (r"\\leqslant", "<="), (r"\\leq", "<="), (r"\\le", "<="),
    (r"\\geqslant", ">="), (r"\\geq", ">="), (r"\\ge", ">="),
    (r"\\neq", "!="), (r"\\ne", "!="), (r"\\approx", "~"),
    (r"\\ll", "<<"), (r"\\gg", ">>"), (r"\\infty", "infinity"),
    (r"\\sqrt", "sqrt"), (r"\\sum", "sum"), (r"\\prod", "prod"),
    (r"\\log", "log"), (r"\\exp", "exp"), (r"\\dist", "dist"),
    (r"\\times", "x"), (r"\\cdot", " "), (r"\\mid", "|"),
    (r"\\in", " in "), (r"\\to", "->"), (r"\\equiv", "="),
    (r"\\tfrac", "frac"), (r"\\dfrac", "frac"),
]
_MACRO_RE = [(re.compile(p + r"(?![a-zA-Z])"), r) for p, r in _MACRO]

# The Unicode the doc uses -> the same ASCII the macros land on.
_UNI = {
    "Ω": "omega", "ω": "omega", "Λ": "lambda", "λ": "lambda",
    "φ": "phi", "ϕ": "phi", "Φ": "phi", "θ": "theta", "Θ": "theta",
    "α": "alpha", "β": "beta", "γ": "gamma", "δ": "delta", "Δ": "delta",
    "σ": "sigma", "χ": "chi", "ψ": "psi", "π": "pi", "ρ": "rho",
    "ζ": "zeta", "μ": "mu", "ν": "nu", "τ": "tau", "ε": "epsilon",
    "≤": "<=", "≥": ">=", "≠": "!=", "≈": "~", "≪": "<<", "≫": ">>",
    "∞": "infinity", "√": "sqrt", "∑": "sum", "∏": "prod", "∈": " in ",
    "→": "->", "≡": "=", "·": " ", "×": "x", "∤": " notdvd ", "∣": "|",
    "₀": "0", "₁": "1", "₂": "2", "₃": "3", "⁻": "-", "¹": "1", "²": "2",
}

_LATEX_BRACED = re.compile(r"\\[a-zA-Z]+\*?\{([^{}]*)\}")
_LATEX_BARE = re.compile(r"\\[a-zA-Z]+\*?")
_DASHES = dict.fromkeys(
    [0x2010, 0x2011, 0x2012, 0x2013, 0x2014, 0x2015, 0x2212, 0x00AD], "-"
)
_QUOTES = {0x2018: "'", 0x2019: "'", 0x201A: "'", 0x201B: "'",
           0x201C: '"', 0x201D: '"', 0x201E: '"', 0x201F: '"',
           0x2032: "'", 0x2033: '"'}
_SPACES = dict.fromkeys([0x00A0, 0x2007, 0x2009, 0x202F, 0x2002, 0x2003], " ")


def normalise(s: str) -> str:
    """Fold everything that is typography rather than content."""
    s = unicodedata.normalize("NFC", s)
    s = s.translate(_QUOTES).translate(_SPACES)
    for rx, rep in _MACRO_RE:          # LaTeX macros BEFORE bare-command strip
        s = rx.sub(rep, s)
    s = s.replace("---", "-").replace("--", "-")
    s = s.translate(_DASHES)
    for k, v in _UNI.items():
        s = s.replace(k, v)
    for _ in range(3):                 # \leaninline{Salt.Foo} -> Salt.Foo
        s, n = _LATEX_BRACED.subn(r"\1", s)
        if not n:
            break
    s = _LATEX_BARE.sub(" ", s)
    s = re.sub(r"[*_`${}~\\\[\]]", "", s)
    s = re.sub(r"\s+", " ", s)
    return s.strip().lower()


# ---------------------------------------------------------------- extraction

# No length cap.  The predecessor's [^"]{6,70} is what made phrases vanish.
_PHRASE = re.compile(r"[\u201c\"]([^\u201c\u201d\"]+)[\u201d\"]")
_PIN = re.compile(r":(\d{1,4})(?:\s*[-\u2013\u2014]\s*(\d{1,4}))?")
_PAPER_TAG = re.compile(r"\b(Pi|Nature)\b")
# A backticked LaTeX label (thm:foo) or Lean declaration name.
_LABEL = re.compile(r"`([A-Za-z][A-Za-z0-9_:.']*)`")


def split_fragments(phrase: str) -> list[str]:
    parts = re.split(r"\u2026|\.\.\.", phrase)
    return [p.strip(" ,;:") for p in parts if p.strip(" ,;:")]


def table_rows(text: str) -> list[tuple[int, str]]:
    return [(int(m.group(1)), line)
            for line in text.splitlines()
            if (m := re.match(r"^\|\s*(\d+)\s*\|", line))]


def cells(line: str) -> list[str]:
    return [c.strip() for c in line.strip().strip("|").split("|")]


def segment_by_paper(cell: str) -> list[tuple[str, str]]:
    """Split an anchor cell at each Pi/Nature mention.

    The table is written paper-first -- "**Nature :201** *"..."*; **Pi :322**
    *"..."*" -- so each mention OWNS the pins and phrases that follow it, and
    segmenting this way is what lets a pin be checked against the paper it was
    actually written for.  Without it a cell passes when ANY pin matches ANY
    paper, and a rotted Pi pin hides behind a correct Nature one.

    Paper names occurring INSIDE a quoted phrase are not boundaries: a quote may
    legitimately contain the word "Nature" or "Pi", and splitting there tears the
    phrase in half so both halves report "no phrase to check" -- a silent skip
    wearing a structural face.  Found by the planted T4 case, not by reading.
    """
    quoted = [(m.start(), m.end()) for m in _PHRASE.finditer(cell)]
    marks = [(m.start(), m.group(1)) for m in _PAPER_TAG.finditer(cell)
             if not any(a <= m.start() < b for a, b in quoted)]
    if not marks:
        return []
    segs = []
    for i, (pos, name) in enumerate(marks):
        end = marks[i + 1][0] if i + 1 < len(marks) else len(cell)
        segs.append((name, cell[pos:end]))
    # Consecutive mentions of the same paper are one segment ("Pi ... Pi ...").
    merged: list[tuple[str, str]] = []
    for name, body in segs:
        if merged and merged[-1][0] == name:
            merged[-1] = (name, merged[-1][1] + " " + body)
        else:
            merged.append((name, body))
    return merged


def pins_in(s: str) -> list[int]:
    out = []
    for m in _PIN.finditer(s):
        out.append(int(m.group(1)))
        if m.group(2):
            out.append(int(m.group(2)))
    return out


# ---------------------------------------------------------------- searching

def find_span(lines: list[str], frag: str) -> list[tuple[int, int]]:
    """(start, end) 1-indexed spans whose normalised text contains the fragment.

    Widening to a multi-line window matters because both papers hard-wrap: the
    zero-free-region phrase genuinely spans two Nature lines, and reporting only
    the window's FIRST line makes a correct pin look rotted.
    """
    want = normalise(frag)
    if not want:
        return []
    norm = [normalise(l) for l in lines]
    hits = [(i + 1, i + 1) for i, l in enumerate(norm) if want in l]
    if hits:
        return hits
    for width in range(2, MAX_WINDOW + 1):
        for i in range(len(norm) - width + 1):
            if want in normalise(" ".join(lines[i:i + width])):
                hits.append((i + 1, i + width))
        if hits:
            return hits
    return []


def spans_cover(spans: list[tuple[int, int]], pin: int) -> bool:
    return any(a <= pin <= b for a, b in spans)


def fmt_spans(spans: list[tuple[int, int]]) -> str:
    return ",".join(str(a) if a == b else f"{a}-{b}" for a, b in spans)


_BEGIN = re.compile(r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}")


def env_at(lines: list[str], pin: int) -> tuple[int, int] | None:
    """If the pinned line OPENS a LaTeX theorem-like environment, its extent.

    A cell may pin the `\\begin{theorem}...\\label{}` line while quoting a
    sentence from the theorem's BODY one line below.  That is a correct pin, not
    rot -- but it must be established by reading the environment, never by a ±1
    tolerance, because the rot this file exists to catch was itself exactly +1.
    """
    if not (1 <= pin <= len(lines)) or not _BEGIN.search(lines[pin - 1]):
        return None
    for j in range(pin, min(pin + 40, len(lines))):
        if "\\end{" in lines[j]:
            return (pin, j + 1)
    return (pin, min(pin + 40, len(lines)))


def find_label(lines: list[str], label: str) -> list[int]:
    """Where a LaTeX \\label{...} or a Lean declaration of this name is DEFINED."""
    out = []
    for i, l in enumerate(lines, 1):
        if f"\\label{{{label}}}" in l:
            out.append(i)
        elif re.search(r"^\s*(?:theorem|lemma|def|abbrev|structure)\s+"
                       + re.escape(label) + r"\b", l):
            out.append(i)
    return out


# ---------------------------------------------------------------- the arms

def load_papers() -> dict[str, list[str]]:
    loaded = {}
    for name, path in PAPERS.items():
        if not path.exists():
            print(f"  !! {name}: MISSING at {path}", file=sys.stderr)
            continue
        loaded[name] = path.read_text(encoding="utf-8", errors="replace").splitlines()
    return loaded


def arms_1_and_2(doc_text, papers, show_norm) -> tuple[int, int, int]:
    print("=" * 78)
    print("ARM 1/2 — PHRASE and LABEL -> LINE, per paper (pins are hints; phrases are not)")
    print("=" * 78)
    ok = drift = skipped = 0

    for rownum, line in table_rows(doc_text):
        cs = cells(line)
        if len(cs) < 3:
            continue
        target, anchor = cs[1], cs[2]
        print(f"\n  row {rownum:<3} {target}")
        segs = segment_by_paper(anchor)
        if not segs:
            print("      SKIP: cell names no paper — cannot choose a file to search")
            skipped += 1
            continue

        for paper, body in segs:
            pins = pins_in(body)
            phrases = _PHRASE.findall(body)
            labels = [l for l in _LABEL.findall(body) if ":" in l or "_" in l]
            lines_ = papers.get(paper)
            head = f"      [{paper}] pins {pins or '—'}"
            if lines_ is None:
                print(head + "   SKIP: paper file not readable")
                skipped += 1
                continue
            if not phrases and not labels:
                print(head + "   SKIP: segment quotes no phrase and names no label"
                             " — nothing to re-derive")
                skipped += 1
                continue
            print(head)

            for kind, item in ([("phrase", p) for p in phrases]
                               + [("label", l) for l in labels]):
                shown = item if len(item) <= 52 else item[:49] + "..."
                if kind == "label":
                    hits = find_label(lines_, item)
                    spans = [(h, h) for h in hits]
                else:
                    frags = [f for f in split_fragments(item)
                             if len(normalise(f)) >= MIN_PHRASE]
                    if not frags:
                        print(f'        SKIP {kind} "{shown}"')
                        print(f"             reason: normalises below {MIN_PHRASE} chars"
                              " — too short to be evidence")
                        skipped += 1
                        continue
                    if show_norm:
                        for f in frags:
                            print(f"             normalised: {normalise(f)!r}")
                    per = [find_span(lines_, f) for f in frags]
                    spans = sorted({s for ss in per for s in ss}) if all(per) else []

                if not spans:
                    print(f'        MISS {kind} "{shown}"  — not found in {paper}')
                    drift += 1
                    continue
                where = fmt_spans(spans)
                if not pins:
                    print(f'        OK   {kind} "{shown}"  -> {paper}@{where}  (no pin)')
                    ok += 1
                elif any(spans_cover(spans, p) for p in pins):
                    hit = [p for p in pins if spans_cover(spans, p)]
                    print(f'        OK   {kind} "{shown}"  -> {paper}@{where}'
                          f'  pin {hit} lands inside')
                    ok += 1
                else:
                    env = next((e for p in pins
                                if (e := env_at(lines_, p))
                                and any(e[0] <= a and b <= e[1] for a, b in spans)), None)
                    if env:
                        print(f'        OK   {kind} "{shown}"  -> {paper}@{where}')
                        print(f"             pin {pins} opens the environment {env[0]}-{env[1]}"
                              f" and the phrase sits inside it")
                        ok += 1
                        continue
                    near = min(pins, key=lambda p: min(abs(p - a) for a, _ in spans))
                    d = min(near - a for a, _ in spans)
                    print(f'        DRIFT {kind} "{shown}"')
                    print(f"             pinned {pins} in {paper}, ACTUALLY at {where}"
                          f"   (nearest pin {near}, delta {d:+d})")
                    drift += 1

    print(f"\n  ARM 1/2 totals: {ok} ok · {drift} drift · {skipped} skipped-with-reason")
    return ok, drift, skipped


_NOUNS = [
    ("landed", re.compile(r"(\d+)\s*(?:rows?\s*)?landed", re.I)),
    ("open", re.compile(r"(\d+)\s*(?:rows?\s*)?open", re.I)),
    ("anchored", re.compile(r"(\d+)\s*(?:target\s+rows?\s*·?\s*)?anchored", re.I)),
    ("parked", re.compile(r"(\d+)\s*parked", re.I)),
    ("rows", re.compile(r"(\d+)\s*(?:target\s+)?rows?", re.I)),
]


def arm3(doc_text: str) -> int:
    print()
    print("=" * 78)
    print("ARM 3 — DERIVED COUNTS  (recomputed from the rows, matched BY NOUN)")
    print("=" * 78)
    landed, open_ = [], []
    for rownum, line in table_rows(doc_text):
        cs = cells(line)
        (landed if cs and cs[-1].startswith("\u2705") else open_).append(rownum)
    parked = len(re.findall(r"^\|\s*`", doc_text, re.M))
    truth = {"landed": len(landed), "open": len(open_),
             "anchored": len(landed) + len(open_), "parked": parked,
             "rows": len(landed) + len(open_) + parked}

    print(f"\n  LANDED   {truth['landed']:>2}   rows {landed}")
    print(f"  OPEN     {truth['open']:>2}   rows {open_}")
    print(f"  ANCHORED {truth['anchored']:>2}   PARKED {truth['parked']}"
          f"   TOTAL rows {truth['rows']}")
    print("\n  count-shaped sentences (a QUERY, so this list is a FLOOR — every"
          "\n  candidate line considered is printed, disagreements marked !!):")

    bad = 0
    for i, line in enumerate(doc_text.splitlines(), 1):
        claims = {}
        for noun, rx in _NOUNS:
            for m in rx.finditer(line):
                claims.setdefault(noun, int(m.group(1)))
        if not claims:
            continue
        wrong = {n: v for n, v in claims.items() if truth[n] != v}
        # "ANCHORED \u2014 12 rows" counts the ANCHORED rows, not all 14.  Disclosed
        # rather than silently widened: a second admissible reading of the same
        # noun is a scoping fact the reader should see, not one the tool buries.
        if wrong.get("rows") == truth["anchored"] and re.search(r"anchored", line, re.I):
            print(f"      (: {i} \u2014 'rows' read as ANCHORED rows ({truth['anchored']}),"
                  " which the line's own word licenses)")
            wrong.pop("rows")
        quoted = bool(re.search(r'["\u201c][^"\u201d]*\d', line))
        if wrong:
            mark = "~~" if quoted else "!!"
            if not quoted:
                bad += 1
        else:
            mark = "  "
        detail = "  ".join(f"{n}={v}(truth {truth[n]})" for n, v in wrong.items())
        print(f"   {mark} :{i:<5} {line.strip()[:76]}")
        if wrong:
            note = " [inside quotes — historical restatement? read it]" if quoted else ""
            print(f"          {detail}{note}")
    print(f"\n  ARM 3: {bad} live line(s) carrying a count the rows do not support")
    return bad


# ---------------------------------------------------------------- self-test

# Each case PLANTS a specific failure and names what must happen.  A checker
# that is its own criterion proves nothing, so the negative controls (T1, T3,
# T6) matter as much as the positives: a tool that flags everything would pass
# a positives-only suite and be useless.
_SELF_PI = r"""\documentclass{article}
\begin{document}
Around these sit an unconditional Siegel--Walfisz theorem, a
Bombieri--Vinogradov theorem, with the corollary $\Omega(p(p+2)) \le 3$
for infinitely many primes $p$.
\begin{theorem}[The gap theorem]\label{thm:gap}
no predicate $E$ is both twin-sufficient and parity-invariant
\end{theorem}
a sentence about the Vinogradov mean
value theorem that wraps across two lines.
\end{document}
"""
_SELF_NATURE = """intro line one
no public artifact proves the large sieve inequality today
a line that exists only in the Nature draft and nowhere in Pi
"""
_SELF_DOC = """# synthetic
## ANCHORED — 2 rows
| # | target | anchor | state |
|---|---|---|---|
| 1 | `t1_notation` | **Pi :4** — *"Ω(p(p+2)) ≤ 3 for infinitely many primes"* | ✅ `a` |
| 2 | `t2_pinrot` | **Nature :1** — *"no public artifact proves the large sieve inequality"* | ✅ `b` |
| 3 | `t3_wrapped` | **Pi :9** — *"the Vinogradov mean value theorem"* | open |
| 4 | `t4_crosspaper` | **Pi :3** — *"a line that exists only in the Nature draft"* | open |
| 5 | `t5_envpin` | **Pi :6** — *"no predicate `E` is both twin-sufficient and parity-invariant"* | open |
| 6 | `t7_short` | **Nature :1** — *"the"* | open |

2 LANDED · 7 OPEN
2 landed · 4 open
"""


def self_test() -> int:
    import tempfile
    print("=" * 78)
    print("SELF-TEST — each case plants a failure (or a control) and names the verdict")
    print("=" * 78)
    with tempfile.TemporaryDirectory() as td:
        d = Path(td)
        (d / "pi.tex").write_text(_SELF_PI, encoding="utf-8")
        (d / "nat.md").write_text(_SELF_NATURE, encoding="utf-8")
        saved = dict(PAPERS)
        PAPERS.clear()
        PAPERS.update({"Pi": d / "pi.tex", "Nature": d / "nat.md"})
        try:
            import io
            import contextlib
            buf = io.StringIO()
            papers = load_papers()
            with contextlib.redirect_stdout(buf):
                arms_1_and_2(_SELF_DOC, papers, False)
                arm3(_SELF_DOC)
            out = buf.getvalue()
        finally:
            PAPERS.clear()
            PAPERS.update(saved)

    cases = [
        ("T1 notation crossing  (Unicode Ω≤ vs LaTeX \\Omega\\le)",
         "must be OK — this is the false MISS the predecessor produced",
         lambda o: 'OK   phrase "Ω(p(p+2))' in o),
        ("T2 pin rot +1         (phrase on :2, pinned :1, no environment)",
         "must DRIFT — the known rot signature, never absorbed",
         lambda o: "DRIFT" in o and "t2" not in o.split("row 2")[1].split("row 3")[0].replace("DRIFT", "")
                   or "DRIFT" in o.split("row 2")[1].split("row 3")[0]),
        ("T3 wrapped sentence   (phrase spans two paper lines)",
         "must be OK with a SPAN — reporting only the first line fakes a rot",
         lambda o: "Pi@9-10" in o and "OK" in o.split("row 3")[1].split("row 4")[0]),
        ("T4 cross-paper leak   (phrase only in Nature, pinned under Pi)",
         "must MISS — segmentation must stop a Nature phrase passing as Pi",
         lambda o: "MISS" in o.split("row 4")[1].split("row 5")[0]),
        ("T5 environment pin    (pin opens \\begin{theorem}, phrase inside)",
         "must be OK — established by READING the env, not by a tolerance",
         lambda o: "sits inside it" in o),
        ("T6 count inversion    (doc says 2 LANDED/7 OPEN; rows say 2/4)",
         "must flag OPEN and NOT flag LANDED — the set-equal check missed this",
         lambda o: "open=7(truth 4)" in o),
        ("T7 short phrase       (a two-letter quote)",
         "must SKIP WITH REASON — never vanish silently",
         lambda o: "too short to be evidence" in o),
    ]
    npass = 0
    for name, expect, pred in cases:
        try:
            got = bool(pred(out))
        except Exception:
            got = False
        npass += got
        print(f"\n  [{'PASS' if got else 'FAIL'}] {name}")
        print(f"         {expect}")
    print(f"\n  {npass}/{len(cases)} planted cases behaved as pre-registered")
    if npass != len(cases):
        print("\n--- full self-test output, so a FAIL can be read rather than guessed ---")
        print(out)
    return 0 if npass == len(cases) else 1


CERT_POPULATIONS = [
    REPO / "Salt" / "Certs",
    REPO.parent / "saltworks" / "SaltWorks" / "Certs",
]

_IDENTLIKE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'₁-₉]*$")
# "8680167^:main.tex:645" — a quote pinned to a PAST revision of a named file.
_ATTRIB = re.compile(r"\b(Pi|Nature|paper|main\.tex|flagship)\b")
_REVPIN = re.compile(r"`?([0-9a-f]{7,40}\^*):([\w/.-]+\.(?:tex|md)):(\d+)`?")


def check_at_revision(rev: str, relpath: str, phrase: str) -> tuple[bool, str]:
    """Verify a historically-pinned quote against the revision it names.

    "The tool cannot check a past revision" is a cop-out when `git show` can.
    A quote pinned to a prior commit makes a claim about THAT file state, and
    today's file can neither confirm nor refute it -- so ask the object.
    """
    import subprocess
    name = Path(relpath).name
    target = next((p for p in PAPERS.values() if p.name == name), None)
    if target is None:
        return False, f"pinned to {relpath}, which is not a known paper — UNRESOLVED"
    repo = REPO if REPO in target.parents else REPO.parent
    inrepo = target.relative_to(repo)
    try:
        out = subprocess.run(["git", "-C", str(repo), "show", f"{rev}:{inrepo}"],
                             capture_output=True, text=True, timeout=20)
    except Exception as e:                                   # noqa: BLE001
        return False, f"could not run git show ({e}) — UNRESOLVED, not passed"
    if out.returncode != 0:
        return False, (f"`git show {rev}:{inrepo}` failed: "
                       f"{out.stderr.strip()[:60]} — UNRESOLVED, not passed")
    spans = find_span(out.stdout.splitlines(), phrase)
    if spans:
        return True, (f"present at {rev}:{inrepo}@{fmt_spans(spans)} — the historical"
                      " pin is CORRECT, and correctly absent from today's file")
    return False, (f"NOT present at {rev}:{inrepo} either — the historical pin does"
                   " not rescue it")


def arm6(show_norm: bool) -> int:
    """Every quoted string in every certificate, checked against the papers.

    Routed here by evidence (10:12): their seals read ONE quote per cert -- the
    certified one -- so ~44 quoted strings across both populations had never
    been read by any seal, and the two that a tool did read were both rotted.

    This is NOT what ARM 1 does.  ARM 1 sweeps the anchor DOC; this sweeps the
    CERT FILES.  Same kind of check, different population, and saying "the tool
    already does it" would have left the sweep undone.

    Every quoted string is printed with a verdict or a NAMED reason for not
    grading one -- the population is the point, so nothing may vanish quietly.

    UNMARKED ELISION (compiler, 10:12) is diagnosed separately: a quote whose
    words all appear, in order, with text silently dropped under an em-dash.
    Fragments are split ONLY on an ellipsis, which is an HONEST omission marker
    the reader can see; an em-dash is the source's own punctuation, so splitting
    on it would let an unmarked elision pass fragment-wise.  When the whole
    string misses but its em-dash pieces each hit the same paper, that is the
    signature and it is reported as such rather than as a generic MISS.
    """
    print()
    print("=" * 78)
    print("ARM 6 — EVERY QUOTED STRING IN EVERY CERTIFICATE, vs the papers")
    print("=" * 78)
    papers = load_papers()
    files = []
    for pop in CERT_POPULATIONS:
        if pop.is_dir():
            files += sorted(pop.glob("*.lean"))
        else:
            print(f"  population MISSING: {pop}")
    print(f"  populations: {len(files)} cert file(s)")
    print("  GRADED AGAINST: Pi + Nature. The saltworks population is counted but NOT")
    print("  graded — compiler (10:13): its cert sources are a BRIEF and the BUS, both")
    print("  outside the paper set, so grading them here would manufacture MISSes and")
    print("  a green run would be SILENT about those files, not clean about them.")

    total = graded = miss = elision = 0
    attrib_miss: list[str] = []
    skipped: dict[str, int] = {}
    for f in files:
        in_scope = REPO in f.parents
        lines = f.read_text(encoding="utf-8", errors="replace").splitlines()
        rel = f"{f.parent.parent.parent.name}/{f.parent.name}/{f.name}"
        printed_header = False
        for i, line in enumerate(lines, 1):
            for q in _PHRASE.findall(line):
                total += 1
                n = normalise(q)
                if not in_scope:
                    skipped["saltworks: sources are a brief and the bus, not the papers"] = \
                        skipped.get("saltworks: sources are a brief and the bus, not the papers", 0) + 1
                    continue
                if len(n) < MIN_PHRASE:
                    skipped["too short to be evidence"] = \
                        skipped.get("too short to be evidence", 0) + 1
                    continue
                if _IDENTLIKE.match(q.strip()) or ".lean" in q:
                    skipped["a Lean identifier or path, not a quotation"] = \
                        skipped.get("a Lean identifier or path, not a quotation", 0) + 1
                    continue
                graded += 1
                hits = {p: find_span(ls, q) for p, ls in papers.items()}
                hits = {p: s for p, s in hits.items() if s}
                if hits:
                    continue
                # Not contiguous in either paper.  Is it an UNMARKED ELISION?
                pieces = [x.strip() for x in re.split(r"\s[–—-]\s", q)
                          if len(normalise(x)) >= MIN_PHRASE]
                elided = None
                if len(pieces) >= 2:
                    for p, ls in papers.items():
                        if all(find_span(ls, x) for x in pieces):
                            elided = p
                            break
                # A quote may be pinned to a PAST revision ("8680167^:main.tex:645").
                # Today's file cannot refute a claim about yesterday's, so the tool
                # asks the object it names -- `git show` -- instead of reporting a
                # MISS it has not earned.
                rev = _REVPIN.search(line)
                if rev:
                    ok, note = check_at_revision(rev.group(1), rev.group(2), q)
                    if not printed_header:
                        print(f"\n  {rel}")
                        printed_header = True
                    print(f"   {'HIST-OK' if ok else 'HIST-BAD'} :{i} \"{q[:52]}\"")
                    print(f"        {note}")
                    if not ok:
                        miss += 1
                    continue
                if not printed_header:
                    print(f"\n  {rel}")
                    printed_header = True
                if elided:
                    elision += 1
                    print(f"   ELISION? :{i} \"{q[:60]}\"")
                    print(f"        every em-dash piece is in {elided}, the whole string is"
                          " not — words dropped under punctuation the reader reads as"
                          " the source's own")
                else:
                    miss += 1
                    # Tier by whether the line CLAIMS the paper. "nothing is
                    # traded" is a cert quoting itself; "Pi's ... 'X'" claims to
                    # be Pi's words.  Both are printed -- the tier is a reading
                    # ORDER, not a filter, and this is a QUERY so its marker list
                    # is a floor.
                    # Test the line WITHOUT the quote: 'one paper phrase' has
                    # 'paper' INSIDE the quotation, which is the quote's own
                    # words, not an attribution.  4th instance of prose inside
                    # a quote being read as structure -- same file, same day.
                    attributed = bool(_ATTRIB.search(line.replace(q, " ")))
                    if attributed:
                        attrib_miss.append(f"{rel}:{i}  \"{q[:50]}\"")
                    print(f"   MISS{'*' if attributed else ' '} :{i} \"{q[:60]}\"")
                    print("        in NEITHER paper — "
                          + ("the LINE NAMES A PAPER, so this quote claims to be its"
                             " words: read FIRST"
                             if attributed else
                             "no paper named on this line; likely the cert quoting"
                             " itself or plain emphasis"))
                if show_norm:
                    print(f"        normalised: {n!r}")

    print(f"\n  population {total} quoted strings · {graded} graded ·"
          f" {total - graded} not graded")
    for reason, k in sorted(skipped.items()):
        print(f"      {k:>3} not graded — {reason}")
    print(f"  {miss} not found in either paper ({len(attrib_miss)} of them ATTRIBUTED) · {elision} unmarked-elision signature")
    for a_ in attrib_miss:
        print(f"      MISS* {a_}")
    print("\n  NOT a defect count: a MISS may be an honest quote of the corpus or plain"
          "\n  emphasis. It is a READ LIST, and its denominator is printed above so it"
          "\n  can be reconciled against an independently-patterned count.")
    return miss + elision


CERTS = REPO / "Salt" / "Certs"
AGGREGATE = "All.lean"      # roll-call/import hub, NOT a certificate


def arm5(doc_text: str) -> int:
    """The row MARKS against the CORPUS — the check ARM 3 structurally cannot do.

    ARM 3 derives LANDED/OPEN from the table's own ✅ marks, so it is internally
    consistent and can still be externally wrong: if a cert lands and nobody
    re-marks its row, ARM 3 certifies a stale total against a stale list and
    reports clean.  That is exactly what happened -- rows 4, 5 and 12 were
    marked open while their certs sat in Salt/Certs/.

    Mention is NOT coverage, and this arm refuses to guess: `Chen.lean` names
    `chen_goldbach` only to say "not this file".  So it prints the mentioning
    LINES and asks for a read, rather than converting a name-hit into a verdict.
    """
    print()
    print("=" * 78)
    print("ARM 5 — ROW MARKS vs THE CORPUS (mention is not coverage: read the lines)")
    print("=" * 78)
    if not CERTS.is_dir():
        print(f"  SKIP: {CERTS} not a directory — cannot check marks against corpus")
        return 0
    files = sorted(p for p in CERTS.glob("*.lean") if p.name != AGGREGATE)
    print(f"  cert corpus: {len(files)} file(s), excluding the aggregate {AGGREGATE}")
    bodies = {p: p.read_text(encoding="utf-8", errors="replace").splitlines()
              for p in files}
    disagree = 0
    for rownum, line in table_rows(doc_text):
        cs = cells(line)
        if len(cs) < 4:
            continue
        landed_mark = cs[-1].startswith("✅")
        names = [n for n in _LABEL.findall(cs[1]) if len(n) > 3]
        hits: dict[str, list[str]] = {}
        for n in names:
            for p, ls in bodies.items():
                for j, l in enumerate(ls, 1):
                    if n in l:
                        hits.setdefault(n, []).append(f"{p.name}:{j}")
        covered = bool(hits)
        if covered == landed_mark:
            state = "✅ landed" if landed_mark else "open"
            print(f"   ok row {rownum:<3} mark={state:<9} corpus agrees")
            continue
        # A recorded READ resolves the row.  The tool never decides coverage --
        # it surfaces the disagreement and a human writes the resolution INTO
        # the doc, where the next reader sees it.  Suppressing it in the script
        # instead would hide the reasoning in the one place nobody opens, and a
        # permanently-red arm trains its readers to ignore it.
        m = re.search(r"ARM5-READ:\s*([^|]+)", cs[-1])
        if m:
            print(f"   ok row {rownum:<3} mark differs from the name-hit, RESOLVED by a"
                  f" recorded read:\n        {m.group(1).strip()[:88]}")
            continue
        disagree += 1
        print(f"\n   !! row {rownum:<3} mark={'✅ landed' if landed_mark else 'open':<9}"
              f" but corpus says {'covered' if covered else 'NO cert file mentions it'}")
        for n, where in hits.items():
            print(f"        `{n}` mentioned at {', '.join(where[:4])}")
            for w in where[:2]:
                fn, ln = w.rsplit(":", 1)
                src = bodies[CERTS / fn][int(ln) - 1].strip()
                print(f"           {w}  {src[:64]}")
        if not hits:
            print(f"        no cert file mentions {names}")
    print(f"\n  ARM 5: {disagree} row(s) whose mark and corpus disagree"
          " — each needs a READ, not a rewrite by this tool")
    return disagree


_PROSE_PIN = re.compile(r"`?([\w./-]+\.(?:tex|md|lean)):(\d{1,5})`?")


def arm4(doc_text: str) -> int:
    """Pins in PROSE, outside the table — the class ARM 1 structurally cannot see.

    ARM 1 walks table ROWS.  A pin written in a paragraph is invisible to it, so
    a green ARM 1 would license "the doc's pins are swept" while a whole class
    went unread.  This arm prints what is AT each prose pin; a reader judges
    intent, but nobody has to take the pin on trust.
    """
    print()
    print("=" * 78)
    print("ARM 4 — PINS IN PROSE (outside the table; ARM 1 never reaches these)")
    print("=" * 78)
    rows = {ln for ln, _ in table_rows(doc_text)}
    del rows
    tablelines = {l for _, l in table_rows(doc_text)}
    bad = 0
    found = 0
    unresolved: list[str] = []
    for i, line in enumerate(doc_text.splitlines(), 1):
        if line in tablelines:
            continue
        for m in _PROSE_PIN.finditer(line):
            rel, pin = m.group(1), int(m.group(2))
            found += 1
            # A pin is often written as a bare basename ("main.tex:1261"), so
            # resolve against the papers this table already names before giving up.
            cand = [REPO / rel, REPO.parent / rel]
            cand += [p for p in PAPERS.values() if p.name == Path(rel).name]
            path = next((c for c in cand if c.exists()), None)
            if path is None:
                print(f"   ?? :{i:<4} {rel}:{pin} — UNRESOLVED, no file at "
                      f"{' or '.join(str(c) for c in cand[:2])}")
                unresolved.append(f"{rel}:{pin} (doc line {i})")
                continue
            plines = path.read_text(encoding="utf-8", errors="replace").splitlines()
            if not (1 <= pin <= len(plines)):
                print(f"   !! :{i:<4} {rel}:{pin} — beyond EOF ({len(plines)} lines)")
                bad += 1
                continue
            at = plines[pin - 1].strip()
            phrases = [p for p in _PHRASE.findall(line)
                       if len(normalise(p)) >= MIN_PHRASE]
            verdict = "  "
            note = ""
            if phrases:
                spans = []
                for ph in phrases:
                    spans += find_span(plines, ph)
                if spans and not any(spans_cover(spans, pin) for _ in [0]):
                    verdict = "!!"
                    bad += 1
                    note = (f"\n          quoted phrase actually at {fmt_spans(spans)}"
                            f" — pin {pin} is not inside it")
                elif spans:
                    note = "\n          quoted phrase confirmed at the pin"
                else:
                    note = "\n          quoted phrase NOT found in this file at all"
                    verdict = "!!"
                    bad += 1
            print(f"   {verdict} :{i:<4} {rel}:{pin} -> {at[:66]}{note}")
    if unresolved:
        print("\n  UNRESOLVED — read but NOT checked. A clean ARM 4 does not cover")
        print("  these, so they are NAMED rather than counted as passing:")
        for u in unresolved:
            print(f"      {u}")
    print(f"\n  ARM 4: {found} prose pin(s) read · {bad} unsupported"
          f" · {len(unresolved)} unresolved")
    return bad + len(unresolved)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--doc", default=str(DEFAULT_DOC))
    ap.add_argument("--self-test", action="store_true",
                    help="run the planted-failure suite instead of the real doc")
    ap.add_argument("--show-normalised", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    doc = Path(args.doc)
    if not doc.exists():
        print(f"cannot run: {doc} missing", file=sys.stderr)
        return 2
    text = doc.read_text(encoding="utf-8", errors="replace")
    papers = load_papers()
    if not papers:
        print("cannot run: no papers readable", file=sys.stderr)
        return 2

    print(f"anchor doc : {doc}")
    for n, p in PAPERS.items():
        print(f"paper {n:<7}: {p}  "
              f"({len(papers[n])} lines)" if n in papers else f"paper {n}: MISSING")

    _, drift, _ = arms_1_and_2(text, papers, args.show_normalised)
    bad = arm3(text)
    prose = arm4(text)
    marks = arm5(text)
    certs = arm6(args.show_normalised)

    print("\n" + "=" * 78)
    if drift or bad or prose or marks or certs:
        print(f"RESULT: NOT CLEAN — {drift} pin drift · {bad} count mismatch"
              f" · {prose} prose pin · {marks} stale mark · {certs} cert quote")
        return 1
    print("RESULT: clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
