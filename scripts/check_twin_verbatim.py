#!/usr/bin/env python3
"""THE STANDOFF-TWIN VERBATIM CHECK (objective O13, STATUS row 306).

A `⟦STANDOFF TWIN⟧` declaration restates a source theorem under the three standoff binders
(`{cS : ℝ} (hcS : 0 < cS) (hSieg : Salt.SW.NoSiegelZerosAt cS)`) and, when its docstring says
`verbatim`, claims that its proof body IS the source's body. This check reads every such claim and
compares the two bodies token by token, after the child swap the twin family makes by
construction:

  * every `_of_standoff` suffix is dropped (a twin calls the twins of the source's callees);
  * the standoff binders and the names `hcS` · `hSieg` are dropped (the twin passes them on);
  * `siegel_real_carve` ↔ `standoff_real_carve` when the docstring names `siegel_real_carve`;
  * comments are dropped, and a parenthesis around a single token is dropped.

A claim passes when the two token sequences are EQUAL. Any other difference is a finding (exit 1),
printed with its first differing tokens.

THE DOCSTRING IS READ WHOLE: the source name is the first backticked name after the marker, and the
source file is the first `(`File.lean:N`)` or `(`File.lean`)` after that name, wherever the line
breaks fall. (An earlier one-line reader missed the twins whose header wraps.)

Usage:
  python3 scripts/check_twin_verbatim.py              check every claim; exit 1 on any finding
  python3 scripts/check_twin_verbatim.py --self-test  the fixture and its mutants; exit 0 iff all hold

LIMITS, printed with every verdict:
  * Source-level only: it compares TEXT after the swap, never elaborated terms. Equal tokens with a
    different elaboration context (a `variable`, an `open`, a `set_option`) are not seen.
  * A twin whose docstring does not contain the word `verbatim` makes no claim and is only counted.
  * A source it cannot resolve (no file, an ambiguous leaf, no such theorem in the file) is a
    finding, not a pass.
  * The swap list above is the whole of what it forgives. A twin that differs in any other way is
    reported even when the difference is harmless.
  * Layout is not seen: tokens are compared without indentation, so a tactic moved under a
    different `have` with the same tokens passes.
  * A twin is found by its docstring marker, never by its name: an `_of_standoff` declaration with
    no `⟦STANDOFF TWIN⟧` docstring is not counted at all.
  * A body is the text after the declaration's first `:=`; an empty body on either side (no `:=`,
    e.g. equation style) is a finding, never an equal pair.
"""
from __future__ import annotations

import difflib
import glob
import os
import re
import sys

MARK = '/-- **⟦STANDOFF TWIN⟧**'
DECL_START = re.compile(r'(?:private |protected )?(?:theorem|lemma) ')
DECL_END = re.compile(r'(theorem|lemma|def|noncomputable|abbrev|structure|instance|/--|/-!|end( |$)|'
                      r'set_option|@\[|#|namespace|section|open )')
LIMITS = ('LIMITS: source-level token compare after the swap (no elaboration context, no layout); a twin '
          'is found by its docstring marker, not its name; a twin without `verbatim` makes no claim; an '
          'unresolved source or an empty body is a finding; only the listed swaps are forgiven.')


def decl_text(lines: list[str], start: int) -> str:
    """The declaration starting at `start`, up to the next top-level command."""
    j = start + 1
    while j < len(lines) and not DECL_END.match(lines[j]):
        j += 1
    return '\n'.join(lines[start:j])


def find_decl(lines: list[str], name: str) -> int | None:
    pat = re.compile(r'(?:private |protected )?(?:theorem|lemma) ' + re.escape(name) + r'(\s|$)')
    hits = [k for k, l in enumerate(lines) if pat.match(l)]
    return hits[0] if len(hits) == 1 else None


def toks(body: str, swaps: list[tuple[str, str]]) -> list[str]:
    s = re.sub(r'/-.*?-/', '', body, flags=re.S)
    s = re.sub(r'--[^\n]*', '', s)
    s = s.replace('_of_standoff', '')
    s = s.replace('{cS : ℝ} (hcS : 0 < cS)', '').replace('(hSieg : Salt.SW.NoSiegelZerosAt cS)', '')
    for a, b in swaps:
        s = re.sub(r'(?<![A-Za-z0-9_.])' + re.escape(b) + r"(?![A-Za-z0-9_'])", a, s)
    t = re.findall(r"[A-Za-z0-9_.'₀-₉ℝℚℕ]+|[^\sA-Za-z0-9_.']", s)
    t = [x for x in t if x not in ('hcS', 'hSieg')]
    out, i = [], 0
    while i < len(t):
        if t[i] == '(' and i + 2 < len(t) and t[i + 2] == ')':
            out.append(t[i + 1])
            i += 3
            continue
        out.append(t[i])
        i += 1
    return out


def body_of(text: str) -> str:
    k = text.find(':=')
    return text[k + 2:] if k >= 0 else ''


def resolve(src: str, files: dict[str, list[str]]) -> str | None:
    if src in files:
        return src
    leaf = os.path.basename(src)
    hits = [f for f in files if os.path.basename(f) == leaf]
    return hits[0] if len(hits) == 1 else None


def check(files: dict[str, list[str]]) -> tuple[int, int, int, list[str]]:
    """Returns (twins, claims, findings, report lines)."""
    twins = claims = bad = 0
    report: list[str] = []
    for f in sorted(files):
        L = files[f]
        for i, l in enumerate(L):
            if not l.startswith(MARK):
                continue
            twins += 1
            j = i
            while j < len(L) and '-/' not in L[j]:
                j += 1
            doc = ' '.join(L[i:j + 1]).split('-/')[0]
            doc = ' '.join(doc.split())
            if 'verbatim' not in doc:
                continue
            claims += 1
            k = j + 1
            while k < len(L) and not DECL_START.match(L[k]):
                k += 1
            if k >= len(L):
                bad += 1
                report.append(f'FINDING {f}:{i + 1}: no theorem follows the twin docstring')
                continue
            tname = L[k].split()[1] if not L[k].startswith(('private', 'protected')) else L[k].split()[2]
            m = re.search(r'⟦STANDOFF TWIN⟧\*\* `([^`]+)` \(`([^`:]+?)(?::\d+(?:[-–]\d+)?)?`\)', doc)
            if not m:
                bad += 1
                report.append(f'FINDING {f}:{i + 1} {tname}: no `name` (`File.lean:N`) source in its docstring')
                continue
            sname, spath = m.group(1), m.group(2)
            sf = resolve(spath, files)
            if sf is None:
                bad += 1
                report.append(f'FINDING {f}:{i + 1} {tname}: source file `{spath}` does not resolve to one file')
                continue
            sk = find_decl(files[sf], sname)
            if sk is None:
                bad += 1
                report.append(f'FINDING {f}:{i + 1} {tname}: `{sname}` is not one theorem in {sf}')
                continue
            swaps = [('siegel_real_carve', 'standoff_real_carve')] if 'siegel_real_carve' in doc else []
            a = toks(body_of(decl_text(files[sf], sk)), swaps)
            b = toks(body_of(decl_text(L, k)), swaps)
            if not a or not b:
                bad += 1
                report.append(f'FINDING {f}:{k + 1} {tname} vs {sf}:{sk + 1} {sname}: an empty body '
                              f'(no `:=` read) on the {"source" if not a else "twin"} side; not compared')
                continue
            d = [x for x in difflib.ndiff(a, b) if x[:1] in '+-']
            if d:
                bad += 1
                report.append(f'FINDING {f}:{k + 1} {tname} vs {sf}:{sk + 1} {sname}: {len(d)} token(s) differ: '
                              + ' '.join(d[:12]))
    return twins, claims, bad, report


def load(root: str) -> dict[str, list[str]]:
    out = {}
    for p in sorted(glob.glob(os.path.join(root, 'Salt', '**', '*.lean'), recursive=True)):
        rel = os.path.relpath(p, root)
        with open(p, encoding='utf-8') as fh:
            out[rel] = fh.read().split('\n')
    return out


FIXTURE_SRC = '''theorem foo (x : Nat) (h : 0 < x) : 0 < x + 1 := by
  have h2 := bar h
  omega
'''
FIXTURE_TWIN_ONELINE = '''/-- **⟦STANDOFF TWIN⟧** `foo` (`Salt/Fix/Src.lean:1`): its statement under the three standoff
binders; the proof is `foo`'s verbatim. -/
theorem foo_of_standoff {cS : ℝ} (hcS : 0 < cS) (hSieg : Salt.SW.NoSiegelZerosAt cS)
    (x : Nat) (h : 0 < x) : 0 < x + 1 := by
  have h2 := bar_of_standoff hcS hSieg h
  omega
'''
FIXTURE_TWIN_WRAPPED = '''/-- **⟦STANDOFF TWIN⟧**
`foo` (`Src.lean:1`): its statement under the three standoff binders; verbatim. -/
theorem foo_of_standoff' {cS : ℝ} (hcS : 0 < cS) (hSieg : Salt.SW.NoSiegelZerosAt cS)
    (x : Nat) (h : 0 < x) : 0 < x + 1 := by
  have h2 := bar_of_standoff hcS hSieg h
  omega
'''


def self_test() -> int:
    ok = True

    def arm(name: str, cond: bool) -> None:
        nonlocal ok
        print(('PASS ' if cond else 'FAIL ') + name)
        ok = ok and cond

    def fx(twin_text: str, src_text: str = FIXTURE_SRC) -> dict[str, list[str]]:
        return {'Salt/Fix/Src.lean': src_text.split('\n'), 'Salt/Fix/Twin.lean': twin_text.split('\n')}

    for label, t in (('one-line header', FIXTURE_TWIN_ONELINE), ('wrapped header', FIXTURE_TWIN_WRAPPED)):
        tw, cl, bad, _ = check(fx(t))
        arm(f'{label}: the clean twin passes (1 twin, 1 claim, 0 findings)', (tw, cl, bad) == (1, 1, 0))
        mut = t.replace('  omega', '  simp; omega')
        assert mut != t
        arm(f'{label}: a planted token in the twin is a finding', check(fx(mut))[2] == 1)
        mut_src = FIXTURE_SRC.replace('bar h', 'baz h')
        assert mut_src != FIXTURE_SRC
        arm(f'{label}: a planted token in the source is a finding', check(fx(t, mut_src))[2] == 1)
        nov = t.replace('verbatim', 'transcribed')
        assert nov != t
        arm(f'{label}: no `verbatim` makes no claim', check(fx(nov))[:3] == (1, 0, 0))
        gone = t.replace('`foo`', '`foo_missing`', 1)
        assert gone != t
        arm(f'{label}: an unresolvable source name is a finding', check(fx(gone))[2] == 1)
        eq_src = 'theorem foo : ∀ n : Nat, 0 ≤ n\n  | 0 => le_rfl\n  | n + 1 => Nat.zero_le _\n'
        eq_twin = t.split('theorem ')[0] + ('theorem foo_of_standoff {cS : ℝ} (hcS : 0 < cS) '
                   '(hSieg : Salt.SW.NoSiegelZerosAt cS) : ∀ n : Nat, 0 ≤ n\n  | 0 => by simp\n'
                   '  | n + 1 => by omega\n')
        arm(f'{label}: an equation-style pair (no `:=`, empty bodies) is a finding',
            check(fx(eq_twin, eq_src))[2] == 1)
    return 0 if ok else 1


def main(argv: list[str]) -> int:
    if '--self-test' in argv:
        return self_test()
    if len(argv) > 0:
        print(__doc__)
        return 2
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    twins, claims, bad, report = check(load(root))
    for r in report:
        print(r)
    print(f'check_twin_verbatim: {twins} STANDOFF TWIN docstring(s), {claims} claim `verbatim`, '
          f'{bad} finding(s)')
    print(LIMITS)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
