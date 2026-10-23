#!/usr/bin/env python3
"""Check that threading a hypothesis through declarations left every original statement unchanged.

For a branch that adds `NAME_of_SW (hSWall : Salt.BV.SiegelWalfisz)` forms and keeps each
`NAME` as a wrapper, this lists every `NAME_of_SW` the branch adds (against BASE), and for each:

  TEXT  the statement of `NAME` (from its keyword to the first top-level `:=`) is byte-identical
        at BASE and at HEAD;
  FORM  the statement of `NAME_of_SW` at HEAD is the BASE statement of `NAME` with exactly the
        binder ` (hSWall : Salt.BV.SiegelWalfisz)` inserted after the name, up to whitespace
        (the long headers are re-wrapped).

It prints the population, a line per name, and a CONTROL: one statement with one character
changed must read DIFFERENT, or the check exits 3. With `--lean FILE` it also writes
`#assert_conclusion_is NAME_of_SW 1 NAME` for every name, so a build of FILE checks the
elaborated types as `Expr`s.

Usage: python3 scripts/check_threaded_statements.py [--base origin/main] [--lean Scratch.lean]
Exit: 0 all identical · 1 a statement differs · 3 the control failed.
"""
import argparse, re, subprocess, sys

BINDER = ' (hSWall : Salt.BV.SiegelWalfisz)'
DECL = r'^(?:private )?(?:theorem|lemma) '

def git(*a):
    return subprocess.run(['git', *a], capture_output=True, text=True, check=True).stdout

def statement(src, name):
    m = re.search(DECL + re.escape(name) + r'(?=[\s:({\[⦃])', src, re.M)
    if not m:
        return None
    # the first top-level `:=`, skipping `--` and `/- -/` comments and string literals (a `:=` in a
    # comment inside a statement must not end it)
    depth, block, i, n = 0, 0, m.end(), len(src)
    while i < n - 1:
        if block:
            if src.startswith('/-', i):
                block += 1; i += 2; continue
            if src.startswith('-/', i):
                block -= 1; i += 2; continue
            i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if src.startswith('/-', i):
            block = 1; i += 2; continue
        c = src[i]
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            i = j + 1; continue
        if c in '([{⦃':
            depth += 1
        elif c in ')]}⦄':
            depth -= 1
        elif depth == 0 and src.startswith(':=', i):
            return src[m.start():i]
        i += 1
    return None

def squash(s):
    return ' '.join(s.split())

def same_text(sb, sh):
    return sb is not None and sb == sh

def same_form(sb, sw, n):
    want = None if sb is None else sb.replace(n, n + '_of_SW' + BINDER, 1)
    return want is not None and sw is not None and squash(want) == squash(sw)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', default='origin/main')
    ap.add_argument('--lean')
    a = ap.parse_args()
    diff = git('diff', '--name-only', a.base, '--', 'Salt')
    files = [f for f in diff.split() if f.endswith('.lean')]
    names, passed, bad = [], [], 0
    for f in files:
        try:
            base = git('show', f'{a.base}:{f}')
        except subprocess.CalledProcessError:
            base = ''
        head = open(f).read()
        added = set(re.findall(DECL + r'(\S+)_of_SW\b', head, re.M)) - set(
            re.findall(DECL + r'(\S+)_of_SW\b', base, re.M))
        for n in sorted(added):
            sb, sh, sw = statement(base, n), statement(head, n), statement(head, n + '_of_SW')
            text_ok, form_ok = same_text(sb, sh), same_form(sb, sw, n)
            bad += not (text_ok and form_ok)
            names.append(n)
            if text_ok and form_ok:
                passed.append(n)
            print(f'{"OK  " if text_ok and form_ok else "DIFF"} {f} {n} '
                  f'text={"identical" if text_ok else "DIFFERENT"} '
                  f'form={"binder-only" if form_ok else "DIFFERENT"} ({0 if sb is None else len(sb.encode())} B)')
    # control: both predicates, run on a statement with one character changed, must reject it
    ctrl_ok = False
    if passed:
        n0 = passed[0]
        src0 = next(open(f).read() for f in files if statement(open(f).read(), n0) is not None)
        s0, w0 = statement(src0, n0), statement(src0, n0 + '_of_SW')
        k = s0.rfind('0')
        k = k if k > 0 else len(s0) - 1
        mutated = s0[:k] + ('1' if s0[k] != '1' else '2') + s0[k + 1:]
        t_rejects, f_rejects = not same_text(mutated, s0), not same_form(mutated, w0, n0)
        ctrl_ok = t_rejects and f_rejects and same_text(s0, s0) and same_form(s0, w0, n0)
        print(f'CONTROL {n0}, one character changed: TEXT reads {"DIFFERENT" if t_rejects else "IDENTICAL"}, '
              f'FORM reads {"DIFFERENT" if f_rejects else "IDENTICAL"}; unchanged reads identical: '
              f'{same_text(s0, s0) and same_form(s0, w0, n0)}')
    print(f'POPULATION {len(names)} threaded declarations in {len(files)} files against {a.base}; '
          f'{len(names) - bad} identical, {bad} different')
    if a.lean:
        mods = sorted({f[:-5].replace('/', '.') for f in files})
        with open(a.lean, 'w') as out:
            out.write(''.join(f'import {m}\n' for m in mods))
            out.write('import Salt.SW.StandoffCert\nopen Salt.SW.StandoffCert\n')
            for n in names:
                full = fullname(n, files)
                out.write(f'#assert_conclusion_is {full}_of_SW 1 {full}\n')
    if not ctrl_ok:
        sys.exit(3)
    sys.exit(1 if bad else 0)

def fullname(n, files):
    for f in files:
        src = open(f).read()
        if statement(src, n) is not None:
            m = list(re.finditer(r'^namespace (\S+)', src[:src.find(statement(src, n))], re.M))
            return (m[-1].group(1) + '.' if m else '') + n
    return n

main()
