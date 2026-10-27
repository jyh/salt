#!/usr/bin/env python3
"""The import rule of the C1 certificates: `SaltC1/Cert54/` imports Mathlib and Lean ONLY.

The k = 54 certificate is checked by its own CI job against Mathlib alone, so nothing under
`SaltC1/Cert54/` may import the `Salt` library or the Maynard chain that consumes it
(`SaltC1.MaynardK`). An import of another `SaltC1.Cert54` module is allowed; so are `Mathlib`,
`Lean`, `Init` and `Std`. Anything else fails, naming the file and the line.

The scan reads the module header the way Lean's parser does -- comments stripped, whitespace-
insensitive -- so an import a line-matcher cannot see (two on one line, the name on the line after
`import`, a comment before the import on its line) is still read. The self-test plants each form.

usage:  python3 scripts/check_cert_imports.py              # the working tree
        python3 scripts/check_cert_imports.py --rev <sha>  # the tree of a commit (the pre-push arm)
        python3 scripts/check_cert_imports.py --self-test  # plant a refused import in a copy; must FAIL
Exit 0 clean, 1 on a refused import, 2 when it could not look (an empty scan of the working tree is not
a clean scan; a commit with no `SaltC1/Cert54/` passes with a line that says so).
"""
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT_DIR = "SaltC1/Cert54"
ALLOWED = ("Mathlib", "Lean", "Init", "Std", "SaltC1.Cert54")
HEADER_MODIFIERS = ("public", "private", "meta")


def strip_comments(text):
    """Every comment replaced by spaces, newlines kept (so line numbers survive). Lean's comments are
    `--` to the end of the line and `/- ... -/`, which nests. The header carries no string literal and
    the scan stops at the first non-header token, so strings are not modelled."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def header_imports(text):
    """The imports of the module header as Lean reads them: `module`? `prelude`? then
    (`public`|`private`|`meta`)* `import` `all`? NAME, repeated, until the first token that is none
    of those. Returns (line number, module name) pairs."""
    src = strip_comments(text)
    toks = [(m.start(), m.group(0)) for m in re.finditer(r"\S+", src)]
    out = []
    i = 0
    if i < len(toks) and toks[i][1] == "module":
        i += 1
    if i < len(toks) and toks[i][1] == "prelude":
        i += 1
    while i < len(toks):
        while i < len(toks) and toks[i][1] in HEADER_MODIFIERS:
            i += 1
        if i >= len(toks) or toks[i][1] != "import":
            break
        i += 1
        if i < len(toks) and toks[i][1] == "all":
            i += 1
        if i >= len(toks):
            break
        pos, name = toks[i]
        out.append((src.count("\n", 0, pos) + 1, name))
        i += 1
    return out


def allowed(mod):
    return any(mod == a or mod.startswith(a + ".") for a in ALLOWED)


def scan(files):
    """files: (path, text) pairs -> list of (path, line number, module)."""
    bad = []
    for path, text in files:
        for n, mod in header_imports(text):
            if not allowed(mod):
                bad.append((path, n, mod))
    return bad


def tree_files(root):
    base = Path(root) / ROOT_DIR
    return [(str(p.relative_to(root)), p.read_text(encoding="utf-8")) for p in sorted(base.rglob("*.lean"))]


def rev_files(rev):
    out = subprocess.run(["git", "ls-tree", "-r", "--name-only", rev, "--", ROOT_DIR],
                         capture_output=True, text=True, check=True).stdout.split()
    files = []
    for path in out:
        if path.endswith(".lean"):
            text = subprocess.run(["git", "show", "%s:%s" % (rev, path)],
                                  capture_output=True, text=True, check=True).stdout
            files.append((path, text))
    return files


def report(files, where):
    if not files:
        print("check_cert_imports: NO .lean file under %s/ in %s -- nothing scanned (not clean)" % (ROOT_DIR, where))
        return 2
    bad = scan(files)
    for path, n, mod in bad:
        print("%s:%d: refused import `%s` (only %s are allowed under %s/)"
              % (path, n, mod, ", ".join(ALLOWED), ROOT_DIR))
    if bad:
        return 1
    print("check_cert_imports OK: %d file(s) under %s/ in %s import only %s"
          % (len(files), ROOT_DIR, where, ", ".join(ALLOWED)))
    return 0


# The self-test's plants: (text, where, the exit the gate MUST return). `top` prepends to Data.lean,
# `end` appends. The first three are refused NAMES in the plain form; the next three are the header
# FORMS Lean accepts that a one-import-per-line matcher cannot see (the A5 refuter pass, FX2: a comment
# before the import on the same line, two imports on one line, the module name on the line after
# `import`); the last three are negative controls -- the word inside a comment or a string is NOT an
# import, and a clean copy must stay clean.
PLANTS = (
    ("import Salt.MaynardK.Cert105\n", "top", 1),
    ("import SaltC1.MaynardK.Cert54Stub\n", "top", 1),
    ("import Salt\n", "top", 1),
    ("/- a comment before the import, on its line -/ import Salt\n", "top", 1),
    ("import Mathlib import Salt\n", "top", 1),
    ("import\n  Salt\n", "top", 1),
    ("-- import Salt\n", "top", 0),
    ("/- import Salt -/\n", "top", 0),
    ('def hdrProbe : String := "import Salt"\n', "end", 0),
)


def self_test(root):
    with tempfile.TemporaryDirectory() as tmp:
        dst = Path(tmp) / ROOT_DIR
        shutil.copytree(Path(root) / ROOT_DIR, dst)
        clean = report(tree_files(tmp), "a clean copy")
        results = []
        for planted, where, want in PLANTS:
            target = dst / "Data.lean"
            orig = target.read_text(encoding="utf-8")
            target.write_text(planted + orig if where == "top" else orig + planted, encoding="utf-8")
            rc = report(tree_files(tmp), "a copy with %r planted at the %s" % (planted, where))
            target.write_text(orig, encoding="utf-8")
            results.append((planted, where, want, rc))
    ok = clean == 0 and all(rc == want for _, _, want, rc in results)
    for planted, where, want, rc in results:
        print("self-test: planted %r at the %s -> exit %d (must be %d)%s"
              % (planted, where, rc, want, "" if rc == want else "  <-- WRONG"))
    print("self-test: clean copy -> exit %d (must be 0)" % clean)
    print("self-test %s" % ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1


def main(argv):
    root = Path(__file__).resolve().parents[1]
    if argv[1:] == ["--self-test"]:
        return self_test(root)
    if len(argv) == 3 and argv[1] == "--rev":
        try:
            files = rev_files(argv[2])
        except subprocess.CalledProcessError as e:
            print("check_cert_imports: could not read %s: %s" % (argv[2], e.stderr.strip()))
            return 2
        if not files:
            # a commit that predates the certificate carries no import to check: say so, in words
            print("check_cert_imports OK: commit %s has no %s/ -- the rule has nothing to rule on" % (argv[2], ROOT_DIR))
            return 0
        return report(files, "commit %s" % argv[2])
    if len(argv) == 1:
        return report(tree_files(root), "the working tree")
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
