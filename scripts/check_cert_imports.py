#!/usr/bin/env python3
"""The import rule of the C1 certificates: `SaltC1/Cert54/` imports Mathlib and Lean ONLY.

The k = 54 certificate is checked by its own CI job against Mathlib alone, so nothing under
`SaltC1/Cert54/` may import the `Salt` library or the Maynard chain that consumes it
(`SaltC1.MaynardK`). An import of another `SaltC1.Cert54` module is allowed; so are `Mathlib`,
`Lean`, `Init` and `Std`. Anything else fails, naming the file and the line.

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
IMPORT = re.compile(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»']+)")


def allowed(mod):
    return any(mod == a or mod.startswith(a + ".") for a in ALLOWED)


def scan(files):
    """files: (path, text) pairs -> list of (path, line number, module)."""
    bad = []
    for path, text in files:
        for n, line in enumerate(text.splitlines(), 1):
            m = IMPORT.match(line)
            if m and not allowed(m.group(1)):
                bad.append((path, n, m.group(1)))
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


def self_test(root):
    with tempfile.TemporaryDirectory() as tmp:
        dst = Path(tmp) / ROOT_DIR
        shutil.copytree(Path(root) / ROOT_DIR, dst)
        clean = report(tree_files(tmp), "a clean copy")
        results = []
        for planted in ("import Salt.MaynardK.Cert105", "import SaltC1.MaynardK.Cert54Stub", "import Salt"):
            target = dst / "Data.lean"
            orig = target.read_text(encoding="utf-8")
            target.write_text(planted + "\n" + orig, encoding="utf-8")
            rc = report(tree_files(tmp), "a copy with `%s` planted" % planted)
            target.write_text(orig, encoding="utf-8")
            results.append((planted, rc))
    ok = clean == 0 and all(rc == 1 for _, rc in results)
    for planted, rc in results:
        print("self-test: planted `%s` -> exit %d (must be 1)" % (planted, rc))
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
