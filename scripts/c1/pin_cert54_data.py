#!/usr/bin/env python3
"""The SHA-256 pins of `SaltC1/Cert54/data/` -- derived from the files, never typed.

`SaltC1/Cert54/Data.lean` carries `cert54Pins`, one `(file, sha256)` pair per data file, and refuses at
elaboration a file whose bytes differ (Lake does not track a file read by `IO.FS.readFile`, so without
the pins a changed table could be replayed from a stale build). This script is the pins' other half:

usage:  python3 scripts/c1/pin_cert54_data.py             # print the Lean table, from the files
        python3 scripts/c1/pin_cert54_data.py --check     # Data.lean's table against the files; exit 1
                                                          # on a mismatch, a missing pin or a missing file
        python3 scripts/c1/pin_cert54_data.py --self-test # a flipped byte and a stray file must FAIL
Exit 0 clean, 1 on a difference, 2 when it could not look (no pins parsed, no files found).
"""
import hashlib
import re
import shutil
import sys
import tempfile
from pathlib import Path

DATA_DIR = "SaltC1/Cert54/data"
LEAN = "SaltC1/Cert54/Data.lean"
PIN = re.compile(r'^\s*\("([^"]+)",\s*"([0-9a-f]{64})"\)', re.M)


def digests(data_dir):
    files = sorted(p for p in Path(data_dir).iterdir() if p.is_file() and not p.name.startswith("."))
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def pins(lean):
    text = Path(lean).read_text(encoding="utf-8")
    start = text.find("def cert54Pins")
    if start < 0:
        return {}
    end = text.find("]", start)
    return dict(PIN.findall(text[start:end]))


def table(data_dir):
    d = digests(data_dir)
    if not d:
        print("pin_cert54_data: no file under %s -- nothing to pin (not clean)" % data_dir)
        return 2
    print("def cert54Pins : List (String × String) := [")
    rows = ['  ("%s", "%s")' % (f, h) for f, h in sorted(d.items())]
    print(",\n".join(rows) + "]")
    return 0


def check(data_dir, lean):
    d, p = digests(data_dir), pins(lean)
    if not d or not p:
        print("pin_cert54_data: %d file(s) under %s, %d pin(s) in %s -- could not check (not clean)"
              % (len(d), data_dir, len(p), lean))
        return 2
    bad = 0
    for f in sorted(set(d) | set(p)):
        if f not in p:
            print("%s/%s: NO PIN in %s" % (data_dir, f, lean))
            bad += 1
        elif f not in d:
            print("%s/%s: pinned in %s but MISSING" % (data_dir, f, lean))
            bad += 1
        elif d[f] != p[f]:
            print("%s/%s: sha256 %s is not the pinned %s" % (data_dir, f, d[f], p[f]))
            bad += 1
    if bad:
        return 1
    print("pin_cert54_data OK: %d file(s) under %s match cert54Pins in %s" % (len(d), data_dir, lean))
    return 0


def self_test(root):
    with tempfile.TemporaryDirectory() as tmp:
        dst = Path(tmp) / "data"
        shutil.copytree(root / DATA_DIR, dst)
        lean = root / LEAN
        clean = check(dst, lean)
        # a flipped byte in one data file
        target = dst / "coef.txt"
        orig = target.read_bytes()
        target.write_bytes(orig[:-2] + bytes([orig[-2] ^ 1]) + orig[-1:])
        flipped = check(dst, lean)
        target.write_bytes(orig)
        # a file with no pin
        stray = dst / "stray.txt"
        stray.write_text("# not pinned\n", encoding="utf-8")
        unpinned = check(dst, lean)
        stray.unlink()
        # a pinned file missing
        moved = dst / "W.txt"
        w = moved.read_bytes()
        moved.unlink()
        missing = check(dst, lean)
        moved.write_bytes(w)
        again = check(dst, lean)
    results = [("clean copy", clean, 0), ("a flipped byte in coef.txt", flipped, 1),
               ("an unpinned stray.txt", unpinned, 1), ("W.txt missing", missing, 1),
               ("restored", again, 0)]
    ok = all(rc == want for _, rc, want in results)
    for what, rc, want in results:
        print("self-test: %s -> exit %d (must be %d)%s" % (what, rc, want, "" if rc == want else "  <-- WRONG"))
    print("self-test %s" % ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1


def main(argv):
    root = Path(__file__).resolve().parents[2]
    if argv[1:] == ["--self-test"]:
        return self_test(root)
    if argv[1:] == ["--check"]:
        return check(root / DATA_DIR, root / LEAN)
    if len(argv) == 1:
        return table(root / DATA_DIR)
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
