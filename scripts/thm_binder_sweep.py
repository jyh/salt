#!/usr/bin/env python3
"""
M1(d) CLASS SWEEP — every pinned theorem in the paper against its Lean declaration's
hypothesis binders.

WHY: main.tex:502 rendered FOUR Lean binders as the undefined phrase "the engine's
regime" while the prose seventeen lines below certified the hypotheses were explicit.
That instance was found by PREDICTION, not by sweep. One repaired instance reads as
cleanliness to anyone who does not know how it was found — so this measures the CLASS.

WHAT IT DOES *NOT* DO, stated up front so a green is never read as clean: it cannot
decide whether a LaTeX sentence STATES a hypothesis. It prints BOTH SIDES and flags
the shape that hid the known defect. A human reads the flagged rows.
  (feedback-instrument-disclosure: instruments print what they READ, not only verdicts.)

Usage:  python3 scripts/thm_binder_sweep.py [main.tex] [lean-root]
"""
import re, sys, os, glob

TEX  = sys.argv[1] if len(sys.argv) > 1 else "papers/flagship/main.tex"
ROOT = sys.argv[2] if len(sys.argv) > 2 else "Salt"

ENVS = ("theorem", "proposition", "lemma", "corollary")

def tex_environments(text):
    """Yield (env, body) for each theorem-like environment."""
    for env in ENVS:
        for m in re.finditer(r"\\begin\{%s\}(.*?)\\end\{%s\}" % (env, env), text, re.S):
            yield env, m.group(1), text[:m.start()].count("\n") + 1

def lean_signature(name):
    """Return the declaration's binder text: everything between the name and the
    top-level ':' that opens the conclusion. None if the declaration is not found."""
    short = name.split(".")[-1]
    for path in glob.glob(os.path.join(ROOT, "**", "*.lean"), recursive=True):
        try:
            src = open(path, encoding="utf-8").read()
        except (OSError, UnicodeDecodeError):
            continue
        m = re.search(r"^(theorem|lemma)\s+%s\b" % re.escape(short), src, re.M)
        if not m:
            continue
        tail = src[m.end():]
        depth, out = 0, []
        for ch in tail:
            if ch in "([{⦃":
                depth += 1
            elif ch in ")]}⦄":
                depth -= 1
            elif ch == ":" and depth == 0:
                break
            out.append(ch)
        return path, m.start(), "".join(out).strip()
    return None

# a binder is a hypothesis if its TYPE looks like a Prop, not data.
PROP = re.compile(r"[≤<≥>=∈∣≠]|\bDivides\b|\bPrime\b")

def binders(sig):
    """Split a signature into top-level binder groups; classify each."""
    groups, depth, cur = [], 0, ""
    for ch in sig:
        if ch in "([{⦃":
            if depth == 0:
                cur = ""
            depth += 1
            if depth == 1:
                continue
        elif ch in ")]}⦄":
            depth -= 1
            if depth == 0:
                groups.append(cur)
                continue
        if depth >= 1:
            cur += ch
    hyps = [g for g in groups if PROP.search(g)]
    return groups, hyps

def main():
    text = open(TEX, encoding="utf-8").read()
    rows, flagged = 0, 0
    for env, body, line in tex_environments(text):
        pin = re.search(r"\\leanname\{([^}]*)\}", body)
        if not pin:
            print("── %-11s tex:%-5d  ⚠️  NO \\leanname PIN — outside this sweep's reach"
                  % (env, line))
            continue
        name = pin.group(1).replace("\\_", "_").strip()
        found = lean_signature(name)
        rows += 1
        if not found:
            print("── %-11s tex:%-5d  %s\n     ⛔ LEAN DECLARATION NOT FOUND — pin may be rotted"
                  % (env, line, name))
            flagged += 1
            continue
        path, _, sig = found
        groups, hyps = binders(sig)
        # the statement text, minus the pin and the display maths
        stmt = re.sub(r"\\leanname\{[^}]*\}", "", body)
        stmt = re.sub(r"\\\[.*?\\\]", " ⟨display⟩ ", stmt, flags=re.S)
        stmt = " ".join(stmt.split())
        print("── %-11s tex:%-5d  %s" % (env, line, name))
        print("     lean   %s" % path)
        print("     binders %d total, %d PROP-shaped (hypotheses):" % (len(groups), len(hyps)))
        for h in hyps:
            print("        ⊢ %s" % " ".join(h.split())[:96])
        print("     latex  %s" % stmt[:220])
        if hyps:
            flagged += 1
            print("     ⇒ READ THIS ROW: %d hypothesis binder(s). Does the LaTeX state each?"
                  % len(hyps))
        print()
    print("=" * 78)
    print("pinned theorem-like environments swept: %d" % rows)
    print("rows carrying PROP-shaped binders (need a human read): %d" % flagged)
    print("⚠️  This tool CANNOT certify a row clean. It flags shape; a reader decides.")

main()
