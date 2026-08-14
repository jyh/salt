#!/usr/bin/env python3
"""The pi-package §3.1 structural gate, re-run after this sitting's edits.

No LaTeX toolchain on this machine (main.tex says so in its own header), so
this checks BALANCE, not compilability — stated plainly, as the package does.
Prints what it read, including the counts that did not change.
"""
import re, pathlib, sys

p = pathlib.Path("papers/flagship/main.tex")
lines = p.read_text(encoding="utf-8").splitlines()

# strip comments: a % is a comment unless preceded by a backslash
def strip(line):
    out, i = [], 0
    while i < len(line):
        c = line[i]
        if c == "\\" and i + 1 < len(line):
            out.append(line[i:i+2]); i += 2; continue
        if c == "%":
            break
        out.append(c); i += 1
    return "".join(out)

body = [strip(l) for l in lines]
text = "\n".join(body)

problems = []

# environments
stack = []
for n, l in enumerate(body, 1):
    for m in re.finditer(r"\\(begin|end)\{([^}]*)\}", l):
        kind, env = m.group(1), m.group(2)
        if kind == "begin":
            stack.append((env, n))
        else:
            if not stack:
                problems.append(f"line {n}: \\end{{{env}}} with empty stack")
            elif stack[-1][0] != env:
                problems.append(f"line {n}: \\end{{{env}}} closes \\begin{{{stack[-1][0]}}} (line {stack[-1][1]})")
                stack.pop()
            else:
                stack.pop()
if stack:
    problems.append(f"unclosed environments at EOF: {stack}")

# math delimiters
dollars = len(re.findall(r"(?<!\\)\$", text))
if dollars % 2:
    problems.append(f"odd number of unescaped $ ({dollars})")
opens = len(re.findall(r"\\\[", text)); closes = len(re.findall(r"\\\]", text))
if opens != closes:
    problems.append(rf"\[ {opens} vs \] {closes}")

# braces
depth = 0
for n, l in enumerate(body, 1):
    for m in re.finditer(r"(?<!\\)[{}]", l):
        depth += 1 if m.group(0) == "{" else -1
        if depth < 0:
            problems.append(f"line {n}: brace depth went negative"); depth = 0
if depth != 0:
    problems.append(f"brace depth {depth} at EOF")

# refs and cites
labels = set(re.findall(r"\\label\{([^}]*)\}", text))
refs   = set(re.findall(r"\\(?:page)?ref\{([^}]*)\}", text))
bibs   = set(re.findall(r"\\bibitem\{([^}]*)\}", text))
cites  = set()
for blob in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]*)\}", text):
    cites.update(k.strip() for k in blob.split(","))

dangling_refs  = sorted(refs - labels)
dangling_cites = sorted(cites - bibs)
if dangling_refs:  problems.append(f"DANGLING \\ref: {dangling_refs}")
if dangling_cites: problems.append(f"DANGLING \\cite: {dangling_cites}")

print(f"lines                 {len(lines)}")
print(f"environments          balanced, empty at EOF" if not stack else "environments UNBALANCED")
print(f"unescaped $           {dollars} = {dollars//2} pairs, even" if dollars % 2 == 0 else f"unescaped $ {dollars} ODD")
print(rf"\[ / \]               {opens} / {closes}")
print(f"braces                depth returns to {depth}")
print(f"\\ref -> \\label        {len(refs)} refs, {len(labels)} labels, dangling {len(dangling_refs)}")
print(f"\\cite -> \\bibitem     {len(cites)} cited keys, {len(bibs)} bibitems, dangling {len(dangling_cites)}")
print(f"uncited bibitems      {sorted(bibs - cites)}")
print()
print("PROBLEMS: " + ("none" if not problems else ""))
for pr in problems:
    print("  ⛔ " + pr)
sys.exit(1 if problems else 0)
