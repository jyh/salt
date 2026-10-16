#!/usr/bin/env python3
"""Emitter for the k = 54 certificate's data (`SaltC1/Cert54/data/`).

Maynard, "Dense clusters of primes in subsets" / Polymath 8b (arXiv:1407.4897v4)
Thm 3.9(vii): M_54 > 4 via the d = 23 vector in the basis
`(1 - P_1)^a * prod_{m=1}^{13} P_{2m}^{c_m}`, `a + sum 2m c_m <= 23` (1,236
functions). The vector (exact rationals) is an INPUT: the file
`vector-k54-eps0-d23.txt` in the data directory, one row `a c_1 .. c_13 : p/q`
per basis function. Nothing here bears on twin primes.

What it computes, every quantity EXACTLY (Python integers):
  coef   the vector rescaled to ONE common-scale integer vector: the smallest
         non-zero |coefficient| keeps 20 digits, i.e. coef = round(q * 10^19 /
         min|q|), round = nearest with ties to even (Python's `round` on a
         Fraction).
  p54    [x^C] GM^54 for weight(C) <= 46 by the Miller power recurrence
           wt(C) p_C = sum_{0 != A <= C} (54 wt(A) - wt(C-A)) g_A p_{C-A}, p_0 = 1,
         exact division asserted at every key; p53 the same at k = 53 over
         weight <= 48. Both are cross-checked on EVERY key against
         `c1series.series_pow` (binary exponentiation of the series): two
         methods, one object.
  WI, WJ the closed forms WI(enc(A,C)) = A! prod c_m! p54(C) 100!/(54+A+wt C)!
         and WJ(enc(E,G)) = E! prod g_m! p53(G) 101!/(53+E+wt G)! (not written:
         the Lean side derives them from fact, p54 and p53, and the kernel
         certifies them).
  W      the 24!-scaled collected marginal: the per-key sum of the terms
           coef_i a! e! (24!/(a+e+1)!) prod_m C(c_m, j_m)  at key enc(a+e+1, c-j),
         e = wt(j), over the basis i and 0 <= j <= c_i.
  Iint, Jint   sum_{i,j} c_i c_j WI(k_i + k_j) and sum_{x,y} W_x W_y WJ(k_x + k_y),
         each computed twice (full double sum; the symmetric half by rows).
  the certificate   0 < Iint and 40015 Iint (24!)^2 101! < 10000 * 54 * Jint * 100!.
Keys are enc(A, C) = A + sum_m c_m 64^m (every component < 64 for sums of two keys).

Files written into DATA_DIR (each with a header naming this generator, its
command line and the vector's sha256): coef.txt (basis order), W.txt, p54.txt,
p53.txt (key order), wterms.txt (the marginal's terms `i a c_1..c_13 j_1..j_13`
sorted by (key, i, enc j), in sections `## wsh<n>` of <= 1,000 terms cut at key
boundaries). It REFUSES (exit 1) if the ratio is below 4.0015 + 1/10000.

usage:  python3 scripts/c1/emit_cert54.py DATA_DIR [--write-lean SaltC1/Cert54 [--manifest PATH]]
        python3 scripts/c1/emit_cert54.py --self-test
--self-test runs the same pipeline at k = 105, M = 1, d = 11 on the coefficient
list `F` of the landed `Salt/MaynardK/Cert105.lean` and must print the landed
`M105_gt_four` value 4.0020697619...
"""
import hashlib
import itertools
import os
import re
import sys
from fractions import Fraction as Fr
from math import comb, factorial
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import c1series  # noqa: E402

REPO = Path(__file__).resolve().parents[2]
VECTOR = "vector-k54-eps0-d23.txt"
DIG = 20
SHARD = 1000


def weight(c):
    return c1series.weight(c)


def enc(A, C):
    v = A
    for m, cm in enumerate(C):
        v += cm * 64 ** (m + 1)
    return v


def box(C):
    return itertools.product(*[range(cm + 1) for cm in C])


def g_of(C):
    v = factorial(weight(C))
    for cm in C:
        v //= factorial(cm)
    return v


def power_by_rec(k, M, wmax):
    """[x^C] GM^k for weight(C) <= wmax by the Miller recurrence, exact division asserted."""
    keys = sorted(c1series.keys_upto(M, wmax), key=lambda C: (weight(C), C))
    g = {C: g_of(C) for C in keys}
    p = {}
    for C in keys:
        if weight(C) == 0:
            p[C] = 1
            continue
        s = 0
        for A in box(C):
            if weight(A) == 0:
                continue
            B = tuple(c - a for c, a in zip(C, A))
            s += (k * weight(A) - weight(B)) * g[A] * p[B]
        assert s % weight(C) == 0, ("inexact division", k, C)
        p[C] = s // weight(C)
    return p


def rescale(q):
    mn = min(abs(x) for x in q if x != 0)
    scale = Fr(10 ** (DIG - 1)) / mn
    return [int(round(x * scale)) for x in q]


def pipeline(k, M, d, coef, check_series=True, log=print):
    """Every table and both forms for the integer vector `coef` in the basis order."""
    B = [(a, c) for c in c1series.keys_upto(M, d) for a in range(d - weight(c) + 1)]
    assert len(B) == len(coef)
    wI, wJ = 2 * d, 2 * d + 2
    pk = power_by_rec(k, M, wI)
    pk1 = power_by_rec(k - 1, M, wJ)
    if check_series:
        sk = c1series.series_pow(M, k, wI)
        sk1 = c1series.series_pow(M, k - 1, wJ)
        assert set(sk) == set(pk) and all(sk[C] == pk[C] for C in pk), "recurrence != series_pow at k"
        assert set(sk1) == set(pk1) and all(sk1[C] == pk1[C] for C in pk1), "recurrence != series_pow at k-1"
        log("cross-check: the recurrence equals series_pow on all %d keys (k = %d, weight <= %d) and all %d keys "
            "(k = %d, weight <= %d)" % (len(pk), k, wI, len(pk1), k - 1, wJ))
    FI, FJ, Fw = factorial(k + wI), factorial(k - 1 + wJ), factorial(d + 1)
    WI = {}
    for C, t in pk.items():
        for A in range(wI - weight(C) + 1):
            num = factorial(A)
            for cm in C:
                num *= factorial(cm)
            num *= t * FI
            den = factorial(k + A + weight(C))
            assert num % den == 0
            WI[enc(A, C)] = num // den
    WJ = {}
    for G, t in pk1.items():
        for E in range(wJ - weight(G) + 1):
            num = factorial(E)
            for gm in G:
                num *= factorial(gm)
            num *= t * FJ
            den = factorial(k - 1 + E + weight(G))
            assert num % den == 0
            WJ[enc(E, G)] = num // den
    terms = []
    W = {}
    for i, ((a, c), ci) in enumerate(zip(B, coef)):
        for j in box(c):
            e = weight(j)
            v = ci * factorial(a) * factorial(e) * (Fw // factorial(a + e + 1))
            for cm, jm in zip(c, j):
                v *= comb(cm, jm)
            key = enc(a + e + 1, tuple(cm - jm for cm, jm in zip(c, j)))
            W[key] = W.get(key, 0) + v
            terms.append((key, i, enc(0, j), a, c, j))
    terms.sort(key=lambda t: (t[0], t[1], t[2]))
    Wl = sorted(W.items())
    keysB = [enc(a, c) for (a, c) in B]
    # the forms, twice: the full double sum, and the symmetric half by rows
    Iint = sum(ci * cj * WI[keysB[i] + keysB[j]] for i, ci in enumerate(coef) for j, cj in enumerate(coef))
    Jint = sum(wi * wj * WJ[ki + kj] for ki, wi in Wl for kj, wj in Wl)
    rowI = [coef[i] * coef[i] * WI[2 * keysB[i]]
            + 2 * sum(coef[i] * coef[j] * WI[keysB[i] + keysB[j]] for j in range(i + 1, len(coef)))
            for i in range(len(coef))]
    rowJ = [Wl[x][1] * Wl[x][1] * WJ[2 * Wl[x][0]]
            + 2 * sum(Wl[x][1] * Wl[y][1] * WJ[Wl[x][0] + Wl[y][0]] for y in range(x + 1, len(Wl)))
            for x in range(len(Wl))]
    assert sum(rowI) == Iint and sum(rowJ) == Jint, "half-sum != full double sum"
    return dict(B=B, pk=pk, pk1=pk1, WI=WI, WJ=WJ, W=Wl, terms=terms, keysB=keysB, Iint=Iint, Jint=Jint,
                rowI=rowI, rowJ=rowJ, FI=FI, FJ=FJ, Fw=Fw)


def ratio_of(k, r):
    return Fr(k * r["Jint"] * r["FI"], r["Iint"] * r["Fw"] ** 2 * r["FJ"])


def ineq(k, r, num):
    """0 < Iint and num * Iint * Fw^2 * FJ < 10000 * k * Jint * FI"""
    return r["Iint"] > 0 and num * r["Iint"] * r["Fw"] ** 2 * r["FJ"] < 10000 * k * r["Jint"] * r["FI"]


def fmt_ratio(x, digits):
    """x (a positive Fraction) truncated to `digits` decimals, exactly."""
    n = x.numerator * 10 ** digits // x.denominator
    s = str(n)
    return s[:-digits] + "." + s[-digits:]


def read_vector(path):
    rows = []
    for line in open(path, encoding="utf-8"):
        if line.startswith("#") or not line.strip():
            continue
        lhs, rhs = line.split(":")
        ws = [int(w) for w in lhs.split()]
        rows.append(((ws[0], tuple(ws[1:])), Fr(rhs.strip())))
    return rows


def coeffs_lean(B, coef, vsha):
    """`SaltC1/Cert54/Coeffs.lean` (the list itself is read from `coef.txt`, never source text)."""
    return COEFFS % vsha


COEFFS = """/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.Cert54.Checks

/-!
# C1 — the `k = 54` certificate's coefficient list

`cs54L` is the vector of the certificate at the common integer scale, one basis function
`(1 − P₁)^a · Π_m P_{2m}^{c_m}` per entry as `(a, [c₁, …, c₁₃], coefficient)`, in the basis order
(`c` over `keysW 13 23`, then `a = 0 … 23 − wt c`). It is read from `data/coef.txt` (one
`enc(a, C) coefficient` line per entry; the vector's sha256 in its header is
`%s`)
by `cert54_coeffs`, which decodes each key into `(a, C)` and adds the list with `addDecl` (a source
literal of this size exhausts the elaborator). `cs54` is the same list in the type of the Lean side,
`List ((ℕ × (Fin 13 → ℕ)) × ℤ)`; `coef_keys_ok` certifies, by `decide +kernel`, that
`coefBT.getB i` is the `i`-th entry's key and coefficient. Nothing here bears on twin primes.
-/

namespace SaltC1.Cert54

open Lean Elab Command Meta in
/-- Read `coef.txt` and add `cs54L : List (Nat × List Nat × Int)`. -/
elab "cert54_coeffs " dir:str : command => do
  let txt ← IO.FS.readFile (dir.getString ++ "/coef.txt")
  let secs ← match parseSections txt with
    | .ok s => pure s
    | .error e => throwError "coef.txt: {e}"
  let some (_, a) := secs.find? (·.1 == "coef") | throwError "coef.txt: section coef missing"
  unless a.size == 1236 && a.all (·.length == 2) do throwError "coef.txt: not 1236 pairs"
  let eTy := prodTy natTy (prodTy natListTy (mkConst ``Int))
  let es := a.toList.map fun l =>
    let key := l[0]!.toNat
    let c := (List.range 13).map fun m => (key / 64 ^ (m + 1)) %% 64
    pairE natTy (prodTy natListTy (mkConst ``Int)) (mkRawNatLit (key %% 64))
      (pairE natListTy (mkConst ``Int) (listOfE natTy (c.map mkRawNatLit)) (intExpr l[1]!))
  addData `SaltC1.Cert54.cs54L (mkApp (mkConst ``List [Level.zero]) eTy) (listOfE eTy es)

cert54_coeffs "SaltC1/Cert54/data"

/-- The coefficient list in the type of the Lean side. -/
noncomputable def cs54 : List ((ℕ × (Fin 13 → ℕ)) × ℤ) :=
  cs54L.map fun e => ((e.1, fun m => e.2.1.getD m 0), e.2.2)

/-- `l` has `nB` entries and its `i`-th entry's key and coefficient are `coefBT.getB i`. -/
noncomputable def checkCoefKeys (l : List (Nat × List Nat × Int)) : Bool :=
  Nat.beq l.length nB && ((List.range nB).zip l).all fun (i, e) =>
    let kv := coefBT.getB i
    Nat.beq kv.1 (encKey e.1 e.2.1) && kv.2 == e.2.2

theorem coef_keys_ok : checkCoefKeys cs54L = true := by decide +kernel

end SaltC1.Cert54
"""


def self_test():
    src = (REPO / "Salt" / "MaynardK" / "Cert105.lean").read_text(encoding="utf-8")
    body = src[src.index("def F : List"):src.index("def Iform")]
    F = {(int(b), int(c)): int(v) for b, c, v in re.findall(r"\(\((\d+),\s*(\d+)\),\s*(-?\d+)\)", body)}
    k, M, d = 105, 1, 11
    B = [(a, c) for c in c1series.keys_upto(M, d) for a in range(d - weight(c) + 1)]
    assert len(F) == len(B) == 42, (len(F), len(B))
    q = [Fr(F[(a, c[0])]) for (a, c) in B]
    coef = rescale(q)
    r = pipeline(k, M, d, coef, log=lambda s: None)
    x = ratio_of(k, r)
    raw = pipeline(k, M, d, [F[(a, c[0])] for (a, c) in B], log=lambda s: None)
    xr = ratio_of(k, raw)
    s = fmt_ratio(x, 10)
    print("self-test k=105 M=1 d=11 (Cert105.F, %d coefficients): ratio=%s (rescaled) ratio=%s (as landed)"
          % (len(B), s, fmt_ratio(xr, 10)))
    if not (s.startswith("4.0020697619") and fmt_ratio(xr, 10).startswith("4.0020697619")):
        print("SELF-TEST FAILED: expected 4.0020697619...", file=sys.stderr)
        return 1
    print("self-test PASSED: the pipeline reproduces the landed M105_gt_four value 4.0020697619...")
    return 0


def main(argv):
    if argv[1:] == ["--self-test"]:
        return self_test()
    args = argv[1:]
    if not args or args[0].startswith("-"):
        print(__doc__, file=sys.stderr)
        return 2
    out = Path(args[0])
    try:
        rel = os.path.relpath(out.resolve(), REPO)
        assert not rel.startswith("..")
    except (ValueError, AssertionError):
        rel = "<a directory outside the repository>"
    vpath = out / VECTOR
    vbytes = vpath.read_bytes()
    vsha = hashlib.sha256(vbytes).hexdigest()
    rows = read_vector(vpath)
    k, M, d = 54, 13, 23
    B = [(a, c) for c in c1series.keys_upto(M, d) for a in range(d - weight(c) + 1)]
    assert [b for b, _ in rows] == B, "the vector's rows are not the basis in its order"
    coef = rescale([x for _, x in rows])
    nz = [len(str(abs(c))) for c in coef if c]
    print("coef: %d entries, digits min %d max %d (the smallest non-zero keeps %d)" % (len(coef), min(nz), max(nz), DIG))
    r = pipeline(k, M, d, coef)
    x = ratio_of(k, r)
    print("tables: p54 %d keys · p53 %d keys · WI %d · WJ %d · marginal keys %d · marginal terms %d"
          % (len(r["pk"]), len(r["pk1"]), len(r["WI"]), len(r["WJ"]), len(r["W"]), len(r["terms"])))
    print("ratio=%s ineq(40015)=%s 40023:%s 40024:%s"
          % (fmt_ratio(x, 9), ineq(k, r, 40015), ineq(k, r, 40023), ineq(k, r, 40024)))
    if not (r["Iint"] > 0 and x >= Fr(40016, 10000)):
        print("REFUSED: the ratio %s is below 4.0015 + 1/10000" % fmt_ratio(x, 9), file=sys.stderr)
        return 1
    cmd = "python3 scripts/c1/emit_cert54.py %s" % rel
    head = ("# generator: scripts/c1/emit_cert54.py (SaltC1/Cert54 data, k = 54, M = 13, d = 23)\n"
            "# command: %s\n"
            "# vector: %s sha256 %s\n"
            "# coef = round(q * 10^19 / min|q|), round = nearest, ties to even\n") % (cmd, VECTOR, vsha)
    files = {}
    files["coef.txt"] = "## coef %d\n" % len(coef) + "".join(
        "%d %d\n" % (kb, c) for kb, c in zip(r["keysB"], coef))
    files["W.txt"] = "## W %d\n" % len(r["W"]) + "".join("%d %d\n" % kv for kv in r["W"])
    files["p54.txt"] = "## p54 %d\n" % len(r["pk"]) + "".join(
        "%d %d\n" % (enc(0, C), v) for C, v in sorted(r["pk"].items(), key=lambda kv: enc(0, kv[0])))
    files["p53.txt"] = "## p53 %d\n" % len(r["pk1"]) + "".join(
        "%d %d\n" % (enc(0, C), v) for C, v in sorted(r["pk1"].items(), key=lambda kv: enc(0, kv[0])))
    # shards of <= SHARD terms cut at key boundaries
    terms = r["terms"]
    groups = []
    for t in terms:
        if groups and groups[-1][0][0] == t[0]:
            groups[-1].append(t)
        else:
            groups.append([t])
    shards = [[]]
    for gr in groups:
        if shards[-1] and len(shards[-1]) + len(gr) > SHARD:
            shards.append([])
        shards[-1] += gr
    assert sum(len(s) for s in shards) == len(terms)

    def tline(t):
        _, i, _, a, c, j = t
        return "%d %d %s %s\n" % (i, a, " ".join(map(str, c)), " ".join(map(str, j)))
    files["wterms.txt"] = "".join("## wsh%d %d\n" % (n, len(s)) + "".join(tline(t) for t in s)
                                  for n, s in enumerate(shards))
    for name, body in files.items():
        (out / name).write_text(head + body, encoding="utf-8")
    print("sha256 %s  %s" % (vsha, VECTOR))
    for name in files:
        print("sha256 %s  %s" % (hashlib.sha256((out / name).read_bytes()).hexdigest(), name))
    print("wterms: %d shards, sizes %s" % (len(shards), [len(s) for s in shards]))
    # the chain of the marginal check, 4 shards per theorem: (pos, lastKey) before, after, and the count
    pos, pk, chain = 0, 0, []
    for g0 in range(0, len(shards), 4):
        sub = shards[g0:g0 + 4]
        runs = sum(len({t[0] for t in s_}) for s_ in sub)
        last = sub[-1][-1][0]
        chain.append((pos, pk, pos + runs, last, sum(len(s_) for s_ in sub)))
        pos, pk = pos + runs, last
    assert pos == len(r["W"])
    for n, (p0, k0, p1, k1, cnt) in enumerate(chain):
        print("wchain %d: from (pos %d, key %d) to (pos %d, key %d), %d terms" % (n, p0, k0, p1, k1, cnt))
    print("Iint = %d" % r["Iint"])
    print("Jint = %d" % r["Jint"])
    if "--write-lean" in args:
        import lean_cert54
        ldir = Path(args[args.index("--write-lean") + 1])
        tables, man_t = lean_cert54.tables_lean(chain)
        forms, man_f = lean_cert54.forms_lean(r, len(coef))
        coeffs = coeffs_lean(B, coef, vsha)
        audit, names = lean_cert54.audit_lean([tables, forms, coeffs])
        outs = {"Tables.lean": tables, "Forms.lean": forms, "Coeffs.lean": coeffs, "Audit.lean": audit,
                "All.lean": lean_cert54.ALL}
        for name, body in outs.items():
            (ldir / name).write_text(body, encoding="utf-8")
            print("sha256 %s  %s" % (hashlib.sha256((ldir / name).read_bytes()).hexdigest(), name))
        print("theorems: Tables %d · Forms %d (decide +kernel shards); %d theorems audited"
              % (len(man_t), len(man_f), len(names)))
        if "--manifest" in args:
            import json
            mpath = Path(args[args.index("--manifest") + 1])
            mpath.write_text(json.dumps({"Tables": man_t, "Forms": man_f}, indent=0), encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
