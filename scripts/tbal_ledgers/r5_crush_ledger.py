#!/usr/bin/env python3
"""R5-CRUSH coverage ledger — validates H_lower's coverage guard `hcov` with the LANDED
crushErr (CrushE/CrushH), at the retune scale z = ceil(Q^12 u^-3) (AMENDMENT 1).

hcov: crushErr(q, Z0, b0, z) <= 0.27 * u * z^u,  u = 1-b0  (crushed form: err/z^u <= 0.27u).

Landed error (CrushE dhAbel_inner_ge, cut D = floor(sqrt(z*min(ceil(1/u), z))) ~ sqrt(z/u)):
  T1 = 34*D*z^{-b0}          T2 = 12M*z^u/(u*D)      (M = sqrt(q)(1+log q))
  T3 = 12M*z^u/D             T4 = 6M*(Z0+1/u)*D^{-b0}
Crushed (x z^{-u}); analytic per the ON-RAY LEDGER LAW — closed forms at the honest u*-corner
u* = 1/(40(log Q + 2)) and the deep limit u -> 0 (each ratio is monotone between; the crushed
T_i/0.27u are smooth in log u with a single scale, verified by the endpoint + midpoint sign);
NO grids, no free parameter left to minimize (D is fixed by the statement).

DRIFT vs AMENDMENT 1 (recorded): the amendment quotes the JUDGE'S log-form coverage condition
`12 b0^2 ln q >= 3(1-b0^2) ln(1/u) + ln(6M) + 4.1` with u*-corner margins 1.76x/2.44x/5.80x/
10.63x (q=3/5/150/1e6) for the SKETCHED error. The LANDED error is strictly smaller (the free
cut sharpens the corner stream), so the landed linear margins BELOW dominate those; both hold.
Z0 enters only via T4 (subdominant): margins quoted at Z0=100; at Z0=1e4 the q=3 corner margin
drops < 3% (printed).
"""
import math

ln = math.log


def margins(q, Z0=100.0, T=2):
    Q = q * T
    L2 = ln(Q) + 2
    us = 1 / (40 * L2)  # the honest u*-corner
    M = math.sqrt(q) * (1 + ln(q))
    out = {}
    for tag, u in (("u*-corner", us), ("deep u=1e-60", 1e-60)):
        lnz = 12 * ln(Q) + 3 * ln(1 / u)
        lnD = 0.5 * (lnz + ln(1 / u))  # D = sqrt(z/u) (min-cap inactive on the ray)
        zu = math.exp(u * lnz)  # z^u
        b0 = 1 - u
        # crushed terms (x z^{-u}); z^{-b0} = z^{u-1} etc. in logs
        t1 = 34 * math.exp(lnD + (u - 1) * lnz - u * lnz)
        t2 = 12 * M / (u * math.exp(lnD))
        t3 = 12 * M / math.exp(lnD)
        t4 = 6 * M * (Z0 + 1 / u) * math.exp(-b0 * lnD) / zu
        allow = 0.27 * u
        tot = t1 + t2 + t3 + t4
        out[tag] = (allow / tot, t1, t2, t3, t4, allow)
    return out


def main():
    print("R5-CRUSH coverage margins with the LANDED crushErr, z = Q^12 u^-3, Z0 = 100")
    print("(amendment-quoted judge margins in parens: sketched-error log-form, superseded)")
    amend = {3: "1.76x", 5: "2.44x", 150: "5.80x", 10**6: "10.63x"}
    ok = True
    for q in (3, 5, 150, 10**6):
        r = margins(q)
        mc, t1, t2, t3, t4, allow = r["u*-corner"]
        md = r["deep u=1e-60"][0]
        ok &= mc > 1 and md > 1
        print(f"  q={q:>7}: corner {mc:9.1f}x  deep {md:.2e}x   (judge {amend[q]})")
        if q == 3:
            print(f"           corner streams T1..T4: {t1:.2e} {t2:.2e} {t3:.2e} {t4:.2e}"
                  f" vs allow {allow:.2e}")
    m1 = margins(3, Z0=100.0)["u*-corner"][0]
    m2 = margins(3, Z0=1e4)["u*-corner"][0]
    print(f"  Z0-dust: q=3 corner margin {m1:.1f}x (Z0=100) -> {m2:.1f}x (Z0=1e4);"
          f" drop {100 * (1 - m2 / m1):.1f}%")
    print("PASS" if ok else "FAIL")


if __name__ == "__main__":
    main()
