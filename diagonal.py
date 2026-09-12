# Copyright (C) 2026 Marcello Federico
# SPDX-License-Identifier: GPL-3.0-or-later
#
# This file is part of the fermat433 proof record
# <https://github.com/marchfederico/fermat433>.  It is free software: you may
# redistribute it and modify it under the terms of the GNU General Public
# License, either version 3 of the License or (at your option) any later
# version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
# the repository root, or <https://www.gnu.org/licenses/>.

"""(1) Local test with the primitivity conditions: gamma must be a unit at the primes above 2 and 3.
(2) Over K = Q(th), th^3 = 2: coordinates r = gamma(th), s + t*ze = gamma(ze*th) turn C_k into A r^4 + G(s,t) = 0,
so E_k := C_k / (r -> -r) is the genus-1 quartic W^2 = -A G(s,t) over K."""
import math
import sympy as sp
from descent_explore_forms import forms, norm  # reuse the forms without re-running the search

A_, B_, C_ = sp.symbols("a b c")

# ---------------- (1) local conditions with gamma a unit at 2 and 3
def local_unit_levels(F, p, M, unit_ok):
    f = sp.lambdify((A_, B_, C_), F, "math")
    level = [(a, b, c) for a in range(p) for b in range(p) for c in range(p) if unit_ok(a, b, c) and f(a, b, c) % p == 0]
    counts = [len(level)]
    for m in range(2, M + 1):
        q = p ** m
        nxt = [(a + da * p ** (m - 1), b + db * p ** (m - 1), c + dc * p ** (m - 1))
               for (a, b, c) in level for da in range(p) for db in range(p) for dc in range(p)
               if f(a + da * p ** (m - 1), b + db * p ** (m - 1), c + dc * p ** (m - 1)) % q == 0]
        level = nxt
        counts.append(len(level))
        if not level:
            break
    return counts

unit2 = lambda a, b, c: a % 2 == 1                     # N(gamma) = a^3 mod 2
unit3 = lambda a, b, c: (a + 2 * b + c) % 3 != 0         # N(gamma) = a + 2b + 4c = a + 2b + c mod 3
for k in (0, 1, 2):
    F = forms[k][0]
    print(f"k={k}: gamma unit at 2, solutions mod 2^m: {local_unit_levels(F, 2, 8, unit2)}")
    print(f"k={k}: gamma unit at 3, solutions mod 3^m: {local_unit_levels(F, 3, 6, unit3)}")

# ---------------- (2) diagonalization over K
th, ze, r, s, t = sp.symbols("th ze r s t")
def red(expr):
    expr = sp.expand(expr)
    P = sp.Poly(expr, th, ze)
    out = 0
    for (i, j), coef in P.terms():
        zj = {0: 1, 1: ze, 2: -1 - ze}[j % 3]
        out += coef * 2 ** (i // 3) * th ** (i % 3) * zj
    out = sp.expand(out)
    P = sp.Poly(out, th, ze)
    if any(j >= 2 or i >= 3 for (i, j) in P.monoms()):
        return red(out)
    return out

subs = {A_: (r + 2 * s - t) / 3, B_: (r - s + 2 * t) * th ** 2 / 6, C_: (r - s - t) * th / 6}
gp_lines = []
for k in (0, 1, 2):
    F = forms[k][0]
    G = sp.Poly(sp.expand(F.subs(subs)), r, s, t)
    coeffs = {}
    for mon, coef in G.terms():
        coeffs[mon] = red(coef)
    mixed = {m: c for m, c in coeffs.items() if m[0] not in (0, 4) and c != 0}
    mixed.update({m: c for m, c in coeffs.items() if m[0] == 4 and (m[1] or m[2]) and c != 0})
    assert not mixed, f"mixed terms remain for k={k}: {mixed}"
    A = coeffs.get((4, 0, 0), 0)
    Gst = sum(coeffs[m] * s ** m[1] * t ** m[2] for m in coeffs if m[0] == 0)
    Q = sp.expand(-A * Gst)
    Qc = sp.Poly(Q, s, t)
    def gpcoef(e):
        e = sp.expand(e)
        c0, c1, c2 = [sp.Rational(sp.Poly(e, th).coeff_monomial(th ** i)) for i in range(3)]
        return f"Mod({c0}+({c1})*w+({c2})*w^2, w^3-2)"
    quartic_x = " + ".join(f"{gpcoef(Qc.coeff_monomial(s ** (4 - i) * t ** i))}*x^{4 - i}" for i in range(5))
    print(f"\nk={k}: A = {A};  E_k: W^2 = -A*G(s,t) with G = {sp.factor(Gst)}")
    gp_lines.append(f"Q{k} = {quartic_x};")
    # known rational points of C_k mapped to E_k (t = 1 affine chart when t != 0)
    pts = {0: [(0, 1, 0), (1, 0, -1), (1, 0, 0)], 1: [(1, -2, 0), (1, -1, 2), (1, 0, 0), (1, 1, 0)], 2: [(0, 1, 1)]}[k]
    for (a, b, c) in pts:
        rv, sv, tv = a + b * th + c * th ** 2, a - c * th ** 2, b * th - c * th ** 2
        Wv = red(A * rv ** 2)
        chk = red(Wv ** 2 - Q.subs({s: sv, t: tv}))
        print(f"   point {(a, b, c)}: s={sv}, t={tv}, W={Wv}; on quartic: {chk == 0}")
        if tv != 0:
            gp_lines.append(f"P{k}_{a}_{b}_{c}".replace("-", "m") + f" = [{gpcoef(red(sv / tv * th**0) if False else 0)}];")
open("quartics.gp", "w").write("\n".join(gp_lines) + "\n")
print("\nwrote quartics.gp")
