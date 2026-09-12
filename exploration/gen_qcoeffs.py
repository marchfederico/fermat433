# Copyright (C) 2026 Marcello Federico
# SPDX-License-Identifier: GPL-3.0-or-later
#
# This file is part of the fermat433 proof record
# <https://github.com/marchfederico/fermat433>.  It is free software: you may
# redistribute it and modify it under the terms of the GNU General Public
# License, either version 3 of the License or (at your option) any later
# version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
# the repository root, or <https://www.gnu.org/licenses/>.

import sympy as sp
from descent_explore_forms import forms
A_, B_, C_ = sp.symbols("a b c")
aa, bb, cc = sp.symbols("aa bb cc")
th, ze, r, s, t = sp.symbols("th ze r s t")

def red(expr):
    expr = sp.expand(expr)
    while True:
        P = sp.Poly(expr, th, ze)
        if all(i < 3 and j < 2 for (i, j) in P.monoms()):
            return expr
        out = 0
        for (i, j), coef in P.terms():
            zj = {0: 1, 1: ze, 2: -1 - ze}[j % 3]
            out += coef * 2 ** (i // 3) * th ** (i % 3) * zj
        expr = sp.expand(out)

def wpoly(e):
    e = red(e)
    assert not e.has(ze), e
    P = sp.Poly(e, th)
    cs = [sp.Rational(P.coeff_monomial(th ** i)) for i in range(3)]
    return f"({cs[0]}) + ({cs[1]})*w + ({cs[2]})*w^2"

subs = {A_: (r + 2 * s - t) / 3, B_: (r - s + 2 * t) * th ** 2 / 6, C_: (r - s - t) * th / 6}
lines = []
for k in (0, 1):
    F = forms[k][0]
    lines.append(f"F{k} = " + str(sp.expand(F.subs({A_: aa, B_: bb, C_: cc}))).replace("**", "^") + ";")
    G = sp.Poly(sp.expand(F.subs(subs)), r, s, t)
    co = {m: red(c) for m, c in G.terms()}
    A = co[(4, 0, 0)]
    for m, c in co.items():
        assert m[0] in (0, 4) and (m[0] == 0 or m == (4, 0, 0)) or c == 0
    QC = [red(-A * co.get((0, 4 - i, i), 0)) for i in range(5)]
    assert red(QC[0] - A ** 2) == 0, "constant term of Q(1,tau) must be A^2"
    lines.append(f"AK{k} = {wpoly(A)};")
    lines.append(f"QC{k} = [" + ", ".join(wpoly(q) for q in QC) + "];")
    # check known points lie on W^2 = Q(s,t)
    pts = {0: [(0, 1, 0), (1, 0, -1), (1, 0, 0)], 1: [(1, -2, 0), (1, -1, 2), (1, 0, 0), (1, 1, 0)]}[k]
    for (a, b, c) in pts:
        rv, sv, tv = a + b * th + c * th ** 2, a - c * th ** 2, b * th - c * th ** 2
        lhs = red((A * rv ** 2) ** 2)
        rhs = red(sum(QC[i] * sv ** (4 - i) * tv ** i for i in range(5)))
        assert red(lhs - rhs) == 0, (k, (a, b, c))
    print(f"k={k}: A = {A}; QC = {QC}; known points verified on W^2 = Q(s,t)")
lines.append("KP0 = [[0,1,0],[1,0,-1],[1,0,0]];")
lines.append("KP1 = [[1,-2,0],[1,-1,2],[1,0,0],[1,1,0]];")
open("qcoeffs.gp", "w").write("\n".join(lines) + "\n")
print("wrote qcoeffs.gp")
