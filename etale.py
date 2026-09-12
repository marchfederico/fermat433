# Copyright (C) 2026 Marcello Federico
# SPDX-License-Identifier: GPL-3.0-or-later
#
# This file is part of the fermat433 proof record
# <https://github.com/marchfederico/fermat433>.  It is free software: you may
# redistribute it and modify it under the terms of the GNU General Public
# License, either version 3 of the License or (at your option) any later
# version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
# the repository root, or <https://www.gnu.org/licenses/>.

"""Etale double covers of C_k: delta = gamma^2 lies on the conic [th^2](u_k delta^2) = 0; parametrize it through the known
point delta = (1,0,0); then gamma^2 = mu * delta(s,t) forces mu * N(delta(s,t)) to be a square, i.e. a rational point
on the genus-2 curve H_lambda : w^2 = lambda * f6(s,t), lambda = squarefree part of mu."""
import math
import sympy as sp
from descent_explore_forms import mul, power, norm

d0, d1, d2, s, t = sp.symbols("d0 d1 d2 s t")
eps = (-1, 1, 0)
for k in (0, 1):
    uk = tuple(-x for x in power(eps, k))
    Qc = sp.expand(mul(uk, mul((d0, d1, d2), (d0, d1, d2)))[2])
    P = sp.Poly(Qc, d0, d1, d2)
    assert P.coeff_monomial(d0**2) == 0, "(1,0,0) must lie on the conic"
    L = sp.expand(sp.diff(Qc, d0))                 # coefficient of d0 (linear in d1, d2)
    Qp = sp.expand(Qc - d0*L)
    assert sp.expand(sp.diff(Qp, d0)) == 0
    param = [-Qp.subs({d1: s, d2: t}), s*L.subs({d1: s, d2: t}), t*L.subs({d1: s, d2: t})]
    param = [sp.expand(e) for e in param]
    assert sp.expand(Qc.subs({d0: param[0], d1: param[1], d2: param[2]})) == 0
    f6 = sp.expand(norm(tuple(param)))
    cont, prim = sp.Poly(f6, s, t).terms_gcd() if False else (None, None)
    print(f"k={k}: conic {Qc} = 0")
    print(f"   delta(s,t) = {param}")
    print(f"   f6 = N(delta) = {sp.factor(f6)}")
    pts = {0: [(0, 1, 0), (1, 0, -1), (1, 0, 0)], 1: [(1, -2, 0), (1, -1, 2), (1, 0, 0), (1, 1, 0)]}[k]
    for g in pts:
        dl = mul(g, g)
        # (s:t) = (d1 : d2) up to the factor L; recover primitive (s,t) and mu with gamma^2 = mu * delta(s,t)
        if dl[1] == 0 and dl[2] == 0:
            st = None
            for cand in [(1, 0), (0, 1), (1, 1), (1, -1), (2, 1), (1, 2)]:
                v = [e.subs({s: cand[0], t: cand[1]}) for e in param]
                if v[1] == 0 and v[2] == 0 and v[0] != 0:
                    st = cand
                    break
            if st is None:
                print(f"   gamma={g}: delta = {dl} is the parametrization's base point (limit)")
                continue
        else:
            gg = math.gcd(dl[1], dl[2])
            st = (dl[1] // gg, dl[2] // gg)
        v = [int(e.subs({s: st[0], t: st[1]})) for e in param]
        mu = sp.Rational(next(dl[i] for i in range(3) if v[i] != 0), next(v[i] for i in range(3) if v[i] != 0))
        assert all(sp.Rational(dl[i]) == mu*v[i] for i in range(3)), (g, dl, v, mu)
        fv = int(f6.subs({s: st[0], t: st[1]}))
        wsq = mu*fv
        num, den = sp.fraction(sp.nsimplify(wsq))
        sqf = sp.Mul(*[pr**(e % 2) for pr, e in sp.factorint(abs(int(num))*abs(int(den))).items()]) * (1 if wsq > 0 else -1)
        print(f"   gamma={g}: (s,t)={st}, mu={mu}, mu*f6(s,t)={wsq}, lambda (squarefree class) = {sqf}")
