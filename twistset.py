#!/usr/bin/env python3
# Copyright (C) 2026 Marcello Federico
# SPDX-License-Identifier: GPL-3.0-or-later
#
# This file is part of the fermat433 proof record
# <https://github.com/marchfederico/fermat433>.  It is free software: you may
# redistribute it and modify it under the terms of the GNU General Public
# License, either version 3 of the License or (at your option) any later
# version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
# the repository root, or <https://www.gnu.org/licenses/>.

"""Lemma A.3, the twist set: with delta = gamma^2 = mu * delta_k(s,t), show mu in {+-1} (k=0) and mu in {+-1, +-1/2} (k=1),
hence exactly the six curves A+-, B+-, C+-.  Elementary: contents of the parametrisation and the unit conditions."""
import math, itertools
import sympy as sp
from descent_explore_forms import mul, power, norm

d0, d1, d2, s, t, a, b, c = sp.symbols("d0 d1 d2 s t a b c")
eps = (-1, 1, 0)                      # epsilon = theta - 1 as (coeff of 1, theta, theta^2)
gam = (a, b, c)
gsq = [sp.expand(e) for e in mul(gam, gam)]
print("gamma^2 =", gsq)
for k in (0, 1):
    uk = tuple(-x for x in power(eps, k))
    Qc = sp.expand(mul(uk, mul((d0, d1, d2), (d0, d1, d2)))[2])
    M = sp.hessian(Qc, (d0, d1, d2)) / 2
    print(f"\n== k = {k}: conic Q_k = {Qc} = 0, Gram determinant {M.det()} (nonzero: smooth conic)")
    L = sp.expand(sp.diff(Qc, d0)); Qp = sp.expand(Qc - d0*L)
    param = [sp.expand(e) for e in (-Qp.subs({d1: s, d2: t}), s*L.subs({d1: s, d2: t}), t*L.subs({d1: s, d2: t}))]
    assert sp.expand(Qc.subs({d0: param[0], d1: param[1], d2: param[2]})) == 0
    print("   parametrisation through (1:0:0): delta_k(s,t) =", param)
    print("   its norm f_k(s,t) =", sp.factor(norm(tuple(param))))
    # (1) content of delta_k(s,t) for coprime (s,t): odd primes cannot divide all three coordinates
    res = [sp.resultant(param[i], param[j], s) for i, j in ((0, 1), (0, 2), (1, 2))]
    print("   resultants of coordinate pairs (in s):", res, " -> common odd prime factor of all three impossible when gcd(s,t)=1")
    conts = {}
    for S_ in range(-12, 13):
        for T_ in range(-12, 13):
            if math.gcd(S_, T_) != 1: continue
            v = [int(e.subs({s: S_, t: T_})) for e in param]
            conts.setdefault((S_ % 2, T_ % 2), set()).add(math.gcd(math.gcd(abs(v[0]), abs(v[1])), abs(v[2])))
    print("   contents observed by (s mod 2, t mod 2):", conts)
    # (2) gamma^2 primitive when gamma is primitive and a unit at 2 and 3 (a odd, a - b + c != 0 mod 3)
    bad2 = [(A, B, C) for A in range(2) for B in range(2) for C in range(2) if A % 2 == 1 and all(int(e.subs({a: A, b: B, c: C})) % 2 == 0 for e in gsq)]
    bad3 = [(A, B, C) for A in range(3) for B in range(3) for C in range(3) if (A - B + C) % 3 != 0 and all(int(e.subs({a: A, b: B, c: C})) % 3 == 0 for e in gsq)]
    print("   gamma^2 divisible by 2 with a odd:", bad2, "  divisible by 3 with a-b+c != 0 mod 3:", bad3, "  (both empty: gamma^2 primitive)")
    # (3) mu = +-1/content, and for k = 0 the theta^0 coordinate a^2 + 4bc is odd, so mu*s^2 odd forces s odd, content 1
    print("   theta^0-coordinate of delta = mu * delta_k(s,t)[0] =", sp.factor(param[0]), "must be odd (it equals a^2 + 4bc)")
    for S_par in (0, 1):
        vals = set()
        for S_ in range(-9, 10):
            for T_ in range(-9, 10):
                if math.gcd(S_, T_) != 1 or S_ % 2 != S_par: continue
                v = [int(e.subs({s: S_, t: T_})) for e in param]
                ct = math.gcd(math.gcd(abs(v[0]), abs(v[1])), abs(v[2]))
                vals.add((ct, (v[0] // ct) % 2))
        print(f"   s {'even' if S_par == 0 else 'odd'}: (content, parity of theta^0-coordinate of delta_k/content) in {vals}")
