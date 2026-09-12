# Copyright (C) 2026 Marcello Federico
# SPDX-License-Identifier: GPL-3.0-or-later
#
# This file is part of the fermat433 proof record
# <https://github.com/marchfederico/fermat433>.  It is free software: you may
# redistribute it and modify it under the terms of the GNU General Public
# License, either version 3 of the License or (at your option) any later
# version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
# the repository root, or <https://www.gnu.org/licenses/>.

"""Descent for x^4 + 2y^3 + z^3 = 0 over K = Q(t), t^3 = 2.
Primitive solution -> alpha = z + y t = -(t-1)^k gamma^4, k in {0,1,2,3}, gamma = a + b t + c t^2.
C_k: coefficient of t^2 in -(t-1)^k gamma^4 vanishes (plane quartic over Q)."""
import itertools, math, time
import numpy as np
import sympy

def mul(u, v):
    a0, a1, a2 = u; b0, b1, b2 = v
    return (a0*b0 + 2*(a1*b2 + a2*b1), a0*b1 + a1*b0 + 2*a2*b2, a0*b2 + a1*b1 + a2*b0)

def power(u, n):
    out = (1, 0, 0)
    for _ in range(n):
        out = mul(out, u)
    return out

def norm(u):
    a, b, c = u
    return a**3 + 2*b**3 + 4*c**3 - 6*a*b*c

A, B, C = sympy.symbols("a b c")
eps = (-1, 1, 0)                                   # t - 1, norm +1
assert norm(eps) == 1 and norm((1, -1, 0)) == -1
forms = {}
for k in range(4):
    u = tuple(-x for x in power(eps, k))
    assert norm(u) == -1
    g4 = power((A, B, C), 4)
    al = mul(u, g4)
    z, y, F = [sympy.expand(e) for e in al]
    forms[k] = (F, z, y)
    pass
    pass
    # identity check: z^3 + 2y^3 = -N(gamma)^4 as polynomials when F = 0 is not an identity; check N(alpha) = -N(gamma)^4
    Nal = sympy.expand(al[0]**3 + 2*al[1]**3 + 4*al[2]**3 - 6*al[0]*al[1]*al[2])
    assert sympy.expand(Nal + norm((A, B, C))**4) == 0
pass

