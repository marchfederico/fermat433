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
    print(f"k={k}: unit {u}")
    print(f"   C_k: {F} = 0")
    # identity check: z^3 + 2y^3 = -N(gamma)^4 as polynomials when F = 0 is not an identity; check N(alpha) = -N(gamma)^4
    Nal = sympy.expand(al[0]**3 + 2*al[1]**3 + 4*al[2]**3 - 6*al[0]*al[1]*al[2])
    assert sympy.expand(Nal + norm((A, B, C))**4) == 0
print("identity N(alpha) = -N(gamma)^4 verified symbolically for all k")

# ---- search small gamma on each C_k
Bd = 60
rng = np.arange(-Bd, Bd + 1, dtype=np.int64)
sols = {}
t0 = time.time()
for k in range(4):
    F, z, y = forms[k]
    f = sympy.lambdify((A, B, C), F, "numpy")
    found = []
    for a in range(-Bd, Bd + 1):
        bb, cc = np.meshgrid(rng, rng, indexing="ij")
        aa = np.full_like(bb, a)
        vals = f(aa, bb, cc)
        idx = np.argwhere(vals == 0)
        for i, j in idx:
            g = (a, int(rng[i]), int(rng[j]))
            if g == (0, 0, 0) or math.gcd(math.gcd(g[0], g[1]), g[2]) != 1:
                continue
            first = next(v for v in g if v != 0)
            if first < 0:
                continue
            found.append(g)
    out = []
    for g in found:
        zz, yy = int(z.subs({A: g[0], B: g[1], C: g[2]})), int(y.subs({A: g[0], B: g[1], C: g[2]}))
        xx = norm(g)
        d = math.gcd(math.gcd(abs(xx), abs(yy)), abs(zz))
        assert xx**4 + 2*yy**3 + zz**3 == 0
        out.append((g, (xx, yy, zz), d))
    sols[k] = out
    print(f"k={k}: gamma with max |coef| <= {Bd} on C_k: {len(out)} -> {[(g, s) for g, s, d in out]}")
print(f"search time {time.time() - t0:.0f}s")

# ---- local solubility: primitive solutions mod p^m, lifted level by level
def local_levels(F, p, M):
    f = sympy.lambdify((A, B, C), F, "math")
    level = [(a, b, c) for a in range(p) for b in range(p) for c in range(p) if (a % p, b % p, c % p) != (0, 0, 0) and f(a, b, c) % p == 0]
    counts = [len(level)]
    for m in range(2, M + 1):
        q = p ** m
        nxt = []
        for (a, b, c) in level:
            for da in range(p):
                for db in range(p):
                    for dc in range(p):
                        a2, b2, c2 = a + da * p ** (m - 1), b + db * p ** (m - 1), c + dc * p ** (m - 1)
                        if f(a2, b2, c2) % q == 0:
                            nxt.append((a2, b2, c2))
        level = nxt
        counts.append(len(level))
        if not level:
            break
    return counts

for k in range(4):
    F = forms[k][0]
    print(f"k={k}: primitive solutions mod 2^m, m=1..: {local_levels(F, 2, 7)}")
    print(f"k={k}: primitive solutions mod 3^m, m=1..: {local_levels(F, 3, 5)}")
    # good primes: smooth F_p points
    grads = [sympy.diff(F, v) for v in (A, B, C)]
    fs = sympy.lambdify((A, B, C), [F] + grads, "math")
    smooth = {}
    for p in [5, 7, 11, 13, 17, 19, 23, 29, 31]:
        cnt = 0
        for a in range(p):
            for b in range(p):
                for c in range(p):
                    if (a, b, c) == (0, 0, 0):
                        continue
                    v = fs(a, b, c)
                    if v[0] % p == 0 and any(g % p for g in v[1:]):
                        cnt += 1
        smooth[p] = cnt // (p - 1)
    print(f"k={k}: smooth projective F_p points: {smooth}")
    # real points: sign change on a grid
    f = sympy.lambdify((A, B, C), F, "math")
    vals = [f(math.cos(u) * math.sin(v), math.sin(u) * math.sin(v), math.cos(v)) for u in np.linspace(0, 6.283, 90) for v in np.linspace(0, 3.1416, 45)]
    print(f"k={k}: real points: {'yes' if min(vals) < 0 < max(vals) else 'no (definite form)'}")
