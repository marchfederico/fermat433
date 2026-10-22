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

"""Independent re-check of the Mordell-Weil sieve (Prop. 6.2) from sieve_cert/inputs_<curve>.txt.

Plain Python, no PARI, no libraries. From the exact inputs (the field L, the sextic f, the generators
P1, P2, the fixed points x+, x- of the involution, the sieving primes, the candidate vectors a mod 499)
it recomputes everything the sieve
uses, by its own route: it reduces modulo the prime of L, builds the bielliptic quotients E1, E2 in the
non-minimal model of step3_setup.gp (the sieve's verdict does not depend on the model or on the choice
of generator), counts E_i(F_q) and X(F_q) by brute force, picks its own generator of the 499-part, and
takes discrete logarithms from a table. A candidate is removed at a prime when the image of its vector
is not the image of any point of X(F_q).

Usage: python3 sieve_cert/check.py [sieve_cert/inputs_Bminus.txt ...]   (default: both curves)
"""
import sys
from fractions import Fraction

ELL = 499


def read_inputs(path):
    data = {"primes": [], "cands": []}
    for line in open(path):
        w = line.split()
        if not w or w[0].startswith("#"):
            continue
        if w[0] == "PL":
            data["PL"] = [int(c) for c in w[1:]]
        elif w[0] == "F":
            data["F"] = [int(c) for c in w[1:]]
        elif w[0] == "GEN":
            data.setdefault("gens", []).append((Fraction(w[1]), Fraction(w[2])))
        elif w[0] in ("XP", "XM"):
            data[w[0]] = [Fraction(c) for c in w[1:]]
        elif w[0] == "PRIME":
            data["primes"].append((int(w[1]), int(w[2])))
        elif w[0] == "CAND":
            data["cands"].append((w[1], int(w[2]), int(w[3]), int(w[4])))
    return data


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))


class Field:
    def __init__(self, q):
        self.q = q

    def inv(self, a):
        assert a % self.q, "division by zero mod q"
        return pow(a, self.q - 2, self.q)

    def frac(self, c):
        return c.numerator * self.inv(c.denominator) % self.q

    def chi(self, a):                           # Legendre symbol
        a %= self.q
        return 0 if a == 0 else (1 if pow(a, (self.q - 1) // 2, self.q) == 1 else -1)

    def sqrt(self, a):                          # brute force is fine for q < 10^5
        a %= self.q
        for y in range(self.q):
            if y * y % self.q == a:
                return y
        raise ValueError("not a square")


def peval(coeffs, x, q):
    s = 0
    for c in reversed(coeffs):
        s = (s * x + c) % q
    return s


def pmul(a, b, q):
    out = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            out[i + j] = (out[i + j] + u * v) % q
    return out


class Curve:
    """y^2 = x^3 + a2 x^2 + a4 x + a6 over F_q; points are (x, y) or None for O."""

    def __init__(self, K, a2, a4, a6):
        self.K, self.q, self.a = K, K.q, (a2 % K.q, a4 % K.q, a6 % K.q)
        b2, b4, b6 = 4 * a2, 2 * a4, 4 * a6
        b8 = a2 * 4 * a6 - a4 * a4
        disc = (-b2 * b2 * b8 - 8 * b4 ** 3 - 27 * b6 * b6 + 9 * b2 * b4 * b6) % self.q
        assert disc, "bad reduction"

    def rhs(self, x):
        a2, a4, a6 = self.a
        return (x ** 3 + a2 * x * x + a4 * x + a6) % self.q

    def on(self, P):
        return P is None or (P[1] * P[1] - self.rhs(P[0])) % self.q == 0

    def add(self, P, Q):
        q = self.q
        if P is None:
            return Q
        if Q is None:
            return P
        if P[0] == Q[0] and (P[1] + Q[1]) % q == 0:
            return None
        if P == Q:
            lam = (3 * P[0] ** 2 + 2 * self.a[0] * P[0] + self.a[1]) * self.K.inv(2 * P[1]) % q
        else:
            lam = (Q[1] - P[1]) * self.K.inv(Q[0] - P[0]) % q
        x3 = (lam * lam - self.a[0] - P[0] - Q[0]) % q
        return (x3, (lam * (P[0] - x3) - P[1]) % q)

    def mul(self, n, P):
        R = None
        while n:
            if n & 1:
                R = self.add(R, P)
            P = self.add(P, P)
            n >>= 1
        return R

    def order(self):
        return self.q + 1 + sum(self.K.chi(self.rhs(x)) for x in range(self.q))


def check_prime(data, q, r, alive):
    assert is_prime(q) and q != ELL, q
    F1 = data["F"]
    assert peval(data["PL"], r, q) == 0, "r is not a root of PL mod q"
    K = Field(q)
    ev = lambda cs: sum(K.frac(c) * pow(r, k, q) for k, c in enumerate(cs)) % q
    xp, xm = ev(data["XP"]), ev(data["XM"])
    assert (xp - xm) % q
    # F(X) = (X - 1)^6 f((xm X - xp)/(X - 1)): even sextic A X^6 + B X^4 + C X^2 + D
    F = [0] * 7
    for k, c in enumerate(F1):
        term = [c % q]
        for _ in range(k):
            term = pmul(term, [(-xp) % q, xm], q)
        for _ in range(6 - k):
            term = pmul(term, [q - 1, 1], q)
        F = [(u + v) % q for u, v in zip(F, term)]
    assert F[1] == F[3] == F[5] == 0, "F is not even: wrong fixed points"
    D, C, B, A = F[0], F[2], F[4], F[6]
    E1 = Curve(K, B, A * C, A * A * D)
    E2 = Curve(K, C, B * D, A * D * D)

    def phi(x, y):                                  # (phi1, phi2) of an affine point of X
        if x == xm:
            return None, (0, D * y % q)
        if x == xp:
            return (0, -A * y % q), None
        X = (x - xp) * K.inv(x - xm) % q
        Y = y * pow(X - 1, 3, q) % q
        return (A * X * X % q, A * Y % q), (D * K.inv(X * X) % q, D * Y * K.inv(pow(X, 3, q)) % q)

    def phi_inf(s):                                 # the point at infinity with y/x^3 -> s
        Y = s * pow(xm - xp, 3, q) % q
        return (A, A * Y % q), (D, D * Y % q)

    logs = []
    for E in (E1, E2):
        N = E.order()
        assert N % ELL == 0 and N % (ELL * ELL), f"499-part of #E(F_q) = {N} is not cyclic of order 499"
        c = N // ELL
        g = None
        for x in range(q):
            if K.chi(E.rhs(x)) >= 0:
                g = E.mul(c, (x, K.sqrt(E.rhs(x))))
                if g is not None:
                    break
        assert g is not None and E.mul(ELL, g) is None
        table, P = {None: 0}, None
        for k in range(1, ELL):
            P = E.add(P, g)
            table[P] = k
        logs.append((E, c, table))

    def xi(i, P):
        E, c, table = logs[i]
        assert E.on(P)
        return table[E.mul(c, P)]

    def image(pair):
        return (xi(0, pair[0]), xi(1, pair[1]))

    gens = [image(phi(K.frac(gx), K.frac(gy))) for gx, gy in data["gens"]]
    allowed, npts = set(), 0
    for x in range(q):
        fx = peval([c % q for c in F1], x, q)
        if K.chi(fx) < 0:
            continue
        y = K.sqrt(fx)
        for yy in ({y, (-y) % q}):
            allowed.add(image(phi(x, yy)))
            npts += 1
    lead = F1[6] % q                                # points at infinity: y/x^3 -> s, s^2 = f_6
    if K.chi(lead) > 0:
        s = K.sqrt(lead)
        for ss in ({s, (-s) % q}):
            allowed.add(image(phi_inf(ss)))
            npts += 1
    still, killed = [], 0
    for cand in alive:
        a1, a2 = cand[2], cand[3]
        v = ((a1 * gens[0][0] + a2 * gens[1][0]) % ELL, (a1 * gens[0][1] + a2 * gens[1][1]) % ELL)
        if v in allowed:
            still.append(cand)
        else:
            killed += 1
    print(f"q={q} r={r}: #E1={E1.order()} #E2={E2.order()} |X(F_q)|={npts} |allowed|={len(allowed)} "
          f"killed {killed}, still alive {len(still)}")
    return still


def main():
    paths = sys.argv[1:] or ["sieve_cert/inputs_Bminus.txt", "sieve_cert/inputs_Cplus.txt"]
    for path in paths:
        data = read_inputs(path)
        alive = data["cands"]
        print(f"{path}: candidates: {len(alive)}")
        for q, r in data["primes"]:
            alive = check_prime(data, q, r, alive)
        print("survivors:")
        for c in alive:
            print("  ", c)


if __name__ == "__main__":
    main()
