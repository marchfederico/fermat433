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

"""qc_sigma.py -- the Mazur-Tate p-adic sigma function as a power series, the local height at p,
and the local heights away from p.

Quadratic Chabauty needs the local component at p of the canonical p-adic height as an analytic
function along a residue disk, not just its value at a point. PARI evaluates the global height
(ellpadicheight) but exposes no sigma, so it is built here from the formal group.

Sigma is characterised (Mazur-Tate, Mazur-Stein-Tate) by

    D^2 log(sigma) = -(x(t) + c),      D = (1/f) d/dt,

with t the formal parameter, x(t) the formal x-coordinate (ellformalpoint) and omega = f dt the
invariant differential (ellformaldifferential). The constant is exactly PARI's ellpadics2, which
its documentation defines as b_2/12 - E_2/12 and characterises as the unique c making sigma lie in
t Z_p[[t]]. That was confirmed here two ways: an integrality scan over candidates, where c = s2 was
the only p-integral choice at every prime that discriminates, and the height check below.

Integrating twice against omega gives log(sigma(t)/t) with zero constant term, so

    sigma(t) = t exp(v(t)),   v = int int -(x + c) domega,

and everything is a series computation, so sigma composes with the formal parameter along a disk.

Two facts about PARI's convention matter and are easy to get wrong. First, ellpadicheight returns
the pair [f, g] of coordinates in de Rham cohomology; the *canonical* height is the combination
ellpadicheight(E,p,n,P) * [1,-s2]~, not the first component. Second, the identity

    canonical height = log_p(denominator(x)) - 2 log_p(sigma(P))

holds only for P in the kernel of reduction at p whose reduction at every finite place is
non-singular. Off the identity component of the Neron model at a bad prime the two differ by
precisely the sum of the local heights away from p -- which is not an error but the second
ingredient quadratic Chabauty needs, and is what away_from_p returns.

The reduction at p must be good and ordinary; ellpadics2 refuses supersingular primes. The sigma
formula for the local height is stated for short models y^2 = x^3 + ax + b.
"""
from __future__ import annotations

import cypari2

_PARI = None


def pari():
    global _PARI
    if _PARI is None:
        _PARI = cypari2.Pari()
        try:
            _PARI.default("parisizemax", "4000000000")
        except Exception:  # noqa: BLE001
            pass
    return _PARI


def is_ordinary(ainvs, p):
    """Good ordinary reduction: p does not divide the discriminant, and a_p is a unit."""
    P = pari()
    if int(P(f"ellinit({list(ainvs)}).disc")) % p == 0:
        return False
    return int(P(f"ellap(ellinit({list(ainvs)}),{p})")) % p != 0


def sigma_series(ainvs, p, n=16, terms=26):
    """v(t) = log(sigma(t)/t) as a t-series with p-adic coefficients, and the constant c = s2."""
    P = pari()
    s2 = P(f"ellpadics2(ellinit({list(ainvs)}),{p},{n})")
    x_t = P(f"ellformalpoint(ellinit({list(ainvs)}),{terms})[1]")
    f_t = P(f"ellformaldifferential(ellinit({list(ainvs)}),{terms})[1]")
    u = P(f"intformal((-(({x_t}) + ({s2}))) * ({f_t}))")
    # u * omega carries a 1/t term whose residue is 1: that is the log(t) in log(sigma) = log t + v.
    w = P(f"({u}) * ({f_t})")
    res = P(f"polcoeff({w}, -1)")
    v = P(f"intformal(({w}) - ({res})/x)")
    return v, s2, res


def reduction_order(ainvs, p):
    return int(pari()(f"ellcard(ellinit({list(ainvs)}),{p})"))


def formal_parameter(point):
    """t = -x/y; the point must lie in the kernel of reduction for the series to converge."""
    return pari()(f"-({point}[1])/({point}[2])")


def log_sigma(v_series, t_value, p, n):
    """log_p(sigma) = log_p(t) + v(t), on PARI's Iwasawa branch with log_p(p) = 0."""
    P = pari()
    return P(f"subst(truncate({v_series}), x, ({t_value}) + O({p}^{n})) + log(({t_value}) + O({p}^{n}))")


def lambda_p(ainvs, point, v_series, p, n):
    """The local height at p: log_p(denominator(x)) - 2 log_p(sigma). Short models, kernel of reduction."""
    P = pari()
    t = formal_parameter(point)
    return P(f"log(denominator(({point})[1]) + O({p}^{n})) - 2*({log_sigma(v_series, t, p, n)})")


def canonical_height(ainvs, point, p, n, s2=None):
    """The canonical cyclotomic height: ellpadicheight(E,p,n,P) * [1,-s2]~ (PARI's own recipe)."""
    P = pari()
    if s2 is None:
        s2 = P(f"ellpadics2(ellinit({list(ainvs)}),{p},{n})")
    return P(f"ellpadicheight(ellinit({list(ainvs)}),{p},{n},{point}) * [1,-({s2})]~")


def away_from_p(ainvs, point, v_series, p, n, s2=None):
    """Sum over v != p of the local heights: canonical height minus the local height at p.
    Zero exactly when the point reduces non-singularly at every finite place."""
    P = pari()
    return P(f"({canonical_height(ainvs, point, p, n, s2)}) - ({lambda_p(ainvs, point, v_series, p, n)})")


if __name__ == "__main__":
    import json
    P = pari()
    curves = json.load(open("/tmp/rank1_short.json"))
    n, terms = 16, 26
    agree = total = nonzero = 0
    print(f"self-test: sigma with c = s2, precision {n} digits, {terms} series terms\n")
    for a, b, G in curves:
        ainvs = [0, 0, 0, a, b]
        for p_ in (5, 7, 11, 13):
            if not is_ordinary(ainvs, p_):
                continue
            v, s2, res = sigma_series(ainvs, p_, n=n, terms=terms)
            m = reduction_order(ainvs, p_)
            assert str(res) == "1", f"residue should be 1, got {res}"
            for k in (1, 2):
                Q = P(f"ellmul(ellinit({ainvs}),{G},{k*m})")
                lam = lambda_p(ainvs, Q, v, p_, n)
                can = canonical_height(ainvs, Q, p_, n, s2)
                d = P(f"({can}) - ({lam})")
                logE = P(f"ellpadiclog(ellinit({ainvs}),{p_},{n},{Q})")
                g = P(f"ellpadicheight(ellinit({ainvs}),{p_},{n},{Q})[2] + ({logE})^2")
                zero = str(d).startswith("O(") or str(d) == "0"
                okg = str(g).startswith("O(") or str(g) == "0"
                total += 1; agree += zero; nonzero += (not zero)
                tag = "lambda_p = canonical height" if zero else f"away-from-p part {str(d)[:30]}"
                print(f"  y^2=x^3+({a})x+({b}) p={p_:3} {k*m}G: {tag}"
                      f"{'' if okg else '   [g check FAILED: ' + str(g)[:24] + ']'}")
    print(f"\n{total} point/prime pairs: {agree} with zero away-from-p part (identity component everywhere), "
          f"{nonzero} with a non-zero one.")
    print("A non-zero residual is the sum of local heights away from p, not a failure of sigma.")
