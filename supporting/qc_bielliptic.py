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

"""qc_bielliptic.py -- quadratic Chabauty for bielliptic genus 2 curves, on PARI alone.

For X : y^2 = a6 x^6 + a4 x^4 + a2 x^2 + a0 with both elliptic quotients of rank 1, classical
Chabauty-Coleman is useless: the Mordell-Weil rank equals the genus. The quadratic Chabauty function
of Bianchi-Padurariu (arXiv:2212.11635, Thm 2.3) still cuts the rational points out of a finite set:

    rho(z) = lambda_p(phi1(z)) - lambda_p(phi2(z)) - 2 log(x(z))
             - alpha1 Log(phi1(z))^2 + alpha2 Log(phi2(z))^2,          rho(X(Q)) contained in Omega

    phi1(x,y) = (a6 x^2, a6 y)      on  E1: Y^2 = X^3 + a4 X^2 + a2 a6 X + a0 a6^2
    phi2(x,y) = (a0 x^-2, a0 y x^-3) on  E2: Y^2 = X^3 + a2 X^2 + a4 a0 X + a6 a0^2

with alpha_i = h_p(P_i)/Log(P_i)^2 for any infinite-order P_i, well defined because rank 1 forces the
height to be alpha times the square of the logarithm. The single-quotient analogue does NOT work: the
away-from-p sum contains twice the logarithm of the denominator of x, which is unbounded on E(Q), so
its value set is infinite and constrains nothing. Both unbounded terms cancel here because
x(phi1(z)) * x(phi2(z)) = a0 a6 is constant, which is what the -2 log(x(z)) term is for.

The split Jacobian is also what lets the p-adic sigma function stand in for a double Coleman integral
(Bianchi, arXiv:1904.04622), so everything below is elliptic-curve arithmetic and power series.

Ingredients, each verified in this repository rather than assumed:
  qc_sigma.lambda_p      the local height at p from the Mazur-Tate sigma, checked against PARI
  qc_local.lambda_values the away-from-p values by Kodaira type, recovered by lindep over 227 curves
Two conventions are easy to get wrong and are pinned down empirically here rather than assumed.
PARI's elldivpol is psi_m for odd m but psi_m divided by the differential's denominator for even m;
with the wrong parity the local height failed on 7 of 8 points outside the formal group, and with
the right one on none of 14. And the sigma identities hold only on models with a1 = a3 = 0: across
six pairs of isomorphic models with equal j-invariants, every a1 = 1 minimal model failed all four
trials and every a1 = a3 = 0 form passed all four. The quotient models built here always satisfy
that, at the price of being non-minimal, almost always only at 2; qc_local.non_minimal_shift carries
the resulting shift of the away-from-p values.
"""
from __future__ import annotations

import cypari2

_PARI = None


def pari():
    global _PARI
    if _PARI is None:
        _PARI = cypari2.Pari()
        try:
            _PARI.default("parisizemax", "8000000000")
        except Exception:  # noqa: BLE001
            pass
    return _PARI


def quotients(G):
    """(E1, E2, a0, a2, a4, a6) from an even sextic given as ascending coefficients."""
    if any(G[i] for i in (1, 3, 5)):
        raise ValueError("sextic is not even, so the curve is not in bielliptic form")
    a0, a2, a4, a6 = G[0], G[2], G[4], G[6]
    return [0, a4, 0, a2 * a6, a0 * a6 * a6], [0, a2, 0, a4 * a0, a6 * a0 * a0], a0, a2, a4, a6


def sigma_series(ainvs, p, n, terms):
    """v(t) = log(sigma(t)/t), with the ODE constant c = ellpadics2."""
    P = pari()
    s2 = P(f"ellpadics2(ellinit({list(ainvs)}),{p},{n})")
    x_t = P(f"ellformalpoint(ellinit({list(ainvs)}),{terms})[1]")
    f_t = P(f"ellformaldifferential(ellinit({list(ainvs)}),{terms})[1]")
    u = P(f"intformal((-(({x_t}) + ({s2}))) * ({f_t}))")
    w = P(f"({u}) * ({f_t})")
    return P(f"intformal(({w}) - polcoeff({w},-1)/x)"), s2


def _log_sigma(v, Q, p, n):
    P = pari()
    t = P(f"-({Q}[1])/({Q}[2])")
    return P(f"subst(truncate({v}), x, ({t})+O({p}^{n})) + log(({t})+O({p}^{n}))")


def _log_psi(ainvs, m, Q, p, n):
    """PARI's elldivpol is psi_m for odd m and psi_m/(2y) for even m -- established by testing
    log sigma(mP) - m^2 log sigma(P) = log psi_m(P): odd matched 16/16, even 24/24."""
    P = pari()
    x_, y_ = P(f"({Q})[1]"), P(f"({Q})[2]")
    e = P(f"subst(elldivpol(ellinit({list(ainvs)}),{m}), x, ({x_}))")
    val = e if m % 2 else P(f"({e})/(2*({y_}))")
    return P(f"log(({val}) + O({p}^{n}))")


def lambda_p(ainvs, Q, v, p, n, m=None):
    """Bianchi's local height at p: -2 log sigma(Q) in the formal group, and
    -(2/m^2) log( sigma(mQ) / psi_m(Q) ) in general.

    Torsion is a genuine exception, not an oversight. For odd p of good reduction the torsion of
    E(Q) injects into E(F_p), so m = #E(F_p) sends every torsion point to the origin and there is no
    multiple left in the formal group. Such a point has zero canonical height, so its local height at
    p is exactly minus the away-from-p sum, which already lies in the span Omega ranges over.
    Returning 0 and widening Omega by that span is therefore sound: a larger finite set can only
    admit extra candidate zeros, never discard a rational point. The flag says when this happened.
    """
    P = pari()
    if m is None:
        m = int(P(f"ellcard(ellinit({list(ainvs)}),{p})"))
    mQ = P(f"ellmul(ellinit({list(ainvs)}),{Q},{m})")
    if str(mQ) == "[0]":
        return P("0"), True
    return P(f"-(2/{m}^2) * (({_log_sigma(v, mQ, p, n)}) - ({_log_psi(ainvs, m, Q, p, n)}))"), False


def log_E(ainvs, Q, p, n, m=None):
    """The formal logarithm at a general point: Log(Q) = Log(mQ)/m."""
    P = pari()
    if m is None:
        m = int(P(f"ellcard(ellinit({list(ainvs)}),{p})"))
    mQ = P(f"ellmul(ellinit({list(ainvs)}),{Q},{m})")
    return P(f"ellpadiclog(ellinit({list(ainvs)}),{p},{n},{mQ}) / {m}")


def minimal_model(ainvs):
    """(minimal a-invariants, change of variable) -- PARI's height is unreliable off-minimal."""
    P = pari()
    res = P(f"E=ellinit({list(ainvs)}); Em=ellminimalmodel(E,&v); [[Em.a1,Em.a2,Em.a3,Em.a4,Em.a6], v]")
    am = [int(P(f"({res})[1][{k+1}]")) for k in range(5)]
    return am, P(f"({res})[2]")


def alpha(ainvs, gen, p, n):
    """h_p(P)/Log(P)^2, the same for every infinite-order P when the rank is 1.

    The height is taken on the MINIMAL model and the logarithm on the given model. That mix is the
    correct one, not a fudge: the canonical height is an invariant of the curve, while the formal
    logarithm scales with the invariant differential and so belongs to whichever model the rest of
    the computation uses. Taking the height off-minimal is what PARI itself reports a bug on.
    """
    P = pari()
    am, vv = minimal_model(ainvs)
    Gm = P(f"ellchangepoint({gen}, {vv})")
    s2m = P(f"ellpadics2(ellinit({am}),{p},{n})")
    h = P(f"ellpadicheight(ellinit({am}),{p},{n},{Gm}) * [1,-({s2m})]~")
    lg = log_E(ainvs, gen, p, n)
    return P(f"({h}) / ({lg})^2")


def rho(G, gens, p, n=20, terms=44, point=None, widened=False):
    """The quadratic Chabauty function at one rational point (x, y) of y^2 = G(x)."""
    P = pari()
    E1, E2, a0, a2, a4, a6 = quotients(G)
    x, y = point
    if x == 0:
        raise ValueError("x = 0: use the translated patch")
    p1 = P(f"[{a6}*({x})^2, {a6}*({y})]")
    p2 = P(f"[{a0}/({x})^2, {a0}*({y})/({x})^3]")
    v1, _ = sigma_series(E1, p, n, terms)
    v2, _ = sigma_series(E2, p, n, terms)
    a_1 = alpha(E1, gens[0], p, n)
    a_2 = alpha(E2, gens[1], p, n)
    l1, t1 = lambda_p(E1, p1, v1, p, n)
    l2, t2 = lambda_p(E2, p2, v2, p, n)
    g1 = P("0") if t1 else log_E(E1, p1, p, n)
    g2 = P("0") if t2 else log_E(E2, p2, p, n)
    val = P(f"({l1}) - ({l2}) - 2*log(({x}) + O({p}^{n})) - ({a_1})*({g1})^2 + ({a_2})*({g2})^2")
    return (val, t1 or t2) if widened else val
