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

"""qc_solve.py -- the quadratic Chabauty solver: rho along each residue disk, and its zeros.

qc_bielliptic.rho evaluates at one point, which can confirm a known rational point but never find an
unknown one. This expands rho as a power series in each residue disk of X(Q_p) and bounds its zeros.

For a disk around (x0, y0) with y0 not congruent to 0, set x(t) = x0 + p t and take y(t) as the
branch of the square root of G(x(t)) agreeing with y0. Elliptic arithmetic over power series works in
PARI, so phi_i(z(t)) can be multiplied into the formal group and the sigma series composed with the
resulting formal parameter; the constant term reproduces the pointwise value.

For each w in Omega, the rational points of the disk are among the zeros of rho(t) - w, and
Strassman's theorem bounds how many there are: for a series with coefficients in Z_p tending to zero,
the number of zeros with |t| <= 1 is at most the largest N whose coefficient attains the minimum
valuation. Summing those bounds over Omega bounds the rational points in the disk. Double roots are
expected where an automorphism fixes the point (x = 0, y = 0, or infinity), so a bound of 2 there is
not evidence of a second point.
"""
from __future__ import annotations

from fractions import Fraction as Fr

from qc_bielliptic import quotients, sigma_series, _log_sigma, _log_psi, alpha, log_E, pari


def disks(G, p):
    """Integral residue disks: (x0, y0) mod p with G(x0) a square mod p. Weierstrass disks (y0 = 0)
    are flagged, since the parametrisation by x breaks there."""
    out = []
    for x0 in range(p):
        val = sum(c * pow(x0, i, p) for i, c in enumerate(G)) % p
        for y0 in range(p):
            if (y0 * y0 - val) % p == 0:
                out.append((x0, y0, y0 % p == 0))
    return out


def disk_series(G, p, x0, y0, D, n):
    """x(t), y(t) on the disk around (x0, y0), as PARI series in t."""
    P = pari()
    poly = " + ".join(f"({c})*xs^{i}" for i, c in enumerate(G) if c)
    # the constant term must carry p-adic precision: with integer coefficients PARI reads log(xs)
    # as the REAL logarithm and refuses to mix it with p-adics further down
    P(f"xs = ({x0} + O({p}^{n})) + {p}*t + O(t^{D})")
    P(f"rhs = {poly} + O({p}^{n})")
    P("ys = sqrt(rhs)")
    if int(P(f"Mod(truncate(polcoeff(ys,0)) - {y0}, {p}) == 0")) != 1:
        P("ys = -ys")
    return P("xs"), P("ys")


def rho_series(G, gens, p, n=16, terms=34, D=10, disk=None):
    """rho expanded along one residue disk, as a series in t."""
    P = pari()
    E1, E2, a0, a2, a4, a6 = quotients(G)
    x0, y0, _ = disk
    xs, ys = disk_series(G, p, x0, y0, D, n)
    v1, _ = sigma_series(E1, p, n, terms)
    v2, _ = sigma_series(E2, p, n, terms)
    a_1, a_2 = alpha(E1, gens[0], p, n), alpha(E2, gens[1], p, n)
    parts = []
    for E, v, xq, yq in ((E1, v1, "{a6}*xs^2".format(a6=a6), "{a6}*ys".format(a6=a6)),
                         (E2, v2, "({a0})/xs^2".format(a0=a0), "({a0})*ys/xs^3".format(a0=a0))):
        m = int(P(f"ellcard(ellinit({E}),{p})"))
        P(f"Qs = [{xq}, {yq}]")
        P(f"mQ = ellmul(ellinit({E}), Qs, {m})")
        P("tp = -mQ[1]/mQ[2]")
        P(f"vs = subst(truncate({v}), x, tp)")
        e = P(f"subst(elldivpol(ellinit({E}),{m}), x, {xq})")
        psi = f"({e})" if m % 2 else f"({e})/(2*({yq}))"
        lam = P(f"-(2/{m}^2) * ((log(tp) + vs) - log({psi}))")
        lg = P(f"ellformallog(ellinit({E}),{terms})")
        parts.append((lam, P(f"subst(truncate({lg}), x, tp) / {m}")))
    (l1, g1), (l2, g2) = parts
    return P(f"({l1}) - ({l2}) - 2*log(xs) - ({a_1})*({g1})^2 + ({a_2})*({g2})^2")


def strassman(series, p, tmax=None):
    """Strassman bound on zeros with |t| <= 1: the largest index attaining the minimum valuation."""
    P = pari()
    deg = int(P(f"poldegree(truncate({series}))"))
    hi = deg if tmax is None else min(deg, tmax)
    vals = []
    for k in range(hi + 1):
        c = P(f"polcoeff({series}, {k})")
        s = str(c)
        if s == "0" or s.startswith("O("):
            vals.append(None)
        else:
            vals.append(int(P(f"valuation({c}, {p})")))
    live = [(k, v) for k, v in enumerate(vals) if v is not None]
    if not live:
        return None, vals
    mn = min(v for _, v in live)
    return max(k for k, v in live if v == mn), vals


# ----------------------------------------------------------------- the complete per-curve solver


def _padic_series_disk(G, gens, p, n, terms, D, x0, y0):
    """rho along an ordinary residue disk, x = x0 + p t."""
    from qc_bielliptic import quotients, sigma_series, alpha
    P = pari()
    E1, E2, a0, a2, a4, a6 = quotients(G)
    poly = " + ".join(f"({c})*xs^{k}" for k, c in enumerate(G) if c)
    P(f"xs = ({x0} + O({p}^{n})) + {p}*t + O(t^{D})")
    P(f"ys = sqrt({poly})")
    if int(P(f"Mod(truncate(polcoeff(ys,0)) - {y0}, {p}) == 0")) != 1:
        P("ys = -ys")
    v1, _ = sigma_series(E1, p, n, terms)
    v2, _ = sigma_series(E2, p, n, terms)
    a_1, a_2 = alpha(E1, gens[0], p, n), alpha(E2, gens[1], p, n)
    parts = []
    for E, v, xq, yq in ((E1, v1, f"({a6})*xs^2", f"({a6})*ys"),
                         (E2, v2, f"({a0})/xs^2", f"({a0})*ys/xs^3")):
        m = int(P(f"ellcard(ellinit({E}),{p})"))
        P(f"mQ = ellmul(ellinit({E}), [{xq}, {yq}], {m}); tp = -mQ[1]/mQ[2]")
        P(f"edp = subst(elldivpol(ellinit({E}),{m}), x, {xq}) * (1 + O({p}^{n}))")
        psi = "edp" if m % 2 else f"edp/(2*({yq}))"
        # combine the two logarithms: within a disk the formal parameter and the division polynomial
        # can both vanish (the image passes through 2-torsion), and only their ratio is regular
        lam = P(f"-(2/{m}^2) * (log(tp/({psi})) + subst(truncate({v}), x, tp))")
        lg = P(f"subst(truncate(ellformallog(ellinit({E}),{terms})), x, tp) / {m}")
        parts.append((lam, lg))
    (l1, g1), (l2, g2) = parts
    return P(f"({l1}) - ({l2}) - 2*log(xs) - ({a_1})*({g1})^2 + ({a_2})*({g2})^2")


def _padic_series_disk_x0(G, gens, p, n, terms, D, y0):
    """rho along the disk x = 0 mod p, where the second quotient map runs into the formal group.

    There its local parameter is S = -x/y, its local height contributes 2 log x - 2 log y, and the
    explicit -2 log(x) cancels, leaving a regular function. Two traps live here and both make PARI
    silently switch to REAL arithmetic, because the disk parameter vanishes at the origin: the
    square root must carry p-adic precision, and so must the division polynomial, whose value
    otherwise has exact integer coefficients and yields a real logarithm.
    """
    from qc_bielliptic import quotients, sigma_series, alpha
    P = pari()
    E1, E2, a0, a2, a4, a6 = quotients(G)
    P(f"xs = {p}*t*(1 + O({p}^{n})) + O(t^{D})")
    poly = " + ".join(f"({c})*xs^{k}" for k, c in enumerate(G) if c)
    P(f"ys = sqrt(({poly}) + O({p}^{n}))")
    if int(P(f"Mod(truncate(polcoeff(ys,0)) - {y0}, {p}) == 0")) != 1:
        P("ys = -ys")
    v1, _ = sigma_series(E1, p, n, terms)
    v2, _ = sigma_series(E2, p, n, terms)
    a_1, a_2 = alpha(E1, gens[0], p, n), alpha(E2, gens[1], p, n)
    m1 = int(P(f"ellcard(ellinit({E1}),{p})"))
    P(f"q1 = [({a6})*xs^2, ({a6})*ys]")
    P(f"mQ1 = ellmul(ellinit({E1}), q1, {m1}); tp1 = -mQ1[1]/mQ1[2]")
    P(f"edp = subst(elldivpol(ellinit({E1}),{m1}), x, ({a6})*xs^2) * (1 + O({p}^{n}))")
    psi1 = "edp" if m1 % 2 else f"edp/(2*(({a6})*ys))"
    lam1 = P(f"-(2/{m1}^2) * (log(tp1/({psi1})) + subst(truncate({v1}), x, tp1))")
    lg1 = P(f"subst(truncate(ellformallog(ellinit({E1}),{terms})), x, tp1) / {m1}")
    P("S = -xs/ys")
    lg2 = P(f"subst(truncate(ellformallog(ellinit({E2}),{terms})), x, S)")
    v2S = P(f"subst(truncate({v2}), x, S)")
    return P(f"({lam1}) - 2*log(ys) + 2*({v2S}) - ({a_1})*({lg1})^2 + ({a_2})*({lg2})^2")


def all_disks(G, p):
    """Every residue disk, tagged: ('gen', x0, y0), ('zero', 0, y0), ('weier', x0, y0)."""
    out = []
    for x0, y0, wei in disks(G, p):
        out.append(("weier" if wei else ("zero" if x0 == 0 else "gen"), x0, y0))
    return out


def reduction_order(E, x_red, p):
    """Order of the reduced point (x_red, 0) in E(F_p), falling back to the group order.

    Using the point's OWN reduction order is what makes a Weierstrass disk computable. Multiplying
    by the order of the whole group sends the 2-torsion image at the branch point to the origin, and
    the series arithmetic then collapses: over a sample only 20 of 148 such disks built, failing as
    "nonexistent component", "log argument = 0", or an impossible series inverse. With the reduction
    order -- which is 2 at every one of them -- all 148 build.
    """
    P = pari()
    try:
        Q = P(f"Mod(1,{p})*[{x_red}, 0]")
        if not int(P(f"ellisoncurve(ellinit({list(E)},{p}), {Q})")):
            return int(P(f"ellcard(ellinit({list(E)}),{p})"))
        o = int(P(f"ellorder(ellinit({list(E)},{p}), {Q})"))
        return o or int(P(f"ellcard(ellinit({list(E)}),{p})"))
    except Exception:  # noqa: BLE001
        return int(P(f"ellcard(ellinit({list(E)}),{p})"))


def _padic_series_disk_weier(G, gens, p, n, terms, D, x0):
    """rho along a Weierstrass disk, where y vanishes and the x-parametrisation breaks.

    Parametrise by y instead. Since p is a prime of good reduction the sextic is squarefree modulo
    p, so a branch point congruent to x0 is a simple root and lifts by Hensel to x_w in Z_p; then
    y = p t and x solves G(x) = y^2 by Newton, converging t-adically.

    Two things are specific to this disk. At the branch point y = 0, so each quotient image has
    second coordinate zero: it is 2-torsion. Multiplying by the group order therefore sends it to
    the origin and destroys the series, so the multiple must be the image's own reduction order.
    And with that multiple the image's formal parameter and the division polynomial both vanish at
    the branch point, with t-valuations 1 and -1, so neither logarithm exists alone and the two
    must be combined into log(tp/psi) before either is taken.
    """
    from qc_bielliptic import quotients, sigma_series, alpha
    P = pari()
    E1, E2, a0, a2, a4, a6 = quotients(G)
    if x0 % p == 0:
        raise ValueError("branch point also lies in the x = 0 disk")
    gp = " + ".join(f"({c})*X^{k}" for k, c in enumerate(G) if c)
    P(f"xw = {x0} + O({p}^{n})")
    for _ in range(8):
        P(f"xw = xw - subst({gp}, X, xw)/subst(deriv({gp}, X), X, xw)")
    P(f"ys = {p}*t*(1 + O({p}^{n})) + O(t^{D})")
    P(f"xs = xw + O(t^{D})")
    for _ in range(7):
        P(f"xs = xs - (subst({gp}, X, xs) - ys^2)/subst(deriv({gp}, X), X, xs)")
    v1, _ = sigma_series(E1, p, n, terms)
    v2, _ = sigma_series(E2, p, n, terms)
    a_1, a_2 = alpha(E1, gens[0], p, n), alpha(E2, gens[1], p, n)
    inv = pow(x0, p - 2, p)
    ms = (reduction_order(E1, (a6 * x0 * x0) % p, p), reduction_order(E2, (a0 * inv * inv) % p, p))
    parts = []
    for m, E, v, xq, yq in ((ms[0], E1, v1, f"({a6})*xs^2", f"({a6})*ys"),
                            (ms[1], E2, v2, f"({a0})/xs^2", f"({a0})*ys/xs^3")):
        P(f"mQ = ellmul(ellinit({E}), [{xq}, {yq}], {m}); tp = -mQ[1]/mQ[2]")
        P(f"edp = subst(elldivpol(ellinit({E}),{m}), x, {xq}) * (1 + O({p}^{n}))")
        psi = "edp" if m % 2 else f"edp/(2*({yq}))"
        lam = P(f"-(2/{m}^2) * (log(tp/({psi})) + subst(truncate({v}), x, tp))")
        lg = P(f"subst(truncate(ellformallog(ellinit({E}),{terms})), x, tp) / {m}")
        parts.append((lam, lg))
    (l1, g1), (l2, g2) = parts
    return P(f"({l1}) - ({l2}) - 2*log(xs) - ({a_1})*({g1})^2 + ({a_2})*({g2})^2")


def _padic_series_disk_inf(G, gens, p, n, terms, D, w0):
    """rho along the disk at infinity, the mirror of the x = 0 disk under inverting x.

    Set u = 1/x and w = y u^3. Then w^2 is the sextic with its coefficients reversed, the disk is
    u = 0 mod p, and the FIRST quotient map runs into the formal group with parameter S = -u/w while
    the second stays finite at (a0 u^2, a0 w). The explicit -2 log(x) equals 2 log(u) and cancels
    against the first local height, leaving 2 log(w) - 2 v1(S), which is regular.

    This disk is where a point whose x-denominator is divisible by p lives, so without it such a
    point is invisible at that prime: on 48672.181415 the points x = +-1/7 are missed entirely at
    p = 7 and found at 11 and 17. Running several primes covers this in practice, since such a point
    is integral at any other prime, but the disk closes the gap directly.
    """
    from qc_bielliptic import quotients, sigma_series, alpha
    P = pari()
    E1, E2, a0, a2, a4, a6 = quotients(G)
    P(f"us = {p}*t*(1 + O({p}^{n})) + O(t^{D})")
    P(f"ws = sqrt((({a6}) + ({a4})*us^2 + ({a2})*us^4 + ({a0})*us^6) + O({p}^{n}))")
    if int(P(f"Mod(truncate(polcoeff(ws,0)) - {w0}, {p}) == 0")) != 1:
        P("ws = -ws")
    v1, _ = sigma_series(E1, p, n, terms)
    v2, _ = sigma_series(E2, p, n, terms)
    a_1, a_2 = alpha(E1, gens[0], p, n), alpha(E2, gens[1], p, n)
    P("S = -us/ws")
    lg1 = P(f"subst(truncate(ellformallog(ellinit({E1}),{terms})), x, S)")
    v1S = P(f"subst(truncate({v1}), x, S)")
    m2 = int(P(f"ellcard(ellinit({E2}),{p})"))
    P(f"q2 = [({a0})*us^2, ({a0})*ws]")
    P(f"mQ2 = ellmul(ellinit({E2}), q2, {m2}); tp2 = -mQ2[1]/mQ2[2]")
    P(f"edp = subst(elldivpol(ellinit({E2}),{m2}), x, ({a0})*us^2) * (1 + O({p}^{n}))")
    psi2 = "edp" if m2 % 2 else f"edp/(2*(({a0})*ws))"
    lam2 = P(f"-(2/{m2}^2) * (log(tp2/({psi2})) + subst(truncate({v2}), x, tp2))")
    lg2 = P(f"subst(truncate(ellformallog(ellinit({E2}),{terms})), x, tp2) / {m2}")
    return P(f"2*log(ws) - 2*({v1S}) - ({lam2}) - ({a_1})*({lg1})^2 + ({a_2})*({lg2})^2")


def infinity_branches(G, p):
    """The w0 with w0^2 = a6 mod p: one disk at infinity per square root, none if a6 is a non-residue."""
    a6 = G[6] if len(G) > 6 else 0
    return [w for w in range(p) if (w * w - a6) % p == 0]
