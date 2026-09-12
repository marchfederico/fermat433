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

"""qc_local.py -- the local p-adic height contributions away from p.

The canonical cyclotomic p-adic height of a rational point is the sum of local terms over all
places. qc_sigma.py computes the one at p from the sigma function. Every other place contributes a
rational multiple of log_p(v), determined by which component of the Neron model at v the point
reduces onto, so the total away-from-p contribution ranges over an explicit finite set. Quadratic
Chabauty needs exactly that set.

The values below are the classical Neron correction terms in the normalisation PARI uses (twice
Silverman's). They were not taken on faith: away_table.json was built by computing, for 227 rank-1
curves over a range of multiples of the generator, the difference between the canonical height
(ellpadicheight * [1,-s2]~) and the local height at p, and recovering the rational coefficients by
p-adic lindep against the logarithms of the bad primes. Every one of the 167 non-zero residuals was
reconstructed and checked back against the residual. The observed values agree with this table, and
validate() re-runs that comparison.

Being conservative here is safe: a superset of the true value set can only admit extra candidate
zeros in the quadratic Chabauty equation, never discard a rational point.
"""
from __future__ import annotations

import re
from fractions import Fraction as Fr

_IN = re.compile(r"^I_(\d+)$")
_INSTAR = re.compile(r"^I_(\d+)\*$")


def lambda_values(kodaira, c_v=None, split=None):
    """Possible values of |lambda_v| / log_p(v) at a place of bad reduction, on a MINIMAL model.

    This is Bianchi Table 1 (arXiv:1904.04622), itself the p-adic form of Cremona-Prickett-Siksek
    Table 2, and it agrees with the values recovered independently here by lindep over 227 rank-1
    curves (see validate()). Magnitudes are returned; the sign convention is fixed by the caller.

    kodaira: "I_0", "II", "III", "IV", "I_0*", "I_n", "I_n*", "IV*", "III*", "II*".
    c_v:     the Tamagawa number, which selects the row for I_n and I_n*.
    split:   for I_n, whether the multiplicative reduction is split. When None it is inferred
             (c_v == n means split) and, if still ambiguous, the union of both rows is returned,
             which is a superset and therefore sound.
    """
    zero = [Fr(0)]
    if c_v == 1:
        return zero                                   # only the identity component is rational
    if kodaira in ("I_0", "I_1", "II", "II*"):
        return zero                                   # trivial component group
    if kodaira == "III":
        vals = {Fr(1, 2)}
    elif kodaira == "III*":
        vals = {Fr(3, 2)}
    elif kodaira == "IV":
        vals = {Fr(2, 3)}
    elif kodaira == "IV*":
        vals = {Fr(4, 3)}
    elif kodaira == "I_0*":
        vals = {Fr(1)}
    elif _INSTAR.match(kodaira):
        n = int(_INSTAR.match(kodaira).group(1))
        if n == 0:
            vals = {Fr(1)}
        elif c_v == 4:
            vals = {Fr(1), Fr(n + 4, 4)}
        elif c_v == 2:
            vals = {Fr(1)}
        else:
            vals = {Fr(1), Fr(n + 4, 4)}
    elif _IN.match(kodaira):
        n = int(_IN.match(kodaira).group(1))
        sp = split if split is not None else (c_v == n if c_v is not None else None)
        chain = {Fr(i * (n - i), n) for i in range(1, n // 2 + 1)}
        if sp is True:
            vals = chain
        elif sp is False:
            vals = {Fr(n, 4)}
        else:
            vals = chain | {Fr(n, 4)}                 # ambiguous: take the union, a sound superset
    else:
        raise ValueError(f"unknown Kodaira type {kodaira!r}")
    return sorted({Fr(0)} | vals)


def non_minimal_shift(ord_delta_quotient, q):
    """Bianchi eq. (4): on a non-minimal model lambda_v = lambda_v^min + (1/6) log|Delta/Delta^min|_v,
    and the value set gains {2k log q : 1 <= k <= ord_q(delta)/12}. Returns (shift, extra) as
    coefficients of log(q), with delta = Delta/Delta^min and ord_delta_quotient = ord_q(delta).

    This is the term whose absence made a short-model experiment here produce meaningless fits:
    Y^2 = X^3 - 27 c4 X - 54 c6 is wildly non-minimal, so its local heights are shifted at 2 and 3.
    """
    shift = Fr(-ord_delta_quotient, 6)
    extra = [Fr(2 * k) for k in range(1, ord_delta_quotient // 12 + 1)]
    return shift, extra


def away_value_set(bad_data):
    """All possible totals of sum_(v != p) lambda_v, as {rational coefficient per bad prime}.

    bad_data: [{"v": prime, "kodaira": type, "c_v": Tamagawa}, ...].
    Returns a list of dicts {prime: coefficient}; the caller multiplies each by log_p(v) and sums.
    """
    out = [{}]
    for e in bad_data:
        vals = lambda_values(e["kodaira"], e.get("c_v"))
        nxt = []
        for acc in out:
            for val in vals:
                d = dict(acc)
                if val:
                    d[e["v"]] = val
                nxt.append(d)
        out = nxt
    seen, uniq = set(), []
    for d in out:
        key = tuple(sorted(d.items()))
        if key not in seen:
            seen.add(key)
            uniq.append(d)
    return uniq


def validate(table_path):
    """Every value observed empirically must lie in the predicted set."""
    import json
    obs = json.load(open(table_path))
    bad = []
    for key, vals in obs.items():
        kod, c_v = eval(key)                                  # noqa: S307  keys are ("I_2", 2) tuples we wrote
        pred = set(lambda_values(kod, c_v))
        for s in vals:
            if Fr(s) not in pred:
                bad.append((kod, c_v, s, sorted(str(x) for x in pred)))
    return bad


if __name__ == "__main__":
    import json
    import os
    import sys
    sp = sys.argv[1] if len(sys.argv) > 1 else "."
    path = os.path.join(sp, "away_table.json")
    print("predicted value sets for the types that occurred:")
    for key in sorted(json.load(open(path))):
        kod, c_v = eval(key)                                  # noqa: S307
        print(f"  {kod:6} c_v={c_v}: {[str(x) for x in lambda_values(kod, c_v)]}")
    bad = validate(path)
    print(f"\nobserved values outside the predicted set: {len(bad)}")
    for b in bad:
        print(f"  MISMATCH {b}")
    ex = [{"v": 2, "kodaira": "IV", "c_v": 3}, {"v": 5, "kodaira": "I_2", "c_v": 2}]
    s = away_value_set(ex)
    print(f"\nexample: bad primes {[e['v'] for e in ex]} types {[e['kodaira'] for e in ex]} "
          f"-> {len(s)} possible away-from-p totals")
    for d in s:
        print(f"  {{{', '.join(f'{k}: {v}' for k, v in d.items()) or 'all zero'}}}")
