\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

f0 = x^6 - 40*x^3 - 32;
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
say(s) = write("g2data.log", s);
{
for (k = 0, 1, my(f = if (k == 0, f0, f1));
  foreach ([1, -1, 2, -2, 3, -3, 6, -6], lam,
    my(P = lam*f, R, pts, split = 1, fac);
    pts = hyperellratpoints(P, 300);
    if (lam != 1 && lam != -2, say(Str("k=", k, " lambda=", lam, ": rational points up to height 300: ", #pts)); next);
    R = genus2red(P);
    say(Str("k=", k, " lambda=", lam, ": conductor ", R[1], "  points (height<=300): ", #pts, "  e.g. ", pts[1..min(6, #pts)]));
    forprime (q = 5, 150, if (R[1] % q == 0, next);
      fac = factor(hyperellcharpoly(Mod(P, q)))[, 1];
      if (#fac == 1 || vecmax(apply(poldegree, fac)) > 2, split = 0));
    say(Str("   Frobenius polynomials factor into quadratics over Z for all good q < 150: ", split))));
}
say("static data done");
{
for (k = 0, 1, my(f = if (k == 0, f0, f1));
  foreach ([1, -2], lam,
    my(L = lfungenus2(lam*f), r = lfunorderzero(L));
    say(Str("k=", k, " lambda=", lam, ": analytic rank ", r))));
}
say("done");
