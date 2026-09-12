\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Does Jac(H) split over F = Q(sqrt(-2))?  Test: at primes split in F the Frobenius quartic must factor over Z
\\ as (T^2 - aT + p)(T^2 - bT + p); at inert primes the trace must vanish.  Also reduction types at 2 and 3.
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
f0 = x^6 - 40*x^3 - 32;
{
test(P, name) =
  my(R = genus2red(P), N = R[1], D = hyperelldisc(P), ok = 0, bad = List(), inert_ok = 0, inert_bad = List(), ab = List());
  print(name, ": conductor ", N, " = ", factor(N)[,1]~, "^", factor(N)[,2]~, "   disc = ", factor(abs(D))[,1]~, "^", factor(abs(D))[,2]~);
  print("   local data: ", R[4]);
  forprime (p = 5, 1500, if (N % p == 0, next);
    my(cp = hyperellcharpoly(Mod(P, p)), fa = factor(cp));
    if (kronecker(-2, p) == 1,
      my(good = #fa[,1] >= 2 && vecmax(vector(#fa[,1], i, poldegree(fa[i,1]))) <= 2 && vecmin(vector(#fa[,1], i, polcoef(fa[i,1], 0))) == p && vecmax(vector(#fa[,1], i, polcoef(fa[i,1], 0))) == p);
      if (good, ok++; if (#ab < 6, listput(ab, [p, vector(#fa[,1], i, -polcoef(fa[i,1], 1))])), listput(bad, [p, cp])),
      if (polcoef(cp, 3) == 0, inert_ok++, listput(inert_bad, [p, cp]))));
  print("   split primes: ", ok, " factor as (T^2-aT+p)(T^2-bT+p), failures: ", #bad, "  ", if (#bad, bad[1], ""));
  print("   sample (p, [a, b]): ", Vec(ab));
  print("   inert primes with trace 0: ", inert_ok, ", failures: ", #inert_bad, "  ", if (#inert_bad, inert_bad[1], ""));
}
test(f1, "B- : y^2 = -C3");
test(-2*f1, "C+ : y^2 = 2C3");
test(f0, "A+ : y^2 = x^6-40x^3-32");
test(-2*f0, "A(-2)");
