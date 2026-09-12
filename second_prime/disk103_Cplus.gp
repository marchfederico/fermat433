\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

default(parisize, "2G");
read("step3_setup.gp");
n = 22; D = 22;            \\ higher p-adic and T precision for this disk
read("step3_disk.gp");
{
foreach ([1, -1], sg, my(R = rhoser2(103, sg, 0), S = R[1], st = strassman(S));
  print("x0=103 sg=", sg, ": strassman ", st[1], " minval ", st[2], " vals ", st[3]);
  print("   T-precision of rho: ", serprec(S, T), "   of lg1: ", serprec(R[2], T), "  of lg2: ", serprec(R[3], T));
  my(pol = sum(k = 0, D - 1, truncate(polcoef(S, k, T)) * T^k), rts0 = polrootspadic(pol, p, 12));
  print("   Z_p roots: ", [lift(r + O(p^6)) | r <- rts0, valuation(r, p) >= 0]));
\\ diagnose: images of the centre point at place 1 and the order of phi1(z0), phi2(z0) modulo p^k
my(x0 = 103, y0 = sqrt(subst(f1, x, x0) + O(p^n)), i = 1, X = (x0 - xpi[i])/(x0 - xmi[i]), Y = y0*(X - 1)^3, Q1 = bnat1(i, X, Y), Q2 = bnat2(i, X, Y));
print("centre: phi1(z0) = ", Q1, "\n        phi2(z0) = ", Q2);
foreach ([2, 3, 4, 6, 8, 12], k, print("   k = ", k, ": k*phi1(z0) = ", ellmul(Et1[i], Q1, k), "   k*phi2(z0) = ", ellmul(Et2[i], Q2, k)));
}
\q
