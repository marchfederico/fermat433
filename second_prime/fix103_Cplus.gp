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
read("step3_setup.gp"); read("step3_disk.gp");
\\ the two zeros in the disks x0 = 103 (both signs), T to 6 digits from step3_out_0.txt
Ts = [198 + 901*1459 + 857*1459^2 + 500*1459^3 + 244*1459^4 + 705*1459^5 + O(1459^6), 108 + 1128*1459 + 572*1459^2 + 301*1459^3 + 1073*1459^4 + 719*1459^5 + O(1459^6)];
x0 = 103;
print("special at places (phi2->O): ", [i | i <- [1..12], spP[i] == x0], "   (phi1->O): ", [i | i <- [1..12], spM[i] == x0]);
good = [i | i <- [1..12], spP[i] != x0 && spM[i] != x0];
g1 = good[1]; g2 = good[2]; print("using places ", [g1, g2], " for the coefficient vector");
Mlog2 = matrix(2, 2, a, b, logE(Et1[[g1, g2][a]], vector(2, j, ev(pts1[b][j], rts[[g1, g2][a]])), mm[[g1, g2][a]][1], FL1[[g1, g2][a]]));
print("log matrix at the good places: valuation of det = ", valuation(matdet(Mlog2), p));
{
foreach ([1, -1], sg, foreach (Ts, Tv, my(xv = x0 + p*Tv, yv = sg*sqrt(subst(f1, x, xv)), lg = vector(2));
  for (k = 1, 2, my(i = [g1, g2][k], X = (xv - xpi[i])/(xv - xmi[i]), Y = yv*(X - 1)^3, Q1s = bnat1(i, X, Y)); lg[k] = logE(Et1[i], Q1s, mm[i][1], FL1[i]));
  my(a = Mlog2^(-1) * lg~);
  print("sg=", sg, " T=", lift(Tv + O(p^3)), "...: a = ", lift(a[1] + O(p^4)), ", ", lift(a[2] + O(p^4)), "  (valuations ", valuation(a[1], p), ", ", valuation(a[2], p), ")  a mod p = [", lift(a[1] + O(p)), ", ", lift(a[2] + O(p)), "]")));
}
\q
