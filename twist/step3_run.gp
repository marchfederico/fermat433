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
read("step3_setup.gp"); read("step3_disk.gp"); read(CHUNK);
E_RAT = 6;  \\ algdep threshold exponent: coefficients below 10^E_RAT count as "rational-looking"
analyse(R, x0, sg, tag) = {
  my(S = R[1], st = strassman(S), pol = sum(k = 0, D - 1, truncate(polcoef(S, k, T)) * T^k), rts0, keep = List(), line);
  rts0 = iferr(polrootspadic(pol, p, 12), err, []);
  for (j = 1, #rts0, my(r = rts0[j]); if (valuation(r, p) < 0, next);
    my(l1 = subst(truncate(R[2]), T, r), l2 = subst(truncate(R[3]), T, r), a = Minv * [l1, l2]~,
       d1 = algdep(a[1], 1), d2 = algdep(a[2], 1), rat = vecmax(abs(Vec(d1))) < 10^E_RAT && vecmax(abs(Vec(d2))) < 10^E_RAT);
    listput(keep, [r + O(p^6), a[1] + O(p^5), a[2] + O(p^5), rat, if (rat, [-polcoef(d1,0)/polcoef(d1,1), -polcoef(d2,0)/polcoef(d2,1)], 0)]));
  line = Str(tag, " x0=", x0, " sg=", sg, " strassman=", st[1], " minval=", st[2], " vals=", st[3], " nroots=", #keep, " roots=", Vec(keep));
  write(OUT, line); line; };
{
if (LO == 0, foreach ([1, -1], sg, my(R = iferr(rhoser2(0, sg, 1), err, 0)); if (R == 0, write(OUT, Str("INF sg=", sg, " ERROR ", err)), analyse(R, "inf", sg, "INF"))));
for (x0 = LO, HI, my(fx = Mod(subst(f1, x, x0), p)); if (fx == 0 || !issquare(fx), next);
  foreach ([1, -1], sg, my(R = iferr(rhoser2(x0, sg, 0), err, 0));
    if (R == 0, write(OUT, Str("DISK x0=", x0, " sg=", sg, " ERROR ", err)), analyse(R, x0, sg, "DISK"))));
write(OUT, "done");
}
\q
