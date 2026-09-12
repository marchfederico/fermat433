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
{
foreach ([[1, 1], [100, 1], [12, 1], [12, -1], [200, 1], [300, -1]], dk, my(x0 = dk[1], sg = dk[2], fx = Mod(subst(f1, x, x0), p));
  if (fx == 0 || !issquare(fx), print("x0=", x0, ": no points"); next);
  my(R = rhoser2(x0, sg, 0), S = R[1], st = strassman(S), pol = sum(k = 0, D - 1, truncate(polcoef(S, k, T)) * T^k), rts0 = polrootspadic(pol, p, 16), keep = List());
  for (j = 1, #rts0, if (valuation(rts0[j], p) >= 0, listput(keep, rts0[j] + O(p^8))));
  print("disk x0=", x0, " sg=", sg, ": Strassman ", st[1], " vals ", st[3], "  Z_p-roots: ", Vec(keep)));
}
\q
