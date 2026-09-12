\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

y; w; aa; bb; cc; CC = vector(2);
read("qcoeffs.gp");
for (k = 0, 1, QC = if (k == 0, QC0, QC1); \
  P = sum(i = 1, 5, Mod(QC[i], w^3 - 2) * x^(i - 1)); \
  c = apply(e -> lift(e), ellfromeqn(y^2 - P)); \
  write("simon_e1.log", "E", k, " Weierstrass (w): ", c); \
  CC[k + 1] = c);
bnf = bnfinit(y^3 - 2, 1);
read("simon/qfsolve.gp"); read("simon/resultant3.gp"); read("simon/ellQ.gp"); read("simon/ell.gp");
DEBUGLEVEL_ell = 0;
ell1 = apply(c -> Mod(subst(c, w, y), y^3 - 2), CC[2]);
r1 = bnfellrank(bnf, ell1);
write("simon_e1.log", "E1 over K: [rank lower bound, 2-Selmer rank, #points] = ", [r1[1], r1[2], #r1[3]]);
write("simon_e1.log", "done");
