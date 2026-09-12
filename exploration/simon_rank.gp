\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

y; w;
read("quartics_clean.gp");
C = vector(3, k, ellfromeqn(y^2 - eval(Str("Q", k - 1))));
Clift = vector(3, k, apply(c -> lift(c), C[k]));
for (k = 1, 3, write("simon_rank.log", "E", k - 1, " Weierstrass coefficients in w: ", Clift[k]));
bnf = bnfinit(y^3 - 2, 1);
write("simon_rank.log", "bnf ready, class number ", bnf.no);
read("simon/qfsolve.gp"); read("simon/resultant3.gp"); read("simon/ellQ.gp"); read("simon/ell.gp");
write("simon_rank.log", "Simon scripts loaded");
DEBUGLEVEL_ell = 1;
for (k = 0, 1, \
  ell = apply(c -> Mod(subst(c, w, y), y^3 - 2), Clift[k + 1]); \
  write("simon_rank.log", "E", k, " over K = ", lift(ell)); \
  r = bnfellrank(bnf, ell); \
  write("simon_rank.log", "E", k, " over K: bnfellrank -> [rank lower bound, 2-Selmer rank, points] = ", lift(r)));
write("simon_rank.log", "done");
