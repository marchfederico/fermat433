\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ All primitive solutions of z^3 + 2 y^3 = -x^4 with 1 <= x <= N, by solving the Thue equation for each x.
tnf = thueinit(x^3 + 2, 1);
N = 3000;
t0 = getwalltime();
for (X = 1, N, \
  S = thue(tnf, -X^4); \
  for (i = 1, #S, z = S[i][1]; y = S[i][2]; \
    if (gcd(gcd(X, y), z) == 1, print("solution: x=", X, " y=", y, " z=", z))); \
  if (X % 250 == 0, print("checked x <= ", X, "  [", (getwalltime() - t0) \ 1000, " s]")));
print("done");
