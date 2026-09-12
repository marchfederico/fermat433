\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

tocl(J) = [8*J[1], 4*J[1]^2 - 96*J[2], 8*J[1]^3 - 160*J[1]*J[2] - 576*J[3], 4096*J[5]];
f0 = x^6 - 40*x^3 - 32;
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
print("TEST ", tocl(genus2igusa([-1, x^3 + 1])));
print("TEST2 ", tocl(genus2igusa([x^6 - 3*x^4 + 3*x^2 - 1, 1])));
C = [[0, 1, f0], [0, -2, -2*f0], [1, 1, f1], [1, -2, -2*f1]];
for (i = 1, 4, print("CURVE ", C[i][1], " ", C[i][2], " ", tocl(genus2igusa(C[i][3]))));
