\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
{
foreach ([499, 1459, 1579, 1723, 1753, 433, 457, 41, 11], p,
  my(cp = hyperellcharpoly(Mod(f1, p)));
  print(p, " mod 8 = ", p % 8, ": ", cp, "   factor/Q: ", factor(cp)[,1]~, "   factor over Q(sqrt-2): ", nffactor(nfinit(y^2 + 2), cp)[,1]~));
}
\q
