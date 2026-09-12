\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

default(realprecision, 60);
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
{
forprime (p = 5, 2500,
  my(cp = hyperellcharpoly(Mod(f1, p)), R = polroots(cp), tr = 0, cnt = 0, r3, sym);
  for (i = 1, 4, for (j = i + 1, 4, my(z = R[i]*R[j]/p); if (abs(z^48 - 1) < 1e-30, cnt++; tr += z)));
  r3 = polrootsmod(x^3 - 2, p);
  sym = vector(#r3, i, kronecker(lift(-1 - r3[i]), p));
  write("nschar.log", p, " ", p % 8, " ", p % 3, " ", #r3, " ", vecsort(sym), " ", issquare(cp), " ", round(real(tr)), " ", cnt, " ", round(imag(tr)*1e6)));
}
write("nschar.log", "done");
\q
