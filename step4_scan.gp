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
\\ degree-1 primes q-bar of L above q: roots of PL mod q; E1 (b-model, minimal at odd primes) and E2 reduced there.
redmodel(ai, r, q) = vector(5, k, Mod(subst(lift(ai[k]), t, r), q));
{
my(PLm = bnf.pol, out = List(), sat = List(), cnt = 0);
forprime (q = 5, 300000, if (q == 499, next);
  my(rs = polrootsmod(subst(PLm, t, x), q)); if (#rs == 0, next);
  for (j = 1, #rs, my(r = lift(rs[j]), E1q = ellinit(redmodel(ai1, r, q)), E2q = ellinit(redmodel(ai2, r, q)), N1, N2);
    if (E1q == [] || E2q == [], next);   \\ bad reduction of the model (should only happen at 2, 3)
    N1 = ellcard(E1q); N2 = ellcard(E2q); cnt++;
    if (N1 % 499 == 0 || N2 % 499 == 0, listput(out, [q, r, N1, ellgroup(E1q), N2, ellgroup(E2q)]));
    if (cnt <= 4000, my(g1 = ellgroup(E1q)); if (#g1 == 2 && g1[2] % 2 == 0 && #sat < 60, listput(sat, [q, r, g1])))));
print("degree-1 primes scanned: ", cnt);
print("primes with 499 | #E1 or #E2: ", #out);
for (i = 1, #out, print("   ", out[i]));
print("primes with full 2-torsion in E1 (for saturation tests), first few: ", vector(min(12, #sat), i, sat[i]));
write("step4_scan.txt", Vec(out)); write("step4_scan_sat.txt", Vec(sat));
}
\q
