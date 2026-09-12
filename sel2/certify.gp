\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

default(parisize, "2G"); default(parisizemax, "8G");
chk(f, S, nm) = { my(c = pollead(f), P = polredbest(c^5 * subst(f, x, y/c)), bnf = bnfinit(P, 1), Sid, su, gens, NC, span);
  print(nm, ": field ", P, "  disc ", factor(bnf.disc), "  class group ", bnf.cyc, "  regulator ", bnf.reg);
  print("   bnfcertify: ", bnfcertify(bnf));
  Sid = concat(apply(p -> idealprimedec(bnf, p), S)); su = bnfsunit(bnf, Sid); gens = concat(concat(bnf.fu, [bnf.tu[2]]), su[1]);
  \\ norm classes of the S-units in Q(S,2), coordinates over {-1} u S
  NC = matrix(1 + #S, #gens, j, i, my(n = nfeltnorm(bnf, gens[i])); if (j == 1, n < 0, valuation(abs(n), S[j-1]) % 2));
  print("   norm classes of the S-unit generators (rows -1, ", S, "): rank ", matrank(Mod(NC, 2)), " of ", 1 + #S);
  foreach ([-1, 2, -2, 3, -3, 17, -17, 34, -34, 6, -6], q, if (q == 17 || q == 34 || q == -17 || q == -34, if (!vecsearch(vecsort(S), 17), next));
    my(v = vectorv(1 + #S, j, if (j == 1, q < 0, valuation(abs(q), S[j-1]) % 2)), sol = matinverseimage(Mod(NC, 2), Mod(v, 2)));
    print("   ", q, " is a norm class of L(S,2): ", #sol > 0)); };
C3 = 17*x^6 - 72*x^5 + 90*x^4 + 40*x^3 - 180*x^2 + 144*x - 40; A = x^6 - 40*x^3 - 32;
chk(A, [2, 3], "L_A (curves A+-)");
chk(-C3, [2, 3, 17], "L_6 (curves B+-, C+-)");
\q
