\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

f0 = x^6 - 40*x^3 - 32;
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
say(s) = write("g2struct.log", s);
{
for (k = 0, 1, my(f = if (k == 0, f0, f1));
  foreach ([1, -2], lam,
    my(P = lam*f, R = genus2red(P), mm = R[3], S, cores = List(), tb = 0, Lf, feq, lval);
    S = if (type(mm) == "t_VEC", 4*mm[1] + mm[2]^2, 4*mm);
    say(Str("k=", k, " lambda=", lam, ": genus2red conductor ", R[1], "  minimal model ", mm, "  |disc(4P+Q^2)|/2^12 = ", abs(poldisc(S))/2^12));
    say(Str("   Igusa-Clebsch invariants: ", genus2igusa(P)));
    forprime (q = 5, 300, if (R[1] % q == 0, next);
      my(cp = hyperellcharpoly(Mod(P, q)), c1 = polcoef(cp, 3), c2 = polcoef(cp, 2), D = c1^2 - 4*(c2 - 2*q));
      listput(cores, if (D == 0, 0, core(D)));
      tb = gcd(tb, subst(cp, 'x, 1)));
    say(Str("   squarefree parts of Frobenius discriminants (RM test): ", Set(cores)));
    say(Str("   torsion bound gcd #J(F_q) = ", tb));
    Lf = lfungenus2(P);
    feq = lfuncheckfeq(Lf);
    lval = lfun(Lf, 1);
    say(Str("   functional-equation check (log10 error): ", feq, "   L(J,1) = ", lval))));
}
say("done");
