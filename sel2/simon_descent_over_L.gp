\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

default(parisize, "4G"); default(realprecision, 60);
TW = 0;   \\ 0: y^2 = -C3(x);  1: the -2-twist y^2 = 2 C3(x)
f1 = if (TW == 0, 1, -2) * (-17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40);
g = sum(k = 0, 6, polcoef(f1, k) * (-x + B)^k * (C*x + 1)^(6 - k));
E = vector(6, k, polcoef(g, k - 1, x) * polcoef(f1, 6) - polcoef(g, 6, x) * polcoef(f1, k - 1));
h6 = 81*t^6 - 540*t^5 + 1494*t^4 - 2240*t^3 + 1980*t^2 - 1008*t + 232;
{
my(vv = polredbest(h6, 1), P6 = vv[1], ab = vv[2], K = nfinit(P6));
my(Eb = vector(6, k, subst(E[k], B, ab)), gc = gcd(Eb[1], Eb[2]));
my(c0 = -polcoef(gc, 0, C) / polcoef(gc, 1, C), kap = 1 + ab*c0);
my(w = rnfequation(K, x^2 - lift(kap)), PL = polredbest(subst(w, x, t)));
bnf = bnfinit(PL, 1);
my(r6 = nfroots(bnf, subst(P6, t, x)), tK = Mod(subst(lift(r6[1]), x, t), PL));
my(bL = subst(lift(ab), t, tK), cL = subst(lift(c0), t, tK), kapL = 1 + bL*cL);
my(sL = Mod(subst(lift(nfroots(bnf, x^2 - lift(kapL))[1]), x, t), PL), xp = (-1 + sL)/cL, xm = (-1 - sL)/cL);
my(F = sum(k = 0, 6, polcoef(f1, k) * (xm*x - xp)^k * (x - 1)^(6 - k)));
my(A = polcoef(F, 6, x), Bq = polcoef(F, 4, x), Cq = polcoef(F, 2, x), Dq = polcoef(F, 0, x));
my(E1 = ellinit([0, Bq, 0, A*Cq, A^2*Dq], bnf), E1m = ellminimalmodel(E1));
ell_t = lift([E1m.a1, E1m.a2, E1m.a3, E1m.a4, E1m.a6]);
PLy = subst(PL, t, y);
write("descent_iso_0.log", "twist=", TW, "  L = ", PLy); write("descent_iso_0.log", "E1 minimal model over L: ", ell_t);
}
bnfy = bnfinit(PLy, 1);
\\ put the curve in the form y^2 = x^3 + a x^2 + b x with a, b integral (2-torsion point at the origin)
ellb = [0, (4*subst(ell_t[2], t, y) + subst(ell_t[1], t, y)^2)/4, 0, (2*subst(ell_t[4], t, y) + subst(ell_t[1], t, y)*subst(ell_t[3], t, y))/2, (4*subst(ell_t[6-1], t, y) + subst(ell_t[3], t, y)^2)/4];
ellb = apply(c -> Mod(c, PLy), ellb);
xT = nfroots(bnfy, x^3 + lift(ellb[2])*x^2 + lift(ellb[4])*x + lift(ellb[5]))[1]; xT = Mod(lift(xT), PLy);
aa = 3*xT + ellb[2]; bb = 3*xT^2 + 2*ellb[2]*xT + ellb[4];
dd = 1; while (denominator(nfalgtobasis(bnfy, aa*dd^2)) > 1 || denominator(nfalgtobasis(bnfy, bb*dd^4)) > 1, dd *= 2);
elli = [0, aa*dd^2, 0, bb*dd^4, 0];
write("descent_iso_0.log", "scaling d = ", dd, "  curve [0,a,0,b,0] with a, b integral: ", elli);
print("prepared: ", dd);
elly = apply(c -> Mod(subst(c, t, y), PLy), ell_t);
read("simon/qfsolve.gp"); read("simon/resultant3.gp"); read("simon/ellQ.gp"); read("simon/ell.gp");
DEBUGLEVEL_ell = 3; LIMTRIV = 0; LIM1 = 0; LIM3 = 0;   \\ no point searches in the degree-12 field: only the Selmer bound is needed
write("descent_iso_0.log", "torsion: ", elltors(ellinit(elly, bnfy))[1]);
gettime();
r = bnfell2descent_viaisog(bnfy, elli);
write("descent_iso_0.log", "bnfellrank: [rank lower bound, 2-Selmer bound, #points] = ", [r[1], r[2], #r[3]], "   time ", gettime()/1000, " s");
write("descent_iso_0.log", "points: ", r[3]);
write("descent_iso_0.log", "done");
\q
