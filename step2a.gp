\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Step 2a: bielliptic model over L, elliptic quotients on global minimal models, images of the generators.
default(parisize, "1G");
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
g = sum(k = 0, 6, polcoef(f1, k) * (-x + B)^k * (C*x + 1)^(6 - k));
E = vector(6, k, polcoef(g, k - 1, x) * polcoef(f1, 6) - polcoef(g, 6, x) * polcoef(f1, k - 1));
pf(a) = apply(pr -> [pr.p, pr.e, pr.f], idealfactor(nfL, a)[,1]);
den(EE, Q) = my(fa = idealfactor(nfL, idealinv(nfL, idealadd(nfL, 1, Q[1])))); [apply(pr -> [pr.p, pr.e, pr.f], fa[,1]), fa[,2]~];
h6 = 81*t^6 - 540*t^5 + 1494*t^4 - 2240*t^3 + 1980*t^2 - 1008*t + 232;
{
my(v = polredbest(h6, 1), P6 = v[1], ab = v[2], K = nfinit(P6));
my(Eb = vector(6, k, subst(E[k], B, ab)), gc = gcd(Eb[1], Eb[2]));
my(c0 = -polcoef(gc, 0, C) / polcoef(gc, 1, C), kap = 1 + ab*c0);
my(w = rnfequation(K, x^2 - lift(kap)), PL = polredbest(subst(w, x, t)));
nfL = bnfinit(PL, 1);
my(r6 = nfroots(nfL, subst(P6, t, x)), tK = Mod(subst(lift(r6[1]), x, t), PL));
bL = subst(lift(ab), t, tK); cL = subst(lift(c0), t, tK); kapL = 1 + bL*cL;
sL = Mod(subst(lift(nfroots(nfL, x^2 - lift(kapL))[1]), x, t), PL);
xp = (-1 + sL)/cL; xm = (-1 - sL)/cL;
print("b, c are {2,3}-units: ", apply(a -> vecsort(apply(pr -> pr.p, idealfactor(nfL, a)[,1])), [bL, cL]));
\\ the even model: X = (x - xp)/(x - xm), Y = y (X-1)^3,  Y^2 = F(X)
F = sum(k = 0, 6, polcoef(f1, k) * (xm*x - xp)^k * (x - 1)^(6 - k));
A = polcoef(F, 6, x); Bq = polcoef(F, 4, x); Cq = polcoef(F, 2, x); D = polcoef(F, 0, x);
print("F even: ", polcoef(F,5,x) == 0 && polcoef(F,3,x) == 0 && polcoef(F,1,x) == 0, "   A = f1(xm): ", A == subst(f1, x, xm), "   D = f1(xp): ", D == subst(f1, x, xp));
print("primes of A: ", pf(A), " exponents ", idealfactor(nfL, A)[,2]~);
print("primes of D: ", pf(D), " exponents ", idealfactor(nfL, D)[,2]~);
\\ quotients E1: Y'^2 = X'^3 + B X'^2 + A C X' + A^2 D,  phi1 = (A X^2, A Y);   E2: Y'^2 = X'^3 + C X'^2 + B D X' + A D^2,  phi2 = (D/X^2, D Y/X^3)
E1 = ellinit([0, Bq, 0, A*Cq, A^2*D], nfL); E2 = ellinit([0, Cq, 0, Bq*D, A*D^2], nfL);
print("j(E1), j(E2) = ", lift(E1.j), ", ", lift(E2.j));
print("disc(E1) primes: ", pf(E1.disc), "  exps ", idealfactor(nfL, E1.disc)[,2]~);
print("disc(E2) primes: ", pf(E2.disc), "  exps ", idealfactor(nfL, E2.disc)[,2]~);
\\ global minimal models
E1m = ellminimalmodel(E1, &v1); E2m = ellminimalmodel(E2, &v2);
print("E1 minimal model a-invariants: ", lift([E1m.a1, E1m.a2, E1m.a3, E1m.a4, E1m.a6]));
print("E2 minimal model a-invariants: ", lift([E2m.a1, E2m.a2, E2m.a3, E2m.a4, E2m.a6]));
print("minimal disc E1 primes: ", pf(E1m.disc), " exps ", idealfactor(nfL, E1m.disc)[,2]~, "   E2: ", pf(E2m.disc), " exps ", idealfactor(nfL, E2m.disc)[,2]~);
print("torsion E1(L): ", elltors(E1m)[1], "   E2(L): ", elltors(E2m)[1]);
\\ images of the generators P1 = (1, 1), P2 = (-1, 15)
pts = [[1, 1], [-1, 15]];
Q1 = vector(2); Q2 = vector(2);
for (i = 1, 2, my(x0 = pts[i][1], y0 = pts[i][2], X = (x0 - xp)/(x0 - xm), Y = y0*(X - 1)^3);
  print("P", i, ": Y^2 = F(X): ", Y^2 == subst(F, x, X));
  Q1[i] = ellchangepoint([A*X^2, A*Y], v1); Q2[i] = ellchangepoint([D/X^2, D*Y/X^3], v2);
  print("   phi1(P", i, ") on E1m: ", ellisoncurve(E1m, Q1[i]), "   phi2(P", i, ") on E2m: ", ellisoncurve(E2m, Q2[i])));
S1 = elladd(E1m, Q1[1], Q1[2]); M1 = ellsub(E1m, Q1[1], Q1[2]); T1 = ellmul(E1m, Q1[1], 2);
S2 = elladd(E2m, Q2[1], Q2[2]); M2 = ellsub(E2m, Q2[1], Q2[2]); T2 = ellmul(E2m, Q2[1], 2);
print("denominator ideals of x on E1m: Q1: ", den(E1m, Q1[1]), "  Q2: ", den(E1m, Q1[2]), "  Q1+Q2: ", den(E1m, S1), "  Q1-Q2: ", den(E1m, M1), "  2Q1: ", den(E1m, T1));
print("denominator ideals of x on E2m: Q1': ", den(E2m, Q2[1]), "  Q2': ", den(E2m, Q2[2]), "  Q1'+Q2': ", den(E2m, S2), "  Q1'-Q2': ", den(E2m, M2), "  2Q1': ", den(E2m, T2));
write("step2a_data.gp", "PL = ", PL, ";\nE1m = ", lift([E1m.a1, E1m.a2, E1m.a3, E1m.a4, E1m.a6]), ";\nE2m = ", lift([E2m.a1, E2m.a2, E2m.a3, E2m.a4, E2m.a6]), ";\nQ1 = ", lift(Q1), ";\nQ2 = ", lift(Q2), ";\nxp = ", lift(xp), ";\nxm = ", lift(xm), ";\nA = ", lift(A), ";\nD = ", lift(D), ";\nv1 = ", lift(v1), ";\nv2 = ", lift(v2), ";\nBq = ", lift(Bq), ";\nCq = ", lift(Cq), ";");
}
\q
