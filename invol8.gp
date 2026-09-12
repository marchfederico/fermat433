\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

default(realprecision, 100);
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
g = sum(k = 0, 6, polcoef(f1, k) * (-x + B)^k * (C*x + 1)^(6 - k));
E = vector(6, k, polcoef(g, k - 1, x) * polcoef(f1, 6) - polcoef(g, 6, x) * polcoef(f1, k - 1));
h6 = 81*t^6 - 540*t^5 + 1494*t^4 - 2240*t^3 + 1980*t^2 - 1008*t + 232;
issq(K, a) = #nffactor(K, x^2 - lift(a))[,1] == 2;
{
my(v = polredbest(h6, 1), P6 = v[1], ab = v[2], K = nfinit(P6));
my(Eb = vector(6, k, subst(E[k], B, ab)), gc = gcd(Eb[1], Eb[2]));
my(c0 = -polcoef(gc, 0, C) / polcoef(gc, 1, C), kap = 1 + ab*c0);
my(w = rnfequation(K, x^2 - lift(kap)), PL = polredbest(subst(w, x, t)), nfL = nfinit(PL));
print("L = ", PL, "   signature ", nfL.sign, "   disc ", factor(abs(nfL.disc)));
my(r6 = nfroots(nfL, subst(P6, t, x))); print("roots of P6 in L: ", #r6);
my(tK = Mod(subst(lift(r6[1]), x, t), PL), bL = subst(lift(ab), t, tK), cL = subst(lift(c0), t, tK), kapL = 1 + bL*cL);
my(rs = nfroots(nfL, x^2 - lift(kapL))); print("sqrt(1+bc) in L: ", #rs);
my(s = Mod(subst(lift(rs[1]), x, t), PL)); print("check s^2 = 1+bc: ", s^2 == kapL);
my(thL = Mod(subst(lift(nfroots(nfL, x^3 - 2)[1]), x, t), PL), epsL = thL - 1);
print("L contains: sqrt(-2)? ", #nfroots(nfL, x^2 + 2) > 0, "  i? ", #nfroots(nfL, x^2 + 1) > 0, "  sqrt(-3)? ", #nfroots(nfL, x^2 + 3) > 0, "  sqrt(2)? ", #nfroots(nfL, x^2 - 2) > 0, "  sqrt(-1-theta)? ", #nfroots(nfL, x^2 + 1 + lift(thL)) > 0, "  sqrt(1+theta)? ", #nfroots(nfL, x^2 - 1 - lift(thL)) > 0, "  sqrt(-eps)? ", #nfroots(nfL, x^2 + lift(epsL)) > 0, "  sqrt(theta)? ", #nfroots(nfL, x^2 - lift(thL)) > 0, "  sqrt(-theta)? ", #nfroots(nfL, x^2 + lift(thL)) > 0, "  sqrt(3)? ", #nfroots(nfL, x^2 - 3) > 0);
my(xp = (-1 + s)/cL, xm = (-1 - s)/cL, F = sum(k = 0, 6, polcoef(f1, k) * (xm*x - xp)^k * (x - 1)^(6 - k)));
print("F even in X: ", polcoef(F, 5, x) == 0 && polcoef(F, 3, x) == 0 && polcoef(F, 1, x) == 0);
my(A = polcoef(F, 6, x), Bq = polcoef(F, 4, x), Cq = polcoef(F, 2, x), D = polcoef(F, 0, x));
my(E1 = ellinit([0, Bq, 0, A*Cq, A^2*D], nfL), E2 = ellinit(ellfromeqn(y^2 - x*(A*x^3 + Bq*x^2 + Cq*x + D)), nfL));
print("j(E_tau) = ", lift(E1.j), "    j(E_iota.tau) = ", lift(E2.j));
my(E0 = ellinit([0, 4, 0, 2, 0]), d1 = E1.c6 * E0.c4 / (E0.c6 * E1.c4), d2 = E2.c6 * E0.c4 / (E0.c6 * E2.c4));
print("twist class d1 = E_tau / E0: norm ", factor(abs(norm(d1))), " sign ", sign(norm(d1)), "    d1/d2 square? ", issq(nfL, d1/d2), "   d1*d2 square? ", issq(nfL, d1*d2));
print("d1 in K6 (fixed by s -> -s)? ", subst(lift(d1), t, lift(tK)) == subst(lift(d1), t, lift(tK)));
foreach ([1, -1, 2, -2, 3, -3, 6, -6], q, foreach ([1, epsL, 1 + thL, epsL*(1 + thL), thL, thL*epsL, thL*(1+thL), s, s*epsL, s*(1+thL), s*thL, s*epsL*(1+thL)], u,
  if (issq(nfL, d1*q*u), print("   d1 ~ ", q, " * [", lift(u), "]  mod squares"))));
print("is 1+bc a unit times a power of 2,3? ideal factorization: ", idealfactor(nfL, kapL)[,2]~, "  over primes with (p,e,f): ", apply(pr -> [pr.p, pr.e, pr.f], idealfactor(nfL, kapL)[,1]));
}
\q
