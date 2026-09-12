\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

default(parisize, "1G");
w = varlower("w"); Mpol = subst(polredbest(polcompositum(x^3 - 2, x^2 + 2)[1]), x, w); M = nfinit(Mpol);
print("M = Q[w]/(", Mpol, "), disc ", factor(M.disc));
th = Mod(subst(nfroots(M, x^3 - 2)[1], x, w), Mpol); nu = Mod(subst(nfroots(M, x^2 + 2)[1], x, w), Mpol);
if (th^3 != 2 || nu^2 != -2, error("roots"));
c = -2*th^2; xp = th*nu; xm = -xp; if (xp^2 != c, error("fixed points"));
f = x^6 - 40*x^3 - 32;
if (subst(f, x, c/x) * x^6 + 32*f != 0, error("involution"));
F0 = sum(i = 0, 6, polcoef(f, i) * xp^i * (1 + x)^i * (1 - x)^(6 - i));
print("F0 odd coefficients: ", vector(3, i, lift(polcoef(F0, 2*i - 1))));
A = polcoef(F0, 6); B = polcoef(F0, 4); C = polcoef(F0, 2); D = polcoef(F0, 0);
print("A = ", lift(A), "  B = ", lift(B), "  C = ", lift(C), "  D = ", lift(D), "   (nu = ", lift(nu), ")");
E1 = ellinit([0, B, 0, A*C, A^2*D], M); E2 = ellinit([0, C, 0, B*D, A*D^2], M);
print("E1 conductor norm: ", factor(idealnorm(M, ellglobalred(E1)[1]))); print("E2 conductor norm: ", factor(idealnorm(M, ellglobalred(E2)[1])));
print("j(E1) = ", lift(E1.j), "   j(E2) = ", lift(E2.j));
phi1(XX, YY) = [A*XX^2, A*YY];
phi2(XX, YY) = [D/XX^2, D*YY/XX^3];
foreach ([3, -3], yv, my(xv = -1, XX = (xv - xp)/(xv - xm), YY = yv*(1 - XX)^3); if (YY^2 != subst(F0, x, XX), error("model")); listput(pts, [XX, YY, Str("(-1,", yv, ")")]));
foreach ([1, -1], sg, my(XX = Mod(1, Mpol), YY = sg*8*c*xp); if (YY^2 != subst(F0, x, XX), error("model at infinity")); listput(pts, [XX, YY, Str("inf", sg)]));
foreach (pts, P, my(Q1 = phi1(P[1], P[2]), Q2 = phi2(P[1], P[2]));
  if (!ellisoncurve(E1, Q1) || !ellisoncurve(E2, Q2), error("not on quotient"));
  print(P[3], ": X = ", lift(P[1]), "; order of phi1 = ", ellorder(E1, Q1), ", of phi2 = ", ellorder(E2, Q2)));
my(P0 = pts[3]); foreach (pts, P, my(d1 = elladd(E1, phi1(P[1], P[2]), ellneg(E1, phi1(P0[1], P0[2]))), d2 = elladd(E2, phi2(P[1], P[2]), ellneg(E2, phi2(P0[1], P0[2]))));
  print("[", P[3], " - inf+]: order on E1 = ", ellorder(E1, d1), "  on E2 = ", ellorder(E2, d2)));
}
print("43 in M: ", apply(pr -> [pr.e, pr.f], idealprimedec(M, 43)), "   f mod 43 roots: ", polrootsmod(f, 43), "   #A+(F_43) via L-poly: ", subst(hyperellcharpoly(Mod(f, 43)), x, 1));
\q
