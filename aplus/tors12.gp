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
w = varlower("w"); Kpol = subst(polredbest(polcompositum(x^6 + 2, x^2 + 3)[1]), x, w); K = nfinit(Kpol);
print("K' = Q[w]/(", Kpol, "), degree ", poldegree(Kpol));
r6 = nfroots(K, x^6 + 2); s3 = nfroots(K, x^2 + 3); print(#r6, " sixth roots of -2 and ", #s3, " square roots of -3 in K'");
W = Mod(subst(r6[1], x, w), Kpol); S = Mod(subst(s3[1], x, w), Kpol);
th = -W^2; nu = -W^3; if (th^3 != 2 || nu^2 != -2 || S^2 != -3, error("generators"));
z3 = (-1 + S)/2; if (z3^3 != 1 || z3 == 1, error("z3"));
c = -2*th^2; xp = th*nu; xm = -xp;
A = 160*W^3 - 64; B = -480*W^3 - 960; C = 480*W^3 - 960; D = -160*W^3 - 64;   \\ note nu = -W^3, so these are the M-coefficients in terms of W
F0 = A*x^6 + B*x^4 + C*x^2 + D;
f = x^6 - 40*x^3 - 32;
\\ consistency: F0(X) must equal (1-X)^6 f(xp(1+X)/(1-X))
if (F0 != sum(i = 0, 6, polcoef(f, i) * xp^i * (1 + x)^i * (1 - x)^(6 - i)), error("model"));
E1 = ellinit([0, B, 0, A*C, A^2*D], K); E2 = ellinit([0, C, 0, B*D, A*D^2], K);
phi1(XX, YY) = [A*XX^2, A*YY];
phi2(XX, YY) = [D/XX^2, D*YY/XX^3];
biel(xv, yv) = my(XX = (xv - xp)/(xv - xm)); [XX, yv*(1 - XX)^3];
Pinf = [Mod(1, Kpol), 8*c*xp]; Q1inf = phi1(Pinf[1], Pinf[2]); Q2inf = phi2(Pinf[1], Pinf[2]);
{
for (k = 0, 2, foreach ([[z3^k*th, 6*S], [z3^k*th, -6*S], [-2*z3^k*th, 12*nu*S], [-2*z3^k*th, -12*nu*S]], P,
  if (P[2]^2 != subst(f, x, P[1]), error("not on A+"));
  my(b = biel(P[1], P[2]), d1 = elladd(E1, phi1(b[1], b[2]), ellneg(E1, Q1inf)), d2 = elladd(E2, phi2(b[1], b[2]), ellneg(E2, Q2inf)));
  print("x = ", if (k, Str("z3^", k, "*"), ""), if (P[1] == z3^k*th, "cbrt2", "-2*cbrt2"), ", y = ", if (P[2] == 6*S || P[2] == 12*nu*S, "+", "-"), if (abs(polcoef(lift(P[2]), 0)) >= 0, if (P[2]^2 == -108, "6*sqrt(-3)", "12*sqrt(6)")), ":  order of [z - inf+] on E1 = ", ellorder(E1, d1), ", on E2 = ", ellorder(E2, d2))));
}
\q
