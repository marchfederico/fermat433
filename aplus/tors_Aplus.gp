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
w = varlower("w"); Mpol = w^6 + 2; M = nfinit(Mpol);
th = Mod(-w^2, Mpol); nu = Mod(-w^3, Mpol); c = -2*th^2; xp = th*nu; xm = -xp;
A = 160*Mod(w,Mpol)^3 - 64; B = -480*Mod(w,Mpol)^3 - 960; C = 480*Mod(w,Mpol)^3 - 960; D = -160*Mod(w,Mpol)^3 - 64;
F0 = A*x^6 + B*x^4 + C*x^2 + D;
E1 = ellinit([0, B, 0, A*C, A^2*D], M); E2 = ellinit([0, C, 0, B*D, A*D^2], M);
phi1(XX, YY) = [A*XX^2, A*YY];
phi2(XX, YY) = [D/XX^2, D*YY/XX^3];
biel(xv, yv) = my(XX = (xv - xp)/(xv - xm)); [XX, yv*(1 - XX)^3];
Pinf = [Mod(1, Mpol), 8*c*xp];
{
foreach ([[0, 4*nu], [0, -4*nu], [2, 12*nu], [2, -12*nu], [-1, 3]], P, my(b = biel(P[1], P[2]));
  if (b[2]^2 != subst(F0, x, b[1]), error("not on curve"));
  my(d1 = elladd(E1, phi1(b[1], b[2]), ellneg(E1, phi1(Pinf[1], Pinf[2]))), d2 = elladd(E2, phi2(b[1], b[2]), ellneg(E2, phi2(Pinf[1], Pinf[2]))));
  print("[(", P[1], ", ", lift(P[2]), ") - inf+]: order on E1 = ", ellorder(E1, d1), "  on E2 = ", ellorder(E2, d2)));
}
print("torsion of E1(M): ", elltors(E1)[1], "   E2(M): ", elltors(E2)[1]);
\q
