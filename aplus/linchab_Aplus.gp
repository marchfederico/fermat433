\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Rank-1 Chabauty for A+ : y^2 = f(x) = x^6 - 40x^3 - 32 at p = 43, through the bielliptic structure over M = Q(6th root of -2):
\\ X = (x - x+)/(x - x-), Y = y (1 - X)^3, Y^2 = A X^6 + B X^4 + C X^2 + D; phi1 = (A X^2, A Y) on E1, phi2 = (D/X^2, D Y/X^3) on E2.
\\ For z in A+(Q): (Log1(z) - Log1(z0), Log2(z) - Log2(z0)) is proportional to (Log1(D), Log2(D)), D = [(-1,3) - inf+], since rank J(Q) = 1.
default(parisize, "2G"); default(parisizemax, "8G");
p = 43; N = 40; NT = 40;                       \\ p-adic precision, series truncation
f = x^6 - 40*x^3 - 32;
wp = polrootspadic(x^6 + 2, p, N)[1]; thp = -wp^2; nup = wp^3;
if (thp^3 != 2 + O(p^N) || nup^2 != -2 + O(p^N), error("embedding"));
cp = -2*thp^2; xp = thp*nup; xm = -xp;
A = xp^6 + 40*xp^3 - 32; B = 15*xp^6 - 120*xp^3 - 480; C = 15*xp^6 + 120*xp^3 - 480; D = xp^6 - 40*xp^3 - 32;
F0 = A*x^6 + B*x^4 + C*x^2 + D;
\\ integer models congruent to E1, E2 modulo p^N
ip(a) = lift(a + O(p^N));
E1 = ellinit([0, ip(B), 0, ip(A*C), ip(A^2*D)]); E2 = ellinit([0, ip(C), 0, ip(B*D), ip(A*D^2)]);
if (valuation(E1.disc, p) || valuation(E2.disc, p), error("bad reduction at p"));
m1 = ellcard(E1, p); m2 = ellcard(E2, p); print("#E1(F_p) = ", m1, "  #E2(F_p) = ", m2);
Log(E, m, P) = if (P == [0], 0, ellpadiclog(E, p, N - 8, ellmul(E, P, m)) / m);
phi1(XX, YY) = [A*XX^2, A*YY];
phi2(XX, YY) = [D/XX^2, D*YY/XX^3];
biel(xv, yv) = my(XX = (xv - xp)/(xv - xm)); [XX, yv*(1 - XX)^3];
L12(xv, yv) = my(b = biel(xv, yv)); [Log(E1, m1, phi1(b[1], b[2])), Log(E2, m2, phi2(b[1], b[2]))];
\\ the known points; infinity: X = 1, Y = +-8 c xp
Linf(sg) = [Log(E1, m1, phi1(1, sg*8*cp*xp)), Log(E2, m2, phi2(1, sg*8*cp*xp))];
L0 = Linf(1); LP = L12(-1, 3);
a = LP - L0; print("Log_J(D) = ", a);
if (vecmin(apply(valuation, apply(t -> t + O(p^(N-10)), a))) > 30, error("D looks torsion at this precision"));
rho_val(L) = a[2]*(L[1] - L0[1]) - a[1]*(L[2] - L0[2]);
print("rho at the known points: ", [rho_val(L12(-1, 3)), rho_val(L12(-1, -3)), rho_val(Linf(1)), rho_val(Linf(-1))]);
\\ ---------- residue discs: series in T, x = x0 + p T (affine, non-Weierstrass), Weierstrass discs by y = pT, infinity by u = 1/x = pT
\\ integrate the invariant differential of E_i along the image of the disc: tiny integral
tiny(Xs, Ys, Ei) = { my(om = deriv(Xs) / (2*Ys)); intformal(om); };   \\ a1 = a3 = 0 models
strassman(s) = { my(v = vector(NT, i, valuation(polcoef(s, i - 1), p)), mn = vecmin(v), k = 0); for (i = 1, NT, if (v[i] == mn, k = i - 1)); k; };
zeros(s) = { my(pol = sum(i = 0, NT - 1, lift(polcoef(s, i) + O(p^(N - 12))) * x^i)); polrootspadic(pol, p, N - 14); };
NZ = 0; found = List(); system("rm -f cands.txt");
disc_report(label, rho, L1s, L2s, x0, sgn) = { my(k = strassman(rho), rts = zeros(rho), zs = select(r -> valuation(r, p) >= 0, rts));
  NZ += #zs;
  foreach (zs, r, my(a1v = (subst(truncate(L1s), T, r) - L0[1]) / a[1], a2v = (subst(truncate(L2s), T, r) - L0[2]) / a[2], rat = bestappr(a1v, 10^6));
    listput(found, [x0, sgn, r, a1v]);
    write("cands.txt", [x0, sgn, lift(r + O(p^12)), lift(a1v + O(p^12)), valuation(a1v - a2v + O(p^20), p), rat]));
  print(label, ": Strassman ", k, "  Z_p-zeros ", #zs, if (#zs, Str("  T = ", apply(r -> lift(r + O(p^6)), zs)), "")); };
{
for (x0 = 0, p - 1,
  my(fx0 = subst(f, x, x0) % p);
  if (fx0 == 0, error("Weierstrass disc: not implemented (f has no root mod p)"));
  if (!issquare(Mod(fx0, p)), next);
  foreach ([1, -1], sg,
    my(xs = x0 + p*T, ys = sqrt(subst(f, x, xs) * (1 + O(p^N)) + O(T^(NT+2))));
    if (lift(polcoef(ys, 0) + O(p)) != lift(sg*sqrt(fx0 + O(p^N)) + O(p)), ys = -ys);
    my(b1 = (xs - xp)/(xs - xm), b2 = ys*(1 - b1)^3);
    my(P1 = phi1(b1, b2), P2 = phi2(b1, b2), I1 = tiny(P1[1], P1[2], E1), I2 = tiny(P2[1], P2[2], E2));
    my(Lc = L12(x0, polcoef(ys, 0)), L1s = Lc[1] + I1, L2s = Lc[2] + I2, rho = a[2]*(L1s - L0[1]) - a[1]*(L2s - L0[2]));
    disc_report(Str("x0=", x0, " sg=", sg), rho, L1s, L2s, x0, sg)));
\\ discs at infinity: u = 1/x = pT, y = +- x^3 sqrt(f(x)/x^6)
foreach ([1, -1], sg,
  my(us = p*T, xs = 1/us, ys = sg * sqrt((1 - 40*us^3 - 32*us^6) * (1 + O(p^N)) + O(T^(NT+2))) / us^3);
  my(b1 = (xs - xp)/(xs - xm), b2 = ys*(1 - b1)^3);
  my(P1 = phi1(b1, b2), P2 = phi2(b1, b2), I1 = tiny(P1[1], P1[2], E1), I2 = tiny(P2[1], P2[2], E2));
  my(Lc = Linf(sg), L1s = Lc[1] + I1, L2s = Lc[2] + I2, rho = a[2]*(L1s - L0[1]) - a[1]*(L2s - L0[2]));
  disc_report(Str("inf sg=", sg), rho, L1s, L2s, -1, sg));
print("total Z_p-zeros of rho on A+(Q_43): ", NZ, "   (known rational points: 4)");
}
\q
