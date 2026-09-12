\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Rank-1 Chabauty for A+ : y^2 = f(x) = x^6 - 40x^3 - 32 at p = 5, inert in F = Q(sqrt(-2)), through the bielliptic model over
\\ M = Q(6th root of -2).  M_P = Q_25 for the primes P | 5.  Logs of E1, E2 over Q_25 from the formal group.  For z in A+(Q):
\\ (L1(z), L2(z)) = lambda (L1(D), L2(D)) with lambda in Q_5 (rank J(Q) = 1, D = [(-1,3) - inf+], Log(inf+) = 0 as torsion).
default(parisize, "2G"); default(parisizemax, "8G");
dummyT = T; dummyt = t;                       \\ variable priorities: T (series) above t (Q_25 generator)
p = 5; N = 45; NT = 44;
Tpol = t^2 - 2;                               \\ Q_25 = Q_5[t]/(t^2 - 2)
f = x^6 - 40*x^3 - 32;
rts = polrootspadic(x^6 + 2, [Tpol, p], N); w0 = rts[1];
thp = -w0^2; nup = -w0^3; if (thp^3 != 2 || nup^2 != -2, error("embedding"));
cp = -2*thp^2; xp = thp*nup; xm = -xp;
A = xp^6 + 40*xp^3 - 32; B = 15*xp^6 - 120*xp^3 - 480; C = 15*xp^6 + 120*xp^3 - 480; D = xp^6 - 40*xp^3 - 32;
F0 = A*x^6 + B*x^4 + C*x^2 + D;
E1c = [B, A*C, A^2*D]; E2c = [C, B*D, A*D^2];       \\ y^2 = x^3 + a2 x^2 + a4 x + a6
\\ ---------- group law on y^2 = x^3 + a2 x^2 + a4 x + a6 over any field
eadd(E, P, Q) = { my(a2 = E[1], a4 = E[2], lam, x3, y3);
  if (P == [0], return(Q)); if (Q == [0], return(P));
  if (P[1] == Q[1], if (P[2] == -Q[2], return([0])); lam = (3*P[1]^2 + 2*a2*P[1] + a4) / (2*P[2]), lam = (Q[2] - P[2]) / (Q[1] - P[1]));
  x3 = lam^2 - a2 - P[1] - Q[1]; y3 = -(lam*(x3 - P[1]) + P[2]); [x3, y3]; };
emul(E, P, n) = { my(R = [0], Q = P); if (n < 0, Q = [Q[1], -Q[2]]; n = -n); while (n > 0, if (n % 2, R = eadd(E, R, Q)); Q = eadd(E, Q, Q); n \= 2); R; };
eon(E, P) = P == [0] || P[2]^2 == P[1]^3 + E[1]*P[1]^2 + E[2]*P[1] + E[3];
\\ ---------- reduction to F_25 and point counts
g = ffgen(Mod(1, p)*Tpol, 't);
red(c) = { my(l = lift(c)); if (type(l) != "t_POL", l = l + 0*t); Mod(lift(polcoef(l, 0)), p) * g^0 + Mod(lift(polcoef(l, 1)), p) * g; };
redE(E) = ellinit([0, red(E[1]), 0, red(E[2]), red(E[3])]);
m1 = ellcard(redE(E1c)); m2 = ellcard(redE(E2c)); print("#E1(F_25) = ", m1, "  #E2(F_25) = ", m2);
\\ ---------- formal logarithm: t = -x/y, w = -1/y; w = t^3 + a2 t^2 w + a4 t w^2 + a6 w^3; omega = dx/(2y)
formallog(E) = { my(ws = T^3 + O(T^(NT + 6)), xs, ys);
  for (i = 1, NT \ 2 + 4, ws = T^3 + E[1]*T^2*ws + E[2]*T*ws^2 + E[3]*ws^3 + O(T^(NT + 6)));
  xs = T / ws; ys = -1 / ws; intformal(deriv(xs) / (2*ys)); };
FL1 = formallog(E1c); FL2 = formallog(E2c);
if (polcoef(FL1, 1) != 1 || polcoef(FL2, 1) != 1, error("formal log normalisation"));
Log(E, FL, m, P) = { my(Q = emul(E, P, m), tt); if (Q == [0], return(0)); tt = -Q[1]/Q[2]; subst(truncate(FL), T, tt) / m; };
phi1(XX, YY) = [A*XX^2, A*YY];
phi2(XX, YY) = [D/XX^2, D*YY/XX^3];
biel(xv, yv) = my(XX = (xv - xp)/(xv - xm)); [XX, yv*(1 - XX)^3];
L12(xv, yv) = my(b = biel(xv, yv), P1 = phi1(b[1], b[2]), P2 = phi2(b[1], b[2])); if (!eon(E1c, P1) || !eon(E2c, P2), error("not on quotient")); [Log(E1c, FL1, m1, P1), Log(E2c, FL2, m2, P2)];
Linf(sg) = my(P1 = phi1(1, sg*8*cp*xp), P2 = phi2(1, sg*8*cp*xp)); [Log(E1c, FL1, m1, P1), Log(E2c, FL2, m2, P2)];
comp(c, i) = my(l = lift(c)); if (type(l) != "t_POL", l = l + 0*t); polcoef(l, i);      \\ Q_5-components of a Q_25 element
val(c) = if (c == 0, 999, min(valuation(comp(c, 0), p), valuation(comp(c, 1), p)));
L0 = Linf(1); LP = L12(-1, 3); a = LP - L0;
print("Log(inf+) = ", apply(val, L0), " (valuations; should be infinite: torsion)");
print("Log_J(D) components: a1 = ", a[1], "\n                     a2 = ", a[2]);
rho_val(L) = a[2]*(L[1] - L0[1]) - a[1]*(L[2] - L0[2]);
print("rho at the known points (valuations): ", apply(val, [rho_val(L12(-1, 3)), rho_val(L12(-1, -3)), rho_val(Linf(1)), rho_val(Linf(-1))]));
lam(L) = (L[1] - L0[1]) / a[1];
print("lambda at (-1,3): ", lam(L12(-1, 3)), "   at (-1,-3): ", lam(L12(-1, -3)));
\\ ---------- residue discs
tiny(Xs, Ys) = intformal(deriv(Xs) / (2*Ys));
strassman(s) = { my(v = vector(NT, i, val(polcoef(s, i - 1))), mn = vecmin(v), k = 0); for (i = 1, NT, if (v[i] == mn, k = i - 1)); k; };
sercomp(s, i) = sum(n = 0, NT - 1, comp(polcoef(s, n), i) * T^n);
zeros0(s0) = { my(pol = sum(i = 0, NT - 1, lift(polcoef(s0, i) + O(p^(N - 10))) * x^i)); select(r -> valuation(r, p) >= 0, polrootspadic(pol, p, N - 12)); };
NZ = 0;
iszero(s) = vecmin(vector(NT, i, valuation(polcoef(s, i - 1) + O(p^(N - 10)), p))) >= N - 10;
strass1(s) = { my(v = vector(NT, i, valuation(polcoef(s, i - 1) + O(p^(N - 10)), p)), mn = vecmin(v), k = 0); for (i = 1, NT, if (v[i] == mn, k = i - 1)); k; };
report(label, rho, L1s) = { my(r0 = sercomp(rho, 0), r1 = sercomp(rho, 1), z0 = iszero(r0), z1 = iszero(r1), use, other, zs, k);
  if (z0 && z1, print(label, ": rho identically zero on the disc (no information)"); NZ += 1000; return);
  use = if (!z0, r0, r1); other = if (!z0, r1, r0);
  zs = zeros0(use); k = strass1(use);
  print(label, ": component ", if (!z0, "1", "t"), " of rho used (the other is ", if (z0 || z1, "identically 0", "nonzero"), "); Strassman index ", k, "; Z_5-zeros: ", #zs);
  foreach (zs, r, my(vo = valuation(subst(truncate(other), T, r) + O(p^(N - 12)), p), lm = (subst(truncate(L1s), T, r) - L0[1]) / a[1], inQ5 = valuation(comp(lm, 1) + O(p^(N - 12)), p) >= N - 14);
    print("     T = ", lift(r + O(p^8)), ": other component valuation ", vo, ";  lambda = ", lift(comp(lm, 0) + O(p^6)), " + (", lift(comp(lm, 1) + O(p^6)), ") t;  lambda in Q_5: ", inQ5);
    print("       lambda full = ", comp(lm, 0), "  bestappr(lambda, 10^8) = ", bestappr(comp(lm, 0), 10^8));
    if (label != "inf sg=1" && label != "inf sg=-1", my(xv = XCUR + p*r); for (d = 1, 6, my(pol = algdep(xv, d)); if (vecmax(abs(Vec(pol))) < 10^8, print("       x algdep: ", pol); break)));
    if (vo >= N - 14 && inQ5, NZ++)); };
{
for (x0 = 0, p - 1, my(fx0 = subst(f, x, x0) % p);
  if (fx0 == 0, error("Weierstrass disc"));
  if (!issquare(Mod(fx0, p)), next);
  foreach ([1, -1], sg,
    my(xs = x0 + p*T, ys = sqrt(subst(f, x, xs) * (1 + O(p^N)) + O(T^(NT + 2))));
    if (lift(polcoef(ys, 0) + O(p)) != lift(sg*sqrt(fx0 + O(p^N)) + O(p)), ys = -ys);
    my(b1 = (xs - xp)/(xs - xm), b2 = ys*(1 - b1)^3, P1 = phi1(b1, b2), P2 = phi2(b1, b2));
    my(I1 = tiny(P1[1], P1[2]), I2 = tiny(P2[1], P2[2]), Lc = L12(x0, polcoef(ys, 0)));
    my(L1s = Lc[1] + I1, L2s = Lc[2] + I2, rho = a[2]*(L1s - L0[1]) - a[1]*(L2s - L0[2]));
    XCUR = x0; report(Str("x0=", x0, " sg=", sg), rho, L1s)));
foreach ([1, -1], sg,
  my(us = p*T, xs = 1/us, ys = sg * sqrt((1 - 40*us^3 - 32*us^6) * (1 + O(p^N)) + O(T^(NT + 2))) / us^3);
  my(b1 = (xs - xp)/(xs - xm), b2 = ys*(1 - b1)^3, P1 = phi1(b1, b2), P2 = phi2(b1, b2));
  my(I1 = tiny(P1[1], P1[2]), I2 = tiny(P2[1], P2[2]), Lc = Linf(sg));
  my(L1s = Lc[1] + I1, L2s = Lc[2] + I2, rho = a[2]*(L1s - L0[1]) - a[1]*(L2s - L0[2]));
  XCUR = 0; report(Str("inf sg=", sg), rho, L1s));
print("total zeros of rho (both components) in A+(Q_5): ", NZ, "   (known rational points: 4)");
}
\q
