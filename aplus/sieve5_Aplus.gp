\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Mordell-Weil sieve at p = 5 for the Chabauty candidates on A+: a rational point z has [z - inf+] = (n/m) D + t with 5 not
\\ dividing m (v_5(Log_J(D)) = 1) and t of order 3; at a prime q of M with 5 | #E_i(F_q): pi_i(phi_i(zbar) - phi_i(inf+)) =
\\ lambda * pi_i(phi_i(Dbar)) on the 5-primary parts, with lambda = the 5-adic coefficient of the candidate (known mod 5^6).
default(parisize, "2G"); default(parisizemax, "8G");
p = 5;
w = varlower("w"); Mpol = w^6 + 2; M = nfinit(Mpol);
xp = Mod(w^5, Mpol); xm = -xp; c = -2*Mod(w, Mpol)^4;
A = 160*Mod(w,Mpol)^3 - 64; B = -480*Mod(w,Mpol)^3 - 960; C = 480*Mod(w,Mpol)^3 - 960; D = -160*Mod(w,Mpol)^3 - 64;
f = x^6 - 40*x^3 - 32;
\\ candidates: [label, lambda mod 5^6]; the last three are the known rational points (must survive)
cands = [["x0=1 sg=+", 8316], ["x0=1 sg=-", 7309], ["(-1,3)", 1], ["(-1,-3)", 15624], ["inf+-", 0]];
alive = vector(#cands, i, 1);
red(e, mp) = nfmodpr(M, lift(e), mp);
img(xv, yv, xpb, xmb, Ab, Db) = { my(XX, YY); if (xv == xpb, return([[0, Ab*yv], [0]])); if (xv == xmb, return([[0], [0, -Db*yv]]));
  XX = (xv - xpb)/(xv - xmb); YY = yv*(1 - XX)^3; [[Ab*XX^2, Ab*YY], [Db/XX^2, Db*YY/XX^3]]; };
QMAX = 3000000;
{
forprime (q = 7, 20000, if (q == 5, next);
  foreach (idealprimedec(M, q), pr, my(mp, Ab, Bb, Cb, Db, xpb, xmb, cb, E1, E2, n1, n2, k1, k2, N1, N2, D1, D2, Pinf1, Pinf2, S, k, mult1, mult2, pts);
    if (q^pr.f > QMAX || pr.e > 1, next);
    mp = nfmodprinit(M, pr);
    Ab = red(A, mp); Bb = red(B, mp); Cb = red(C, mp); Db = red(D, mp); xpb = red(xp, mp); xmb = red(xm, mp); cb = red(c, mp);
    E1 = ellinit([0, Bb, 0, Ab*Cb, Ab^2*Db]); E2 = ellinit([0, Cb, 0, Bb*Db, Ab*Db^2]);
    if (E1.disc == 0 || E2.disc == 0, next);
    n1 = ellcard(E1); n2 = ellcard(E2); k1 = valuation(n1, p); k2 = valuation(n2, p);
    if (max(k1, k2) < 2, next);                      \\ need 25 | #E to separate lambda = 8316 (16 mod 25) from the rational points
    N1 = n1 / p^k1; N2 = n2 / p^k2; k = max(k1, k2); if (k > 6, k = 6);
    Pinf1 = [Ab, 8*Ab*cb*xpb]; Pinf2 = [Db, 8*Db*cb*xpb];
    my(bD = img(red(-1, mp), red(3, mp), xpb, xmb, Ab, Db));
    D1 = ellmul(E1, elladd(E1, bD[1], ellneg(E1, Pinf1)), N1); D2 = ellmul(E2, elladd(E2, bD[2], ellneg(E2, Pinf2)), N2);
    if (D1 == [0] && D2 == [0], next);
    mult1 = vector(p^k, i, ellmul(E1, D1, i - 1)); mult2 = vector(p^k, i, ellmul(E2, D2, i - 1));
    pts = List(); for (xv = 0, q - 1, my(fx = Mod(subst(f, x, xv), q)); if (fx == 0, listput(pts, [red(xv, mp), red(0, mp)]); next); if (issquare(fx), my(yq = lift(sqrt(fx))); listput(pts, [red(xv, mp), red(yq, mp)]); listput(pts, [red(xv, mp), red(-yq, mp)])));
    listput(pts, "inf+"); listput(pts, "inf-");
    S = List();
    foreach (pts, P, my(im, P1, P2);
      if (type(P) == "t_STR", im = if (P == "inf+", [Pinf1, Pinf2], [[Ab, -8*Ab*cb*xpb], [Db, -8*Db*cb*xpb]]), im = img(P[1], P[2], xpb, xmb, Ab, Db));
      P1 = ellmul(E1, elladd(E1, im[1], ellneg(E1, Pinf1)), N1); P2 = ellmul(E2, elladd(E2, im[2], ellneg(E2, Pinf2)), N2);
      for (aa = 0, p^k - 1, if (mult1[aa + 1] == P1 && mult2[aa + 1] == P2, listput(S, aa))));
    S = Set(S);
    my(before = vecsum(alive));
    for (i = 1, #cands, if (alive[i] && !setsearch(S, cands[i][2] % p^k), alive[i] = 0));
    if (#S < p^k, print("q = ", q, " f = ", pr.f, ": #E1 = ", n1, " #E2 = ", n2, "  5-parts ", [k1, k2], "  |S| = ", #S, " of ", p^k, "   alive: ", before, " -> ", vecsum(alive), "  ", [cands[i][1] | i <- [1..#cands], alive[i]]));
    if (alive[1] == 0 && alive[2] == 0, break(2))));
}
print("final: ", [cands[i][1] | i <- [1..#cands], alive[i]]);
\q
