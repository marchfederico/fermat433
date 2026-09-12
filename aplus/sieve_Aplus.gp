\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Mordell-Weil sieve for the 43-adic Chabauty candidates on A+ : a rational point z has [z - inf+] = (n/m) D + t with
\\ 43 not dividing m (Log_J(D) has valuation 1) and t of order prime to 43; so for every prime q of M with 43 | #E_i(F_q),
\\ the 43-primary projections satisfy pi_i(phi_i(zbar) - phi_i(inf+)) = a(z) * pi_i(phi_i(Dbar)) with a(z) = the 43-adic
\\ coefficient of the candidate.  Candidates are read from cands.txt: [x0, sg, T, a mod 43^12, ., .].
default(parisize, "2G"); default(parisizemax, "8G");
p = 43;
w = varlower("w"); Mpol = w^6 + 2; M = nfinit(Mpol);
xp = Mod(w^5, Mpol); xm = -xp; c = -2*Mod(w, Mpol)^4;
A = 160*Mod(w,Mpol)^3 - 64; B = -480*Mod(w,Mpol)^3 - 960; C = 480*Mod(w,Mpol)^3 - 960; D = -160*Mod(w,Mpol)^3 - 64;
f = x^6 - 40*x^3 - 32;
cands = readvec("cands.txt");
cands = select(cd -> cd[4] != 0, cands);          \\ the a = 0 candidates are handled by the torsion argument
alive = vector(#cands, i, 1);
print(#cands, " candidates with a != 0 (mod 43^12)");
QMAX = 200000;
red(e, mp) = nfmodpr(M, lift(e), mp);
img(xv, yv, xpb, xmb, Ab, Db) = { my(XX, YY); if (xv == xpb, return([[0, Ab*yv], [0]])); if (xv == xmb, return([[0], [0, -Db*yv]]));
  XX = (xv - xpb)/(xv - xmb); YY = yv*(1 - XX)^3; [[Ab*XX^2, Ab*YY], [Db/XX^2, Db*YY/XX^3]]; };
{
forprime (q = 5, 3000, if (q == 43, next);
  foreach (idealprimedec(M, q), pr, my(mp, F, Ab, Bb, Cb, Db, xpb, xmb, cb, E1, E2, n1, n2, k1, k2, N1, N2, D1, D2, Pinf1, Pinf2, S, ok = 1);
    if (q^pr.f > QMAX || pr.e > 1, next);
    mp = nfmodprinit(M, pr);
    Ab = red(A, mp); Bb = red(B, mp); Cb = red(C, mp); Db = red(D, mp); xpb = red(xp, mp); xmb = red(xm, mp); cb = red(c, mp);
    E1 = ellinit([0, Bb, 0, Ab*Cb, Ab^2*Db]); E2 = ellinit([0, Cb, 0, Bb*Db, Ab*Db^2]);
    if (E1.disc == 0 || E2.disc == 0, next);
    n1 = ellcard(E1); n2 = ellcard(E2); k1 = valuation(n1, p); k2 = valuation(n2, p);
    if (k1 == 0 && k2 == 0, next);
    N1 = n1 / p^k1; N2 = n2 / p^k2;
    \\ images of points of A+(F_q): X = (x - xp)/(x - xm), Y = y (1 - X)^3; special cases X = 0 (x = xp) and X = oo (x = xm)
    Pinf1 = [Ab, 8*Ab*cb*xpb]; Pinf2 = [Db, 8*Db*cb*xpb];
    my(bD = img(red(-1, mp), red(3, mp), xpb, xmb, Ab, Db));
    D1 = ellmul(E1, elladd(E1, bD[1], ellneg(E1, Pinf1)), N1); D2 = ellmul(E2, elladd(E2, bD[2], ellneg(E2, Pinf2)), N2);
    if (D1 == [0] && D2 == [0], next);
    my(k = max(k1, k2), mult1 = vector(p^k, i, ellmul(E1, D1, i - 1)), mult2 = vector(p^k, i, ellmul(E2, D2, i - 1)));
    S = List();
    \\ enumerate A+(F_q): affine points with y in F_q, and inf+-
    my(pts = List()); for (xv = 0, q - 1, my(fx = Mod(subst(f, x, xv), q)); if (fx == 0, listput(pts, [red(xv, mp), red(0, mp)]); next); if (issquare(fx), my(yq = lift(sqrt(fx))); listput(pts, [red(xv, mp), red(yq, mp)]); listput(pts, [red(xv, mp), red(-yq, mp)])));
    listput(pts, "inf+"); listput(pts, "inf-");
    foreach (pts, P, my(im, P1, P2);
      if (type(P) == "t_STR", im = if (P == "inf+", [Pinf1, Pinf2], [[Ab, -8*Ab*cb*xpb], [Db, -8*Db*cb*xpb]]), im = img(P[1], P[2], xpb, xmb, Ab, Db));
      P1 = ellmul(E1, elladd(E1, im[1], ellneg(E1, Pinf1)), N1); P2 = ellmul(E2, elladd(E2, im[2], ellneg(E2, Pinf2)), N2);
      for (aa = 0, p^k - 1, if (mult1[aa + 1] == P1 && mult2[aa + 1] == P2, listput(S, aa))));
    S = Set(S);
    my(before = vecsum(alive));
    for (i = 1, #cands, if (alive[i] && !setsearch(S, cands[i][4] % p^k), alive[i] = 0));
    print("q = ", q, " f = ", pr.f, ": #E1 = ", n1, " #E2 = ", n2, "  43-parts ", [k1, k2], "  |S| = ", #S, " of ", p^k, "   candidates alive: ", before, " -> ", vecsum(alive));
    if (vecsum(alive) == 0, break(2))));
}
print("surviving candidates with a != 0: ", [cands[i][1..2] | i <- [1..#cands], alive[i]]);
\q
