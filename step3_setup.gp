\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Step 3 setup: everything needed to expand rho on residue disks of X(Q_499).  Loads in ~4 minutes.
default(realprecision, 60);
p = 499; N = 30; n = 14; nterms = 44; D = 14;
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
g = sum(k = 0, 6, polcoef(f1, k) * (-x + B)^k * (C*x + 1)^(6 - k));
E = vector(6, k, polcoef(g, k - 1, x) * polcoef(f1, 6) - polcoef(g, 6, x) * polcoef(f1, k - 1));
bmodel(EE) = [0, EE.b2/4, 0, EE.b4/2, EE.b6/4];
bpoint(EE, Q) = [Q[1], Q[2] + (EE.a1*Q[1] + EE.a3)/2];
ev(a, r) = subst(lift(a), t, r);
intmodel(ai) = vector(5, k, if (k == 2 || k == 4 || k == 5, truncate(ai[k] + O(p^N)), 0));
sigmaser(EE) = { my(s2 = ellpadics2(EE, p, n), xt = ellformalpoint(EE, nterms)[1], ft = ellformaldifferential(EE, nterms)[1], u, w);
  u = intformal(-(xt + s2) * ft); w = u * ft; intformal(w - polcoef(w, -1)/x); };
logser(S) = { my(S0 = polcoef(S, 0, T)); if (S0 == 0, error("logser: zero constant term")); log(S0 + O(p^n)) + log(S / S0); };   \\ Iwasawa log of a series (unit or not)
logsig(v, Q) = { my(tt = -Q[1]/Q[2]); subst(truncate(v), x, tt) + logser(tt); };
psivals(ai, Q, K) = { my(xx = Q[1], yy = Q[2], b2 = 4*ai[2], b4 = 2*ai[4], b6 = 4*ai[5], b8 = 4*ai[2]*ai[5] - ai[4]^2, ps = vector(K + 3));
  ps[1] = 0; ps[2] = 1; ps[3] = 2*yy; ps[4] = 3*xx^4 + b2*xx^3 + 3*b4*xx^2 + 3*b6*xx + b8;
  ps[5] = ps[3] * (2*xx^6 + b2*xx^5 + 5*b4*xx^4 + 10*b6*xx^3 + 10*b8*xx^2 + (b2*b8 - b4*b6)*xx + b4*b8 - b6^2);
  for (k = 5, K + 2, my(m2 = k \ 2);
    if (k % 2, ps[k+1] = ps[m2+3]*ps[m2+1]^3 - ps[m2]*ps[m2+2]^3, ps[k+1] = ps[m2+1]*(ps[m2+3]*ps[m2]^2 - ps[m2-1]*ps[m2+2]^2) / ps[3]));
  ps; };
lamp(EE, ai, v, Q, m) = { my(mQ = ellmul(EE, Q, m), ps = psivals(ai, Q, m)); -(2/m^2) * (logsig(v, mQ) - logser(ps[m+1])); };
logE(EE, Q, m, fl) = { my(mQ = ellmul(EE, Q, m), tt = -mQ[1]/mQ[2]); subst(truncate(fl), x, tt) / m; };
chival(al) = sum(i = 1, 12, chi[i] * log(ev(al, rts[i])));
away(EE, Q) = { my(fa = idealfactor(bnf, idealinv(bnf, idealadd(bnf, 1, Q[1]))), s = 0);
  for (k = 1, #fa[,1], my(pr = fa[k,1]); if (pr.p == 2 || pr.p == 3 || pr.p == p, next);
    s += fa[k,2] * chival(nfbasistoalg(bnf, bnfisprincipal(bnf, pr, 1)[2]))); s; };
mvals(Q) = max(0, -valuation(Q[1], p));
hgt(k, which) = { my(s = 0, P = if (which == 1, pts1[k], pts2[k]), EE = if (which == 1, E1m, E2m));
  for (i = 1, 12, my(Pi = vector(2, j, ev(P[j], rts[i])), ai = if (which == 1, intmodel(vector(5, kk, ev(ai1[kk], rts[i]))), intmodel(vector(5, kk, ev(ai2[kk], rts[i])))));
    s += chi[i] * lamp(if (which == 1, Et1[i], Et2[i]), ai, if (which == 1, V1[i], V2[i]), Pi, mm[i][which]) + dw[i] * mvals(Pi));
  s + away(EE, P); };
{
my(h6 = 81*t^6 - 540*t^5 + 1494*t^4 - 2240*t^3 + 1980*t^2 - 1008*t + 232);
my(vv = polredbest(h6, 1), P6 = vv[1], ab = vv[2], K = nfinit(P6));
my(Eb = vector(6, k, subst(E[k], B, ab)), gc = gcd(Eb[1], Eb[2]));
my(c0 = -polcoef(gc, 0, C) / polcoef(gc, 1, C), kap = 1 + ab*c0);
my(w = rnfequation(K, x^2 - lift(kap)), PL = polredbest(subst(w, x, t)));
bnf = bnfinit(PL, 1);
my(r6 = nfroots(bnf, subst(P6, t, x)), tK = Mod(subst(lift(r6[1]), x, t), PL));
bL = subst(lift(ab), t, tK); cL = subst(lift(c0), t, tK); kapL = 1 + bL*cL;
sL = Mod(subst(lift(nfroots(bnf, x^2 - lift(kapL))[1]), x, t), PL);
xp = (-1 + sL)/cL; xm = (-1 - sL)/cL;
F = sum(k = 0, 6, polcoef(f1, k) * (xm*x - xp)^k * (x - 1)^(6 - k));
A = polcoef(F, 6, x); Bq = polcoef(F, 4, x); Cq = polcoef(F, 2, x); Dq = polcoef(F, 0, x);
E1 = ellinit([0, Bq, 0, A*Cq, A^2*Dq], bnf); E2 = ellinit([0, Cq, 0, Bq*Dq, A*Dq^2], bnf);
E1m = ellminimalmodel(E1, &v1); E2m = ellminimalmodel(E2, &v2);
pts = [[1, 1], [-1, 15]]; XX = vector(2); Q1 = vector(2); Q2 = vector(2);
for (i = 1, 2, my(x0 = pts[i][1], y0 = pts[i][2], X = (x0 - xp)/(x0 - xm), Y = y0*(X - 1)^3);
  XX[i] = X; Q1[i] = ellchangepoint([A*X^2, A*Y], v1); Q2[i] = ellchangepoint([Dq/X^2, Dq*Y/X^3], v2));
ai1 = bmodel(E1m); ai2 = bmodel(E2m);
pts1 = [bpoint(E1m, Q1[1]), bpoint(E1m, Q1[2]), bpoint(E1m, elladd(E1m, Q1[1], Q1[2]))];
pts2 = [bpoint(E2m, Q2[1]), bpoint(E2m, Q2[2]), bpoint(E2m, elladd(E2m, Q2[1], Q2[2]))];
rts = polrootspadic(PL, p, N);
bi = vector(12, i, ev(bL, rts[i])); ci = vector(12, i, ev(cL, rts[i])); si = vector(12, i, ev(sL, rts[i]));
Amat = vector(12, i, [-1, -ci[i]; -bi[i], 1] / si[i]);
M4 = matrix(4, 12, r, i, Amat[i][(r - 1) \ 2 + 1, (r - 1) % 2 + 1]);
Rmat = matker(mattranspose(matker(M4)));
fu = bnf.fu; U = matrix(12, #fu, i, j, log(ev(fu[j], rts[i])));
chi = Rmat * matker(mattranspose(U) * Rmat)[,1]; chi = chi / chi[1];
\\ per-place data
xpi = vector(12, i, ev(xp, rts[i])); xmi = vector(12, i, ev(xm, rts[i])); Ai = vector(12, i, ev(A, rts[i])); Di = vector(12, i, ev(Dq, rts[i]));
v1i = vector(12, i, vector(4, k, ev(v1[k], rts[i]))); v2i = vector(12, i, vector(4, k, ev(v2[k], rts[i])));
a13_1 = vector(12, i, [ev(E1m.a1, rts[i]), ev(E1m.a3, rts[i])]); a13_2 = vector(12, i, [ev(E2m.a1, rts[i]), ev(E2m.a3, rts[i])]);
Et1 = vector(12); Et2 = vector(12); V1 = vector(12); V2 = vector(12); FL1 = vector(12); FL2 = vector(12); mm = vector(12);
for (i = 1, 12, my(a1p = vector(5, k, ev(ai1[k], rts[i])), a2p = vector(5, k, ev(ai2[k], rts[i])));
  Et1[i] = ellinit(intmodel(a1p)); Et2[i] = ellinit(intmodel(a2p)); mm[i] = [ellcard(Et1[i], p), ellcard(Et2[i], p)];
  V1[i] = sigmaser(Et1[i]); V2[i] = sigmaser(Et2[i]); FL1[i] = ellformallog(Et1[i], nterms); FL2[i] = ellformallog(Et2[i], nterms));
\\ heights of the generator images and the bilinear form G (with the d_w m_w terms at p, expected 0)
dw = vector(12); prs = idealprimedec(bnf, p);
for (j = 1, 12, my(al = nfbasistoalg(bnf, bnfisprincipal(bnf, prs[j], 1)[2]), val = chival(al));
  for (i = 1, 12, if (valuation(ev(al, rts[i]), p) > 0, dw[i] = val)));
h1 = vector(3, k, hgt(k, 1)); h2 = vector(3, k, hgt(k, 2));
G = matrix(2, 2); G[1,1] = h1[1] - h2[1]; G[2,2] = h1[2] - h2[2]; G[1,2] = ((h1[3] - h1[1] - h1[2]) - (h2[3] - h2[1] - h2[2]))/2; G[2,1] = G[1,2];
\\ log matrix of the generators at places 1, 2 (curve E1)
Mlog = matrix(2, 2, a, b, logE(Et1[a], vector(2, j, ev(pts1[b][j], rts[a])), mm[a][1], FL1[a]));
Minv = Mlog^(-1);
\\ Omega_397 (constant): 2 * sum over the 397-primes of chi'(pi_w) v_w(X(P1))
Om397 = 0; faX = idealfactor(bnf, XX[1]);
for (j = 1, #faX[,1], my(pr = faX[j,1]); if (pr.p == 397, Om397 += 2 * faX[j,2] * chival(nfbasistoalg(bnf, bnfisprincipal(bnf, pr, 1)[2]))));
spP = vector(12, i, lift(Mod(truncate(xpi[i]), p))); spM = vector(12, i, lift(Mod(truncate(xmi[i]), p)));
print("setup done. G = ", G); print("Omega_397 = ", Om397); print("special residues (phi2 -> O): ", spP); print("special residues (phi1 -> O): ", spM);
print("-17 square mod p (infinity disks exist)? ", issquare(Mod(-17, p)));
}
