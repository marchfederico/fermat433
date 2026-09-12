\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Step 2b: chi_Z-heights of the generator images on the elliptic quotients, at p = 499, via the twelve embeddings.
default(parisize, "2G"); default(realprecision, 60);
p = 499; N = 30; n = 20; nterms = 44;
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
g = sum(k = 0, 6, polcoef(f1, k) * (-x + B)^k * (C*x + 1)^(6 - k));
E = vector(6, k, polcoef(g, k - 1, x) * polcoef(f1, 6) - polcoef(g, 6, x) * polcoef(f1, k - 1));
\\ ---- helpers (top level) ----
bmodel(EE) = [0, EE.b2/4, 0, EE.b4/2, EE.b6/4];                       \\ y' = y + (a1 x + a3)/2
bpoint(EE, Q) = [Q[1], Q[2] + (EE.a1*Q[1] + EE.a3)/2];
ev(a, r) = subst(lift(a), t, r);                                        \\ embedding L -> Q_p at the root r
intmodel(ai) = vector(5, k, if (k == 2 || k == 4 || k == 5, truncate(ai[k] + O(p^N)), 0));  \\ integer model congruent mod p^N
sigmaser(EE) = { my(s2 = ellpadics2(EE, p, n), xt = ellformalpoint(EE, nterms)[1], ft = ellformaldifferential(EE, nterms)[1], u, w);
  u = intformal(-(xt + s2) * ft); w = u * ft; [intformal(w - polcoef(w, -1)/x), s2]; };
logsig(v, Q) = { my(tt = -Q[1]/Q[2]); subst(truncate(v), x, tt + O(p^n)) + log(tt + O(p^n)); };
\\ division polynomial values psi_k(Q), k = 0..K, on a model with a1 = a3 = 0 (b-invariants), by the classical recurrences
psivals(ai, Q, K) = { my(xx = Q[1], yy = Q[2], b2 = 4*ai[2], b4 = 2*ai[4], b6 = 4*ai[5], b8 = 4*ai[2]*ai[5] - ai[4]^2, ps = vector(K + 3));
  ps[1] = 0; ps[2] = 1; ps[3] = 2*yy; ps[4] = 3*xx^4 + b2*xx^3 + 3*b4*xx^2 + 3*b6*xx + b8;
  ps[5] = ps[3] * (2*xx^6 + b2*xx^5 + 5*b4*xx^4 + 10*b6*xx^3 + 10*b8*xx^2 + (b2*b8 - b4*b6)*xx + b4*b8 - b6^2);
  for (k = 5, K + 2, my(m2 = k \ 2);                                    \\ ps[k+1] = psi_k
    if (k % 2, ps[k+1] = ps[m2+3]*ps[m2+1]^3 - ps[m2]*ps[m2+2]^3,
               ps[k+1] = ps[m2+1]*(ps[m2+3]*ps[m2]^2 - ps[m2-1]*ps[m2+2]^2) / ps[3]));
  ps; };
\\ local height at p on the model ai (a1=a3=0, good ordinary reduction), for a point Q of infinite order: m = #E(F_p)
lamp(EE, ai, v, Q, m) = { my(mQ = ellmul(EE, Q, m), ps = psivals(ai, Q, m)); if (mQ == [0], error("torsion")); -(2/m^2) * (logsig(v, mQ) - log(ps[m+1] + O(p^n))); };
chival(al) = sum(i = 1, 12, chi[i] * log(ev(al, rts[i])));   \\ sign: PARI's height convention (+log q at q != p)      \\ chi at the uniformiser of a prime (al a generator), and d_w for w | p
away(EE, Q) = { my(fa = idealfactor(bnf, idealinv(bnf, idealadd(bnf, 1, Q[1]))), s = 0);
  for (k = 1, #fa[,1], my(pr = fa[k,1]); if (pr.p == 2 || pr.p == 3 || pr.p == p, next);
    s += fa[k,2] * chival(nfbasistoalg(bnf, bnfisprincipal(bnf, pr, 1)[2]))); s; };
logE(EE, Q, m, fl) = { my(mQ = ellmul(EE, Q, m), tt = -mQ[1]/mQ[2]); subst(truncate(fl), x, tt + O(p^n)) / m; };
{
\\ ---- the field, the involution, the bielliptic model, the quotients (as in step 2a) ----
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
A = polcoef(F, 6, x); Bq = polcoef(F, 4, x); Cq = polcoef(F, 2, x); D = polcoef(F, 0, x);
E1 = ellinit([0, Bq, 0, A*Cq, A^2*D], bnf); E2 = ellinit([0, Cq, 0, Bq*D, A*D^2], bnf);
E1m = ellminimalmodel(E1, &v1); E2m = ellminimalmodel(E2, &v2);
pts = [[1, 1], [-1, 15]]; XX = vector(2); Q1 = vector(2); Q2 = vector(2);
for (i = 1, 2, my(x0 = pts[i][1], y0 = pts[i][2], X = (x0 - xp)/(x0 - xm), Y = y0*(X - 1)^3);
  XX[i] = X; Q1[i] = ellchangepoint([A*X^2, A*Y], v1); Q2[i] = ellchangepoint([D/X^2, D*Y/X^3], v2));
ai1 = bmodel(E1m); ai2 = bmodel(E2m);
pts1 = [bpoint(E1m, Q1[1]), bpoint(E1m, Q1[2]), bpoint(E1m, elladd(E1m, Q1[1], Q1[2])), bpoint(E1m, ellsub(E1m, Q1[1], Q1[2])), bpoint(E1m, ellmul(E1m, Q1[1], 2))];
pts2 = [bpoint(E2m, Q2[1]), bpoint(E2m, Q2[2]), bpoint(E2m, elladd(E2m, Q2[1], Q2[2])), bpoint(E2m, ellsub(E2m, Q2[1], Q2[2])), bpoint(E2m, ellmul(E2m, Q2[1], 2))];
names = ["Q1", "Q2", "Q1+Q2", "Q1-Q2", "2Q1"];
print("b-model checks: ", vector(5, k, my(P = pts1[k]); P[2]^2 == P[1]^3 + ai1[2]*P[1]^2 + ai1[4]*P[1] + ai1[5]), vector(5, k, my(P = pts2[k]); P[2]^2 == P[1]^3 + ai2[2]*P[1]^2 + ai2[4]*P[1] + ai2[5]));
\\ ---- embeddings and the character (as in step 1) ----
rts = polrootspadic(PL, p, N);
bi = vector(12, i, ev(bL, rts[i])); ci = vector(12, i, ev(cL, rts[i])); si = vector(12, i, ev(sL, rts[i]));
Amat = vector(12, i, [-1, -ci[i]; -bi[i], 1] / si[i]);
M = matrix(4, 12, r, i, Amat[i][(r - 1) \ 2 + 1, (r - 1) % 2 + 1]);
Rmat = matker(mattranspose(matker(M)));
fu = bnf.fu; U = matrix(12, #fu, i, j, log(ev(fu[j], rts[i])));
chi = Rmat * matker(mattranspose(U) * Rmat)[,1]; chi = chi / chi[1];
print("character recomputed; dim checks: ", #Rmat, " ", #matker(mattranspose(U) * Rmat));
\\ ---- local data at the twelve places ----
lam1 = matrix(12, 5); lam2 = matrix(12, 5); Lg1 = matrix(12, 5); Lg2 = matrix(12, 5); mm = vector(12, i, [0, 0]);
for (i = 1, 12,
  my(a1p = vector(5, k, ev(ai1[k], rts[i])), a2p = vector(5, k, ev(ai2[k], rts[i])),
     Et1 = ellinit(intmodel(a1p)), Et2 = ellinit(intmodel(a2p)),
     m1 = ellcard(Et1, p), m2 = ellcard(Et2, p), S1 = sigmaser(Et1), S2 = sigmaser(Et2),
     fl1 = ellformallog(Et1, nterms), fl2 = ellformallog(Et2, nterms));
  mm[i] = [m1, m2];
  if (i == 1,  \\ calibration: sigma(kQ)/sigma(Q)^{k^2} = psi_k(Q) on a formal-group point
    my(Q0 = ellmul(Et1, vector(2, k, ev(pts1[1][k], rts[i])), m1), ps = psivals(intmodel(a1p), Q0, 4));
    print("calibration log sigma(kQ0) - k^2 log sigma(Q0) - log psi_k(Q0), k=2,3,4: ",
      vector(3, k, logsig(S1[1], ellmul(Et1, Q0, k+1)) - (k+1)^2*logsig(S1[1], Q0) - log(ps[k+2] + O(p^n)))));
  for (k = 1, 5,
    my(P1 = vector(2, j, ev(pts1[k][j], rts[i])), P2 = vector(2, j, ev(pts2[k][j], rts[i])));
    lam1[i, k] = lamp(Et1, intmodel(a1p), S1[1], P1, m1); lam2[i, k] = lamp(Et2, intmodel(a2p), S2[1], P2, m2);
    Lg1[i, k] = logE(Et1, P1, m1, fl1); Lg2[i, k] = logE(Et2, P2, m2, fl2)));
print("orders #E(F_p) at the 12 places: ", mm);
\\ ---- away-from-p terms: chi(pi_w) * max(0, -v_w(x)) over primes w not above p (chi = 0 above 2, 3) ----
aw1 = vector(5, k, away(E1m, pts1[k])); aw2 = vector(5, k, away(E2m, pts2[k]));
h1 = vector(5, k, sum(i = 1, 12, chi[i] * lam1[i, k]) + aw1[k]); h2 = vector(5, k, sum(i = 1, 12, chi[i] * lam2[i, k]) + aw2[k]);
for (k = 1, 5, print(names[k], ":  h_chi on E1 = ", h1[k], "   away part ", aw1[k]); print("       h_chi on E2 = ", h2[k], "   away part ", aw2[k]));
print("parallelogram law E1: h(Q1+Q2)+h(Q1-Q2)-2h(Q1)-2h(Q2) = ", h1[3] + h1[4] - 2*h1[1] - 2*h1[2]);
print("parallelogram law E2: ", h2[3] + h2[4] - 2*h2[1] - 2*h2[2]);
print("h(2Q1) - 4 h(Q1):  E1: ", h1[5] - 4*h1[1], "   E2: ", h2[5] - 4*h2[1]);
G = matrix(2, 2); G[1,1] = h1[1] - h2[1]; G[2,2] = h1[2] - h2[2]; G[1,2] = ((h1[3] - h1[1] - h1[2]) - (h2[3] - h2[1] - h2[2]))/2; G[2,1] = G[1,2];
print("bilinear form G = <.,.>^E1 - <.,.>^E2 on the generators: ", G);
\\ ---- the identity at the known points: rho(P_k) = sum_i chi_i [lam_i(phi1 P_k) - lam_i(phi2 P_k)] + 2 sum_i chi_i(X(P_k)) - G_kk ----
dw = vector(12, i, chival(nfbasistoalg(bnf, bnfisprincipal(bnf, idealprimedec(bnf, p)[i], 1)[2])));
print("d_w = chi_w(p) at the 12 places (order of idealprimedec): ", dw);
for (k = 1, 2, my(fa = idealfactor(bnf, XX[k])); print("ideal factorisation of X(P", k, "): primes ", apply(pr -> [pr.p, pr.e, pr.f], fa[,1]), " exponents ", fa[,2]~);
  my(br = 0); for (j = 1, #fa[,1], my(pr = fa[j,1]); if (pr.p == 397, br += 2 * fa[j,2] * chival(nfbasistoalg(bnf, bnfisprincipal(bnf, pr, 1)[2]))));
  print("   397-bracket 2 sum chi'(pi_w) v_w(X(P", k, ")) = ", br));
for (k = 1, 2, my(logX = 0);
  for (i = 1, 12, my(Xi = ev(XX[k], rts[i]));
    logX += chi[i] * log(Xi + O(p^n));
    if (valuation(Xi, p) != 0, print("   X(P", k, ") not a unit at place ", i, " valuation ", valuation(Xi, p))));
  my(rho = sum(i = 1, 12, chi[i] * (lam1[i, k] - lam2[i, k])) + 2*logX - G[k, k],
     rhominus = sum(i = 1, 12, chi[i] * (lam1[i, k] - lam2[i, k])) - 2*logX - G[k, k]);
  print("rho(P", k, ") with +2 log X: ", rho, "    with -2 log X: ", rhominus));
\\ independence of the generators: 2x2 log matrices at two places
print("det of [Log_w(Q_i)] at places 1,2 (E1): ", matdet([Lg1[1,1], Lg1[1,2]; Lg1[2,1], Lg1[2,2]]), "   (E2): ", matdet([Lg2[1,1], Lg2[1,2]; Lg2[2,1], Lg2[2,2]]));
print("log consistency: Log(Q1+Q2) - Log(Q1) - Log(Q2) at place 1 (E1): ", Lg1[1,3] - Lg1[1,1] - Lg1[1,2], "   Log(2Q1) - 2Log(Q1): ", Lg1[1,5] - 2*Lg1[1,1]);
write("step2b_data.txt", "chi=", chi, "\nG=", G, "\nh1=", h1, "\nh2=", h2, "\nlam1=", lam1, "\nlam2=", lam2, "\nLg1=", Lg1, "\nLg2=", Lg2, "\nmm=", mm, "\ndw=", dw);
}
\q
