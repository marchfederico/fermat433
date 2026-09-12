\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Chabauty-Coleman on the descent quartic C_k (k = KK) of x^4 + 2y^3 + z^3 = 0 via p-adic elliptic logarithms.
default(parisizemax, 4000000000);
w; u; z; aa; bb; cc;
read("qcoeffs.gp");
p = PP; PREC = 30; M = 40;
F = if (KK == 0, F0, F1); AK = if (KK == 0, AK0, AK1); QC = if (KK == 0, QC0, QC1); KP = if (KK == 0, KP0, KP1);
Fd = [deriv(F, aa), deriv(F, bb), deriv(F, cc)];
ev(P, v) = substvec(P, [aa, bb, cc], v);
TH = polrootspadic(x^3 - 2, p, PREC);
if (#TH != 3, error("p does not split completely in K"));
emb(e, j) = subst(e, w, TH[j]);
{
EC = vector(3, j,
  my(q = emb(AK, j), qc = vector(5, i, emb(QC[i], j)), d = qc[2], c = qc[3], b = qc[4], a = qc[5]);
  if (valuation(qc[1] - q^2, p) < PREC - 2, error("constant term is not A^2"));
  my(a1 = d/q, a2 = c - d^2/(4*q^2), a3 = 2*q*b, a4 = -4*q^2*a, a6 = a2*a4);
  my(E = ellinit([a1, a2, a3, a4, a6]), Ered = ellinit(apply(t -> Mod(truncate(t), p), [a1, a2, a3, a4, a6])));
  [TH[j], q, d, c, E, ellcard(Ered), valuation(E.disc, p), ellformallog(E, M, 'z)]);
}
for (j = 1, 3, print("E^(", j, "): v_p(disc) = ", EC[j][7], ", #E(F_p) = ", EC[j][6]));
{
piT(P, j) =
  my(th = EC[j][1], q = EC[j][2], d = EC[j][3], c = EC[j][4]);
  my(r = P[1] + P[2]*th + P[3]*th^2, s = P[1] - P[3]*th^2, t = P[2]*th - P[3]*th^2, W = q*r^2);
  if (t == 0, return([0]));
  [(2*q*(W + q*s^2) + d*s*t)/t^2, s*(4*q^2*(W + q*s^2) + 2*q*(d*s*t + c*t^2) - d^2*t^2/(2*q))/t^3];
}
{
plog(R, j) =
  my(E = EC[j][5], N = EC[j][6], R2, tt);
  if (#R == 1, return(0));
  R2 = ellmul(E, R, N);
  if (#R2 == 1, return(0));
  tt = -R2[1]/R2[2];
  if (valuation(tt, p) < 1, error("multiple not in the kernel of reduction"));
  subst(truncate(EC[j][8]), 'z, tt) / N;
}
charts(Pb) = if (Pb[3] % p, 3, if (Pb[2] % p, 2, 1));
{
param(Pb, ch) =
  my(fr = setminus([1, 2, 3], [ch]), g = vector(3, i, ev(Fd[i], Pb)));
  if (g[fr[2]] % p, [fr[1], fr[2]], [fr[2], fr[1]]);
}
{
expand(B, ch, par, oth) =
  my(C = vector(3), S);
  C[ch] = 1; C[par] = B[par] + u + O(u^M); S = B[oth] + O(u^M);
  for (it = 1, 9, C[oth] = S; S = S - ev(F, C)/ev(Fd[oth], C));
  C[oth] = S; C;
}
{
basis(C, ch, par) =
  my(den, sgn);
  if (ch == 3, if (par == 1, den = ev(Fd[2], C); sgn = 1, den = ev(Fd[1], C); sgn = -1));
  if (ch == 2, if (par == 3, den = ev(Fd[1], C); sgn = 1, den = ev(Fd[3], C); sgn = -1));
  if (ch == 1, if (par == 3, den = ev(Fd[2], C); sgn = -1, den = ev(Fd[3], C); sgn = 1));
  vector(3, g, sgn*C[g]/den);
}
{
hensel(Pb, ch, par, oth) =
  my(B = vector(3, i, Pb[i] + O(p^PREC)), S);
  B[ch] = 1 + O(p^PREC); S = B[oth];
  for (it = 1, 12, B[oth] = S; S = S - ev(F, B)/ev(Fd[oth], B));
  B[oth] = S; B;
}
pts = List();
for (a0 = 0, p - 1, for (b0 = 0, p - 1, if (ev(F, [a0, b0, 1]) % p == 0, listput(pts, [a0, b0, 1]))));
for (a0 = 0, p - 1, if (ev(F, [a0, 1, 0]) % p == 0, listput(pts, [a0, 1, 0])));
if (ev(F, [1, 0, 0]) % p == 0, listput(pts, [1, 0, 0]));
pts = Vec(pts);
print("#C(F_p) = ", #pts, "; all smooth: ", vecmin(vector(#pts, i, sum(g = 1, 3, (ev(Fd[g], pts[i]) % p) != 0))) > 0);
{
reduceP(Q) =
  my(ch = if (Q[3] % p, 3, if (Q[2] % p, 2, 1)), R = Q/Q[ch]);
  vector(3, i, lift(Mod(numerator(R[i]), p) / denominator(R[i])));
}
{
diskof = vector(#KP, i,
  my(R = reduceP(KP[i]), ix = select(t -> t == R, pts, 1));
  if (#ix != 1, error("known point not among F_p points"));
  ix[1]);
}
gbase = 0;
{
for (i = 1, #pts,
  my(Pb = pts[i], ok = 1);
  if (Pb[3] == 1 && ev(Fd[2], Pb) % p,
    for (j = 1, 3, my(th = EC[j][1], t = Pb[2]*th - Pb[3]*th^2); if (valuation(t, p) > 0, ok = 0));
    if (ok, gbase = i; break)));
}
Bg = hensel(pts[gbase], 3, 1, 2);
Cg = expand(Bg, 3, 1, 2); eg = basis(Cg, 3, 1);
{
pullback(C, j) =
  my(th = EC[j][1], q = EC[j][2], d = EC[j][3], c = EC[j][4], E = EC[j][5]);
  my(r = C[1] + C[2]*th + C[3]*th^2, s = C[1] - C[3]*th^2, t = C[2]*th - C[3]*th^2, W = q*r^2);
  my(X = (2*q*(W + q*s^2) + d*s*t)/t^2, Y = s*(4*q^2*(W + q*s^2) + 2*q*(d*s*t + c*t^2) - d^2*t^2/(2*q))/t^3);
  deriv(X, u) / (2*Y + E.a1*X + E.a3);
}
{
GV = vector(3, j,
  my(om = pullback(Cg, j), Mx = matrix(3, 3, i, g, polcoef(eg[g], i - 1, u)), rhs = vector(3, i, polcoef(om, i - 1, u))~, sol, res);
  sol = matsolve(Mx, rhs);
  res = vecmin(vector(10, i, valuation(polcoef(om - sol[1]*eg[1] - sol[2]*eg[2] - sol[3]*eg[3], i + 2, u), p)));
  print("E^(", j, "): pullback in the canonical basis; residual valuation on coefficients 3..12 >= ", res);
  sol~);
}
ELL = vector(#KP, i, vector(3, j, plog(piT(KP[i], j), j)));
for (i = 1, #KP, print("log vector of ", KP[i], ": valuations ", vector(3, j, valuation(ELL[i][j], p))));
nz = select(v -> v != [0, 0, 0], ELL);
if (#nz < 2, error("fewer than two independent known classes"));
cross(a, b) = [a[2]*b[3] - a[3]*b[2], a[3]*b[1] - a[1]*b[3], a[1]*b[2] - a[2]*b[1]];
LAM = cross(nz[1], nz[2]);
for (i = 3, #nz, print("third class against the annihilator: valuation ", valuation(LAM*nz[i]~, p)));
GL = LAM[1]*GV[1] + LAM[2]*GV[2] + LAM[3]*GV[3];
sc = p^(-vecmin(vector(3, i, valuation(GL[i], p))));
GL = GL*sc; LAM = LAM*sc;
print("annihilating differential, valuations of coefficients: ", vector(3, i, valuation(GL[i], p)));
{
strassman(H) =
  my(m = +oo, L = #H, idx = -1);
  for (i = 1, L, if (H[i] != 0, m = min(m, valuation(H[i], p))));
  if (m == +oo, return(-1));
  for (i = 1, L, if (H[i] == 0 && type(H[i]) == "t_PADIC" && padicprec(H[i], p) <= m, return(-1)));
  if (L - floor(log(L)/log(p)) <= m, return(-1));
  for (i = 1, L, if (H[i] != 0 && valuation(H[i], p) == m, idx = i - 1));
  idx;
}
total = 0; bad = 0;
{
for (i = 1, #pts,
  my(Pb = pts[i], ch = charts(Pb), pr, par, oth, kn, B, h0, C, e, Om, H, bnd);
  pr = param(Pb, ch); par = pr[1]; oth = pr[2];
  kn = select(d -> d == i, diskof, 1);
  if (#kn,
    my(Q = KP[kn[1]]); B = vector(3, t, Q[t]/Q[ch] + O(p^PREC)); h0 = 0,
    B = hensel(Pb, ch, par, oth); h0 = sum(j = 1, 3, LAM[j]*plog(piT(B, j), j)));
  C = expand(B, ch, par, oth); e = basis(C, ch, par);
  Om = GL[1]*e[1] + GL[2]*e[2] + GL[3]*e[3];
  H = concat([h0], vector(M - 1, n, polcoef(Om, n - 1, u) * p^n / n));
  bnd = strassman(H);
  if (bnd < 0, bad++, total += bnd);
  if (bnd != #kn, print("disk ", Pb, ": bound ", bnd, ", known rational points ", #kn)));
}
print("\nC_", KK, " at p = ", p, ": total Strassman bound ", total, ", undetermined disks ", bad, ", known rational points ", #KP);
