\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ rho as a power series in the disk parameter T (x = x0 + p T), and Strassman.
sqrtser(S) = { my(S0 = polcoef(S, 0, T)); sqrt(S0 + O(p^n)) * sqrt(S / S0); };
bnat1(i, X, Y) = bpointi(ellchangepoint([Ai[i]*X^2, Ai[i]*Y], v1i[i]), a13_1[i]);         \\ phi1 point on the b-model at place i
bnat2(i, X, Y) = bpointi(ellchangepoint([Di[i]/X^2, Di[i]*Y/X^3], v2i[i]), a13_2[i]);
bpointi(Q, a13) = [Q[1], Q[2] + (a13[1]*Q[1] + a13[2])/2];
\\ formal parameter of phi2(z) near O, analytic in X (X -> 0):  s2 = -2u X (D - r X^2) / (2(DY - sDX + (sr-t)X^3) + a1 u X (D - rX^2) + a3 u^3 X^3)
s2par(i, X, Y) = { my(u = v2i[i][1], r = v2i[i][2], s = v2i[i][3], tt = v2i[i][4], a1 = a13_2[i][1], a3 = a13_2[i][2], Dd = Di[i]);
  -2*u*X*(Dd - r*X^2) / (2*(Dd*Y - s*Dd*X + (s*r - tt)*X^3) + a1*u*X*(Dd - r*X^2) + a3*u^3*X^3); };
\\ formal parameter of phi1(z) near O, analytic in W = 1/X (X -> oo), with y the curve's y:  Y W^3 = y (1 - W)^3
s1par(i, W, yy) = { my(u = v1i[i][1], r = v1i[i][2], s = v1i[i][3], tt = v1i[i][4], a1 = a13_1[i][1], a3 = a13_1[i][2], Aa = Ai[i]);
  -2*u*W*(Aa - r*W^2) / (2*(Aa*yy*(1 - W)^3 - s*Aa*W + (s*r - tt)*W^3) + a1*u*W*(Aa - r*W^2) + a3*u^3*W^3); };
rhoser2(x0, y0sign, inf) = {
  my(xt, yt, rho = 0, lg = vector(2));
  if (!inf, xt = x0 + p*T + O(T^D); yt = y0sign * sqrtser(subst(f1, x, xt)),
            xt = 0; yt = 0);     \\ infinity disk: u = p T, handled via X_i, Y_i directly
  for (i = 1, 12, my(X, Y, term, u);
    if (!inf, X = (xt - xpi[i]) / (xt - xmi[i]); Y = yt * (X - 1)^3,
              u = p*T + O(T^D); X = (1 - xpi[i]*u) / (1 - xmi[i]*u);
              Y = y0sign * sqrtser(subst(x^6 * subst(f1, x, 1/x), x, u)) * (xmi[i] - xpi[i])^3 / (1 - xmi[i]*u)^3);
    if (!inf && x0 == spP[i],   \\ phi2(z) -> O: combine -c lambda(phi2) - 2c log X analytically; phi1 normal
      my(s2 = s2par(i, X, Y), Q1s = bnat1(i, X, Y));
      term = chi[i] * lamp(Et1[i], intmodel(vector(5, kk, ev(ai1[kk], rts[i]))), V1[i], Q1s, mm[i][1]) + 2*chi[i] * (logser(s2 / X) + subst(truncate(V2[i]), x, s2));
      if (i <= 2, lg[i] = logE(Et1[i], Q1s, mm[i][1], FL1[i])),
    if (!inf && x0 == spM[i],   \\ phi1(z) -> O: W = 1/X
      my(W = 1 / X, s1 = s1par(i, W, yt), Q2s = bnat2(i, X, Y));
      term = -2*chi[i] * (logser(s1 / W) + subst(truncate(V1[i]), x, s1)) - chi[i] * lamp(Et2[i], intmodel(vector(5, kk, ev(ai2[kk], rts[i]))), V2[i], Q2s, mm[i][2]);
      if (i <= 2, lg[i] = subst(truncate(FL1[i]), x, s1)),
      my(Q1s = bnat1(i, X, Y), Q2s = bnat2(i, X, Y));
      term = chi[i] * (lamp(Et1[i], intmodel(vector(5, kk, ev(ai1[kk], rts[i]))), V1[i], Q1s, mm[i][1]) - lamp(Et2[i], intmodel(vector(5, kk, ev(ai2[kk], rts[i]))), V2[i], Q2s, mm[i][2])) - 2*chi[i] * logser(X);
      if (i <= 2, lg[i] = logE(Et1[i], Q1s, mm[i][1], FL1[i]))));
    rho += term);
  my(a = Minv * [lg[1], lg[2]]~);
  [rho - (a~ * G * a) + Om397, lg[1], lg[2]]; };
rhoser(x0, y0sign, inf) = rhoser2(x0, y0sign, inf)[1];
strassman(S) = { my(vals = vector(D, k, my(c = polcoef(S, k - 1, T)); if (c == 0, 10^6, valuation(c, p))), vmin = vecmin(vals), idx = 0);
  for (k = 1, D, if (vals[k] == vmin, idx = k - 1)); [idx, vmin, vals]; };
