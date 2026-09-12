\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

default(realprecision, 200);
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
R = polroots(f1);
near(z) = { my(m = 1e100, k = 0); for (i = 1, 6, if (abs(z - R[i]) < m, m = abs(z - R[i]); k = i)); if (m < 1e-80, k, 0); };
mob(M, z) = (M[1,1]*z + M[1,2]) / (M[2,1]*z + M[2,2]);
mobmat(a, b, c, A, B, C) = { my(S(u,v,w) = [v - w, -u*(v - w); v - u, -w*(v - u)]); matsolve(S(A, B, C), S(a, b, c)); };
g = sum(k = 0, 6, polcoef(f1, k) * (-x + b)^k * (c*x + 1)^(6 - k));
E = vector(6, k, polcoef(g, k - 1, x) * polcoef(f1, 6) - polcoef(g, 6, x) * polcoef(f1, k - 1));
r1 = polresultant(E[1], E[2], c);
{
for (i = 1, 6, for (j = 1, 6, for (k = 1, 6, if (i == j || j == k || i == k, next);
  my(M = mobmat(R[1], R[2], R[3], R[i], R[j], R[k]), perm = vector(6), ok = 1);
  for (t = 1, 6, perm[t] = near(mob(M, R[t])); if (!perm[t], ok = 0; break));
  if (!ok || #Set(perm) != 6, next);
  my(Q = perm, ord = 1); while (Q != [1,2,3,4,5,6], Q = vector(6, t, perm[Q[t]]); ord++);
  if (ord != 2, next);
  M = M / M[2,2]; my(bn = M[1,2], cn = M[2,1]);
  print(perm, "  a=", round(real(M[1,1])), "  b=", bn, "  c=", cn);
  print("   |E_k(b,c)| = ", vector(6, t, round(abs(subst(subst(E[t], b, bn), c, cn)) * 1e60)), "e-60   |r1(b)| = ", abs(subst(r1, b, bn)));
  print("   lambda/(1+bc)^3 = ", subst(f1, x, mob(M, 1/3)) * (cn/3 + 1)^6 / subst(f1, x, 1/3) / (1 + bn*cn)^3))));
}
\q
