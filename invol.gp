\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Reduced automorphism group of y^2 = f1(x): Mobius maps permuting the six roots, recognised algebraically.
default(realprecision, 120);
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
R = polroots(f1);
near(z) = { my(m = 1e100, k = 0); for (i = 1, 6, if (abs(z - R[i]) < m, m = abs(z - R[i]); k = i)); if (m < 1e-60, k, 0); };
mob(M, z) = (M[1,1]*z + M[1,2]) / (M[2,1]*z + M[2,2]);
mobmat(a, b, c, A, B, C) = {
  \\ matrix of the Mobius map sending a->A, b->B, c->C: compose (a,b,c)->(0,1,oo) with inverse for (A,B,C)
  my(S(u,v,w) = [v - w, -u*(v - w); v - u, -w*(v - u)]);
  matsolve(S(A, B, C), S(a, b, c));
};
found = List();
{
for (i = 1, 6, for (j = 1, 6, for (k = 1, 6, if (i == j || j == k || i == k, next);
  my(M = mobmat(R[1], R[2], R[3], R[i], R[j], R[k]), perm = vector(6), ok = 1);
  for (t = 1, 6, perm[t] = near(mob(M, R[t])); if (!perm[t], ok = 0; break));
  if (ok && #Set(perm) == 6, listput(found, [perm, M / M[2,2]])))));
print("order of the reduced automorphism group: ", #found);
for (n = 1, #found, my(P = found[n][1], M = found[n][2], ord = 1, Q = P);
  while (Q != [1,2,3,4,5,6], Q = vector(6, t, P[Q[t]]); ord++);
  \\ lambda: f1(mob(x)) * (c x + d)^6 = lambda * f1(x)
  my(lam = subst(f1, x, mob(M, R[1] + 1/3)) * (M[2,1]*(R[1] + 1/3) + M[2,2])^6 / subst(f1, x, R[1] + 1/3));
  print("perm ", P, " order ", ord, "  M = [", M[1,1], ", ", M[1,2]; M[2,1], ", 1]");
  if (ord == 2, print("   algdep a: ", algdep(M[1,1], 6), "  b: ", algdep(M[1,2], 6), "  c: ", algdep(M[2,1], 6));
                 print("   lambda: ", lam, "  algdep(lambda,12): ", algdep(lam, 12), "  algdep(sqrt(lambda),24): ", algdep(sqrt(lam), 24))));
}
\q
