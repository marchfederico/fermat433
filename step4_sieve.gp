\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

default(parisize, "2G");
read("step3_setup.gp"); read("cands.gp");
rqf(a, r, q) = Mod(subst(lift(a), t, r), q);
tob(P, a1, a3) = [P[1], P[2] + (a1*P[1] + a3)/2];
xi(E, P, cof, g) = if (P == [0], 0, my(R = ellmul(E, P, cof)); if (R == [0], 0, elllog(E, R, g, 499)));
gen499(E, cof) = { my(R); until (ellmul(E, R, cof) != [0], R = random(E)); ellmul(E, R, cof); };
sieve_prime(q, r) = {
  my(E1q = ellinit([0, rqf(ai1[2], r, q), 0, rqf(ai1[4], r, q), rqf(ai1[5], r, q)]), E2q = ellinit([0, rqf(ai2[2], r, q), 0, rqf(ai2[4], r, q), rqf(ai2[5], r, q)]));
  my(N1 = ellcard(E1q), N2 = ellcard(E2q)); if (N1 % 499 || N2 % 499, return([0, "499 does not divide both orders"]));
  my(c1 = N1 / 499, c2 = N2 / 499, g1 = gen499(E1q, c1), g2 = gen499(E2q, c2));
  my(v1q = vector(4, k, rqf(v1[k], r, q)), v2q = vector(4, k, rqf(v2[k], r, q)), a1_1 = rqf(E1m.a1, r, q), a3_1 = rqf(E1m.a3, r, q), a1_2 = rqf(E2m.a1, r, q), a3_2 = rqf(E2m.a3, r, q));
  my(Aq = rqf(A, r, q), Dq2 = rqf(Dq, r, q), xpq = rqf(xp, r, q), xmq = rqf(xm, r, q));
  \\ generators' images
  my(Qb1 = vector(2, i, [rqf(pts1[i][1], r, q), rqf(pts1[i][2], r, q)]), Qb2 = vector(2, i, [rqf(pts2[i][1], r, q), rqf(pts2[i][2], r, q)]));
  if (!ellisoncurve(E1q, Qb1[1]) || !ellisoncurve(E2q, Qb2[2]), return([0, "generator images not on the reduced curves"]));
  my(XI = vector(2, i, [xi(E1q, Qb1[i], c1, g1), xi(E2q, Qb2[i], c2, g2)]));
  \\ allowed set: images of X(F_q)
  my(allowed = Set(), npts = 0, cnt = 0);
  my(addw = 0);
  for (xx = 0, q - 1, my(fx = Mod(subst(f1, x, xx), q), ys);
    if (fx == 0, ys = [Mod(0, q)], if (issquare(fx), my(s = sqrt(fx)); ys = [s, -s], next));
    foreach (ys, yy, my(xb = Mod(xx, q), P1, P2); npts++;
      if (xb == xmq, P1 = [0], P2 = [0]);
      if (xb == xmq, P2n = [Mod(0, q), Dq2 * yy]; P1 = [0]; P2 = tob(ellchangepoint(P2n, v2q), a1_2, a3_2),
        if (xb == xpq, P1n = [Mod(0, q), -Aq * yy]; P2 = [0]; P1 = tob(ellchangepoint(P1n, v1q), a1_1, a3_1),
          my(X = (xb - xpq) / (xb - xmq), Y = yy * (X - 1)^3);
          P1 = tob(ellchangepoint([Aq*X^2, Aq*Y], v1q), a1_1, a3_1); P2 = tob(ellchangepoint([Dq2/X^2, Dq2*Y/X^3], v2q), a1_2, a3_2)));
      if ((P1 != [0] && !ellisoncurve(E1q, P1)) || (P2 != [0] && !ellisoncurve(E2q, P2)), cnt++);
      allowed = setunion(allowed, Set([[xi(E1q, P1, c1, g1), xi(E2q, P2, c2, g2)]]))));
  if (issquare(Mod(-17, q)), my(s17 = sqrt(Mod(-17, q))); foreach ([s17, -s17], s, my(Y = s * (xmq - xpq)^3, P1 = tob(ellchangepoint([Aq, Aq*Y], v1q), a1_1, a3_1), P2 = tob(ellchangepoint([Dq2, Dq2*Y], v2q), a1_2, a3_2)); npts++;
      if (!ellisoncurve(E1q, P1) || !ellisoncurve(E2q, P2), cnt++);
      allowed = setunion(allowed, Set([[xi(E1q, P1, c1, g1), xi(E2q, P2, c2, g2)]]))));
  [1, N1, N2, XI, allowed, npts, cnt]; };
{
my(entries = read("step4_scan.txt"), usable = List(), surv = vector(#cands, i, 1), report = List());
for (i = 1, #entries, my(e = entries[i]); if (e[1] < 100000 && e[3] % 499 == 0 && e[5] % 499 == 0, listput(usable, [e[1], e[2]])));
print("usable primes (q, root): ", Vec(usable));
for (u = 1, #usable, my(q = usable[u][1], r = usable[u][2], S = sieve_prime(q, r));
  if (S[1] == 0, print("q=", q, " r=", r, ": skipped: ", S[2]); next);
  my(XI = S[4], allowed = S[5], killed = 0, alive = 0);
  for (j = 1, #cands, if (!surv[j], next);
    my(a1 = cands[j][3], a2 = cands[j][4], v = [(a1*XI[1][1] + a2*XI[2][1]) % 499, (a1*XI[1][2] + a2*XI[2][2]) % 499]);
    if (setsearch(allowed, v), alive++, surv[j] = 0; killed++));
  print("q=", q, " r=", r, ": #E1=", S[2], " #E2=", S[3], "  |X(F_q)| = ", S[6], "  |allowed| = ", #allowed, "  off-curve images: ", S[7], "  killed ", killed, ", still alive ", alive));
print("SURVIVORS:");
for (j = 1, #cands, if (surv[j], print("   disk x0=", cands[j][1], " sg=", cands[j][2], "  a mod 499^5 = [", cands[j][3], ", ", cands[j][4], "]  rational-looking: ", cands[j][5])));
write("step4_survivors.txt", vector(#cands, j, surv[j]));
}
\q
