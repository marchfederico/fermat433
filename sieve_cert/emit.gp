\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Export the inputs of the Mordell-Weil sieve (Prop. 6.2) for an independent check, for both
\\ curves of the hard pair. Only the exact data the sieve starts from is written: the field L,
\\ the sextic f, the generators P1, P2, the fixed points x+, x- of the involution (as elements
\\ of L), the sieving primes, and the candidate coefficient vectors from step 3. Everything
\\ else (reduced curves, group orders, generators, discrete logs, the image of X(F_q)) the
\\ checker recomputes on its own.
\\ This repeats the first block of step3_setup.gp (the field and the involution) and
\\ skips the p-adic heights, so it runs in seconds rather than minutes.
\\ Usage (from the repository root):  gp -q sieve_cert/emit.gp
default(parisize, "1G");
\\ the two curves of the hard pair: their sextic f, the generators P1, P2 used by the sieve
\\ (step3_setup.gp, twist/step3_setup.gp) and the candidates left by quadratic Chabauty at p = 499
\\ The runs: curve, sextic f, generators P1, P2, candidates left by quadratic Chabauty at the prime
\\ ell (step3_setup.gp, twist/step3_setup.gp, second_prime/make_p1459.py), the sieving primes that
\\ remove candidates (from the step-4 logs), and an optional file of recomputed disks.
{fB = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40; fC = -2*fB;
 ptsB = [[1, 1], [-1, 15]]; ptsC = [[6/5, 172/125], [2, 12]];
 q499 = [[997, 35], [12973, 775]]; q1459 = [[2917, 1166], [26261, 1439]];
 runs = [["Bminus", fB, ptsB, "logs/step3_candidates.gp", 499, q499, ""],
         ["Cplus", fC, ptsC, "logs/twist/step3_candidates.gp", 499, q499, ""],
         ["Bminus_p1459", fB, ptsB, "logs/p1459/Bminus/step3_candidates.gp", 1459, q1459, ""],
         ["Cplus_p1459", fC, ptsC, "logs/p1459/Cplus/step3_candidates.gp", 1459, q1459,
          "second_prime/cands103_Cplus.gp"]];}
fmt(v) = strjoin(apply(c -> Str(c), v), " ");
{
for (ci = 1, #runs,
  my(name = runs[ci][1], f1 = runs[ci][2], pts = runs[ci][3], ell = runs[ci][5]);
  my(sprimes = runs[ci][6]);
  my(g = sum(k = 0, 6, polcoef(f1, k) * (-x + B)^k * (C*x + 1)^(6 - k)));
  my(E = vector(6, k, polcoef(g, k - 1, x) * polcoef(f1, 6) - polcoef(g, 6, x) * polcoef(f1, k - 1)));
  my(h6 = 81*t^6 - 540*t^5 + 1494*t^4 - 2240*t^3 + 1980*t^2 - 1008*t + 232);
  my(vv = polredbest(h6, 1), P6 = vv[1], ab = vv[2], K = nfinit(P6));
  my(Eb = vector(6, k, subst(E[k], B, ab)), gc = gcd(Eb[1], Eb[2]));
  my(c0 = -polcoef(gc, 0, C) / polcoef(gc, 1, C), kap = 1 + ab*c0);
  my(w = rnfequation(K, x^2 - lift(kap)), PL = polredbest(subst(w, x, t)));
  my(bnf = bnfinit(PL, 1));
  my(r6 = nfroots(bnf, subst(P6, t, x)), tK = Mod(subst(lift(r6[1]), x, t), PL));
  my(bL = subst(lift(ab), t, tK), cL = subst(lift(c0), t, tK), kapL = 1 + bL*cL);
  my(sL = Mod(subst(lift(nfroots(bnf, x^2 - lift(kapL))[1]), x, t), PL));
  my(xp = (-1 + sL)/cL, xm = (-1 - sL)/cL);
  read(runs[ci][4]);
  my(cs = cands);
  \\ C+ at p = 1459: the two disks x = 103 gave coefficient vectors of zero precision in the main
  \\ run; they are replaced by the vectors recomputed at higher precision (RESULTS.md, p = 1459).
  if (runs[ci][7] != "",
    read(runs[ci][7]);
    my(old = #[c | c <- cs, c[1] == "103"]);
    cs = concat([c | c <- cs, c[1] != "103"], [c | c <- cands, c[1] == "103"]);
    print(name, ": replaced ", old, " candidates of disk 103 by ", #[c | c <- cands, c[1] == "103"]));
  my(out = Str("sieve_cert/inputs_", name, ".txt"));
  system(Str("rm -f ", out));   \\ write() appends
  write(out, "# fermat433 sieve certificate inputs, curve ", name, ": y^2 = ", f1, ", ell = ", ell);
  write(out, "ELL ", ell);
  write(out, "PL ", fmt(Vec(Polrev(Vec(PL)))));
  write(out, "F ", fmt(Vec(Polrev(Vec(f1)))));
  write(out, "GEN ", fmt(pts[1]));
  write(out, "GEN ", fmt(pts[2]));
  write(out, "XP ", fmt(vector(12, k, polcoef(lift(xp), k - 1, t))));
  write(out, "XM ", fmt(vector(12, k, polcoef(lift(xm), k - 1, t))));
  for (i = 1, #sprimes, write(out, "PRIME ", sprimes[i][1], " ", sprimes[i][2]));
  for (j = 1, #cs, write(out, "CAND ", cs[j][1], " ", cs[j][2], " ", cs[j][3] % ell, " ",
    cs[j][4] % ell));
  print(name, ": ", #cs, " candidates -> ", out));
}
\q
