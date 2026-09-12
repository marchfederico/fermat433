\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Step 1: the p-adic idele class character chi_Z of L = Q(tau) in the Neron-Severi isotypic component, p = 499.
default(realprecision, 60);
f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
g = sum(k = 0, 6, polcoef(f1, k) * (-x + B)^k * (C*x + 1)^(6 - k));
E = vector(6, k, polcoef(g, k - 1, x) * polcoef(f1, 6) - polcoef(g, 6, x) * polcoef(f1, k - 1));
h6 = 81*t^6 - 540*t^5 + 1494*t^4 - 2240*t^3 + 1980*t^2 - 1008*t + 232;
p = 499; N = 30; default(parisize, "1G");
{
my(v = polredbest(h6, 1), P6 = v[1], ab = v[2], K = nfinit(P6));
my(Eb = vector(6, k, subst(E[k], B, ab)), gc = gcd(Eb[1], Eb[2]));
my(c0 = -polcoef(gc, 0, C) / polcoef(gc, 1, C), kap = 1 + ab*c0);
my(w = rnfequation(K, x^2 - lift(kap)), PL = polredbest(subst(w, x, t)));
bnf = bnfinit(PL, 1);
my(r6 = nfroots(bnf, subst(P6, t, x)), tK = Mod(subst(lift(r6[1]), x, t), PL));
bL = subst(lift(ab), t, tK); cL = subst(lift(c0), t, tK); kapL = 1 + bL*cL;
sL = Mod(subst(lift(nfroots(bnf, x^2 - lift(kapL))[1]), x, t), PL);
print("s^2 = 1+bc: ", sL^2 == kapL);
\\ the twelve embeddings into Q_p
rts = polrootspadic(PL, p, N); print("embeddings L -> Q_p: ", #rts);

bi = vector(12, i, subst(lift(bL), t, rts[i])); ci = vector(12, i, subst(lift(cL), t, rts[i])); si = vector(12, i, subst(lift(sL), t, rts[i]));
print("check s_i^2 = 1 + b_i c_i for all i: ", vector(12, i, si[i]^2 == 1 + bi[i]*ci[i]) == vector(12, i, 1));
\\ do the Mobius maps permute the p-adic roots of f1?
my(R = polrootspadic(f1, p, N)); print("p-adic roots of f1: ", #R);
if (#R == 6, print("   Mobius maps permute them: ", vector(12, i, my(ok = 1); for (k = 1, 6, my(z = (-R[k] + bi[i])/(ci[i]*R[k] + 1)); if (!vecmin(vector(6, m, valuation(z - R[m], p))) > N - 5, ok = 0)); ok)));
\\ action on holomorphic forms: A_i = (1/s_i) [[-1, -c_i], [-b_i, 1]]  (basis dx/y, x dx/y)
A = vector(12, i, [-1, -ci[i]; -bi[i], 1] / si[i]);
print("A_i^2 = 1: ", vector(12, i, A[i]^2 == matid(2)) == vector(12, i, 1), "   traces: ", vector(12, i, trace(A[i])));
\\ kernel of c -> sum c_i A_i   (expected dimension 9), and its orthogonal complement (the NS-isotypic part, dim 3)
M = matrix(4, 12, r, i, A[i][(r - 1) \ 2 + 1, (r - 1) % 2 + 1]);
Kmat = matker(M); print("dim ker (expect 9): ", #Kmat, "   rank of the A_i span (expect 3): ", matrank(M));
Rmat = matker(mattranspose(Kmat)); print("dim of the isotypic part R (expect 3): ", #Rmat);
allones = vectorv(12, i, 1); print("R orthogonal to the all-ones vector: ", mattranspose(Rmat) * allones);
\\ units
fu = bnf.fu; print("fundamental units: ", #fu, "   class number: ", bnf.no);
U = matrix(12, #fu, i, j, log(subst(lift(fu[j]), t, rts[i])));
print("rank of unit logs: ", matrank(U), "   sum over embeddings of log(u) (cyclotomic check, should be 0): ", vector(#fu, j, sum(i = 1, 12, U[i, j])));
\\ the character: c in R with c^T U = 0
my(Y = matker(mattranspose(U) * Rmat)); print("dim of the character space in the isotypic part (expect 1): ", #Y);
chi = Rmat * Y[,1]; chi = chi / chi[1];
print("chi at the 12 places above p (normalised chi_1 = 1):"); print(chi);
print("check chi^T U = 0: ", mattranspose(chi) * U);
print("dim(R meet span U) = ", 3 - #Y);
\\ values at the primes above 2 and 3 via generators (class number 1)
foreach ([2, 3], q, my(P = idealprimedec(bnf, q)); for (k = 1, #P, my(gen = bnfisprincipal(bnf, P[k], 1)[2], al = nfbasistoalg(bnf, gen));
  print("prime above ", q, " (e=", P[k].e, ", f=", P[k].f, "): chi(uniformiser) = ", -sum(i = 1, 12, chi[i] * log(subst(lift(al), t, rts[i]))))));
\\ effective class Z_eff = sum chi_i A_i (traceless 2x2 over Q_p)
Zeff = sum(i = 1, 12, chi[i] * A[i]); print("Z_eff = ", Zeff, "   trace ", trace(Zeff), "   det ", matdet(Zeff));
write("step1_data.txt", "p=", p, "\nPL=", PL, "\nb=", lift(bL), "\nc=", lift(cL), "\ns=", lift(sL), "\nroots=", rts, "\nchi=", chi, "\nZeff=", Zeff);
}
\q
