\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Fake 2-Selmer group of Jac(y^2 = f(x)), deg f = 6 irreducible: global side.
default(parisize, "2G");
f = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;
c = pollead(f); P = c^5 * subst(f, x, y/c);           \\ monic: root Y = c*theta
print("monic sextic: ", P, "   discriminant factors: ", factor(abs(poldisc(P)))[,1]~);
bnf = bnfinit(P, 1);
print("class group: ", bnf.cyc, "   signature: ", bnf.sign, "   field disc: ", factor(abs(bnf.disc)));
th = Mod(y, P) / c;                                     \\ theta as an element of L
print("check f(theta) = 0: ", subst(f, x, th) == 0);
\\ quadratic subfields?  (then (1,-1) would be trivial globally)
print("subfields of degree 2: ", #select(v -> poldegree(v[1]) == 2, nfsubfields(bnf, 2)), "   degree 3: ", #select(v -> poldegree(v[1]) == 3, nfsubfields(bnf, 3)));
S = concat([idealprimedec(bnf, 2), idealprimedec(bnf, 3), idealprimedec(bnf, 17)]);
print("primes above 2, 3, 17 (p, e, f): ", apply(pr -> [pr.p, pr.e, pr.f], S));
su = bnfsunit(bnf, S);
gens = concat([bnf.tu[2]], concat(bnf.fu, su[1]));      \\ torsion unit, fundamental units, S-units
print("generators of L(S,2) (mod squares): ", #gens, "  (class group 2-part: ", bnf.cyc, ")");
\\ norms mod squares as vectors over {-1, 2, 3, 17}
nv(a) = { my(n = nfeltnorm(bnf, a), v = vector(4)); v[1] = (n < 0); n = abs(n); v[2] = valuation(n, 2) % 2; v[3] = valuation(n, 3) % 2; v[4] = valuation(n, 17) % 2; if (n / 2^valuation(n,2) / 3^valuation(n,3) / 17^valuation(n,17) != 1, error("norm has other primes")); v; };
NM = Mod(matrix(#gens, 4, i, j, nv(gens[i])[j]), 2);
K = lift(matker(mattranspose(NM)));   \\ combinations with square norm: kernel of the F2-linear map gens -> norm vector
print("dim of norm-square subgroup of L(S,2): ", #K, " (out of ", #gens, ")");
\\ images of Q(S,2) = <-1, 2, 3, 17> in L(S,2): express via bnfissunit
qv(a) = { my(e = bnfissunit(bnf, su, a)); if (e == 0, error("not an S-unit")); lift(Mod(e, 2)); };
QS = [qv(-1), qv(2), qv(3), qv(17)];
print("Q(S,2) images (exponent vectors mod 2) computed");
\\ F_glob = norm-square subgroup / span(QS): basis of the quotient
V = matconcat(vector(#K, i, K[,i]));    \\ columns: basis of norm-square subgroup, in the gens coordinates
W = Mod(matconcat([V, matconcat(QS~)~]), 2);
print("dim norm-square subgroup: ", matrank(Mod(V, 2)), "   dim of Q(S,2) image: ", matrank(Mod(matconcat(QS~)~, 2)), "   dim F_glob = ", matrank(W) - matrank(Mod(matconcat(QS~)~, 2)));
\\ local factorisations
foreach ([2, 3, 17], p, my(fa = factorpadic(f, p, 60), degs = vector(#fa[,1], i, poldegree(fa[i,1])), m = #degs, hasodd = vecmax(apply(d -> d % 2, degs)) == 1, t, d);
  t = m - 1 - hasodd; d = t + 4*(p == 2);
  print("p = ", p, ": factor degrees ", degs, "   dim J(Q_p)[2] = ", t, "   dim J(Q_p)/2J = ", d, "   odd-degree factor: ", hasodd));
print("real roots of f: ", #select(r -> abs(imag(r)) < 1e-30, polroots(f)));
write("global_out.txt", "done");
