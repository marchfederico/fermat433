\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

\\ Fake 2-Selmer SET of the genus-2 curve C : y^2 = f(x), f irreducible of degree 6 over Q (Bruin-Stoll 2009, Sections 2, 4-6).
\\ Sel_fake(C) = {delta in L(S,2)/Q(S,2) : N(delta) in f6 Q*^2, res_v(delta) in mu_v(C(Q_v)) for v in S and v = oo}.
\\ The set computed here uses only the places in S (a superset of the true fake Selmer set); if it is empty, C(Q) is empty.
\\ Local images mu_p(C(Q_p)) are computed exactly by recursive subdivision of p-adic discs (Bruin-Stoll Lemma 4.4 / our criterion).
default(parisize, "2G"); default(parisizemax, "8G");
read("curve_input.gp");
clorder(cols, cyc) = if (#cyc == 0, 1, my(M = if (#cols == 0, matdiagonal(cyc), matconcat([matconcat(cols), matdiagonal(cyc)]))); abs(matdet(mathnf(M))));
setup(fpol) = {
  my(P0, red, cyc, cols, q, ord, tgt, Msys, e0);
  f = fpol; c = pollead(f); P0 = c^5 * subst(f, x, y/c);
  red = polredbest(P0, 1); P = red[1]; th = red[2] / c; thinv = th^(-1);
  if (subst(f, x, th) != 0, error("theta is not a root of f"));
  bnf = bnfinit(P, 1); cyc = bnf.cyc;
  print("L = Q[y]/(", P, "), signature ", bnf.sign, ", class group ", cyc);
  SEXTRA = []; cols = [];
  foreach (SPRIMES, p, foreach (idealprimedec(bnf, p), pr, cols = concat(cols, [bnfisprincipal(bnf, pr, 0)])));
  ord = clorder(cols, cyc); q = 2;
  while (ord % 2 == 0, q = nextprime(q + 1); if (vecsearch(vecsort(SPRIMES), q) || bnf.disc % q == 0, next);
    foreach (idealprimedec(bnf, q), pr, cols = concat(cols, [bnfisprincipal(bnf, pr, 0)])); SEXTRA = concat(SEXTRA, [q]); ord = clorder(cols, cyc));
  SALL = concat(SPRIMES, SEXTRA);
  S = concat(apply(p -> idealprimedec(bnf, p), SALL)); su = bnfsunit(bnf, S);
  gens = concat(concat(bnf.fu, [bnf.tu[2]]), su[1]);
  NM = matrix(#gens, 1 + #SALL, i, j, my(n = nfeltnorm(bnf, gens[i]), an = abs(n)); if (j == 1, n < 0, valuation(an, SALL[j-1]) % 2));
  for (i = 1, #gens, my(an = abs(nfeltnorm(bnf, gens[i]))); foreach (SALL, q, an /= q^valuation(an, q)); if (an != 1, error("norm outside S")));
  QS = matrix(#gens, 1 + #SALL, i, j, my(e = bnfissunit(bnf, su, concat([-1], SALL)[j])); if (e == 0 || #e != #gens, error("not an S-unit")); lift(Mod(e[i], 2)));
  for (j = 1, 1 + #SALL, my(q = concat([-1], SALL)[j], e = bnfissunit(bnf, su, q), pr = Mod(1, P)); for (i = 1, #gens, pr *= Mod(lift(gens[i]) * Mod(1, P), P)^lift(e[i])); if (pr != q, error("S-unit exponent ordering mismatch")));
  \\ norm class of f6 over {-1} u SALL; f6 must be an S-unit
  my(af = abs(c)); foreach (SALL, q, af /= q^valuation(af, q)); if (af != 1, error("leading coefficient not an S-unit: enlarge SPRIMES"));
  tgt = vectorv(1 + #SALL, j, if (j == 1, c < 0, valuation(abs(c), SALL[j-1]) % 2));
  Msys = Mod(mattranspose(NM), 2);
  K = lift(matker(Msys));
  e0 = matinverseimage(Msys, Mod(tgt, 2));
  if (#e0 == 0, print("no element of L(S,2) has norm in f6 Q*^2: W = {}  =>  C(Q) is empty"); ISEMPTY = 1; return([]));
  ISEMPTY = 0; E0 = lift(e0);
  my(Bq = Mod(QS, 2), rq = matrank(Bq), Fb = List());
  for (i = 1, #K, my(M = matconcat([Bq, matconcat(Vec(Fb)), Mod(K[,i], 2)])); if (matrank(M) > rq + #Fb, listput(Fb, Mod(K[,i], 2))));
  FB = apply(v -> lift(v), Vec(Fb));
  print("S = ", SALL, "; #gens L(S,2) = ", #gens, ", norm-square subgroup dim ", #K, ", Q(S,2) image dim ", rq, "; the coset W has 2^", #FB, " elements mod Q(S,2)");
  elt(ev) = my(a = Mod(1, P)); for (j = 1, #gens, if (ev[j] % 2, a *= Mod(lift(gens[j]) * Mod(1, P), P))); a;
  W = vector(2^#FB, i, my(bits = binary(i - 1), ev = E0); bits = concat(vector(#FB - #bits), bits); for (j = 1, #FB, if (bits[j], ev += FB[j])); elt(ev));
  W; };
hb(a, b, pr) = (nfhilbert(bnf, lift(a), lift(b), pr) == -1);
nonres(p) = { my(u = 2); while (kronecker(u, p) != -1, u++); u; };
mkbasis(pr) = { my(m = 2 + (pr.p == 2) * pr.e * pr.f, cands = List(), sel = List(), H, G, unif, ee, jmax);
  listput(cands, Mod(nfbasistoalg(bnf, pr.gen[2]), P)); foreach ([-1, 2, 3, 5, 7, 11, 13], q, listput(cands, Mod(q, P)));
  for (k = -6, 6, listput(cands, Mod(y + k, P)); listput(cands, Mod(y^2 + k, P)); listput(cands, Mod(y^2 + k*y + 1, P)); listput(cands, Mod(y^3 + k, P)));
  for (t = 1, 160, listput(cands, Mod(sum(i = 0, 5, (random(7) - 3) * y^i), P)));
  unif = Mod(nfbasistoalg(bnf, pr.gen[2]), P); ee = pr.e; jmax = 2*ee + 3;
  for (j = 1, jmax, foreach ([1, y, y + 1, y^2 + 1, y^2 + y + 1, y^3 + 1], u, listput(cands, 1 + unif^j * Mod(u, P))));
  cands = select(cc -> cc != 0, Vec(cands));
  H = Mod(matrix(#cands, #cands, a, b, hb(cands[a], cands[b], pr)), 2);
  if (matrank(H) != m, error(Str("candidates span ", matrank(H), " of ", m, " dimensions at a prime above ", pr.p)));
  for (i = 1, #cands, if (#sel >= m, break); my(rows = concat(Vec(sel), [i]), Mr = matrix(#rows, #cands, a, b, H[rows[a], b])); if (matrank(Mr) > #sel, listput(sel, i)));
  G = Mod(matrix(m, m, a, b, H[sel[a], sel[b]]), 2);
  [vector(m, i, cands[sel[i]]), G^(-1)]; };
coords(a, B) = { my(sel = B[1], Ginv = B[2], h = Mod(vectorv(#sel, j, hb(a, sel[j], pr_cur)), 2)); lift(Ginv * h); };
resv(a, p) = { my(v = []); for (k = 1, #PR[p], pr_cur = PR[p][k]; v = concat(v, Vec(coords(a, BAS[p][k])))); vectorv(#v, i, v[i]); };
realsym(a, b) = { my(sa = nfeltsign(bnf, lift(a)), sb = nfeltsign(bnf, lift(b)), s = 1); for (i = 1, #sa, if (sa[i] < 0 && sb[i] < 0, s = -s)); s; };
prodcheck(ntests) = { my(bad = 0);
  for (t = 1, ntests, my(a = Mod(sum(i = 0, 5, (random(9) - 4) * y^i), P), b = Mod(sum(i = 0, 5, (random(9) - 4) * y^i), P), s, pl);
    if (a == 0 || b == 0, next); s = realsym(a, b);
    pl = Set(concat([2], concat(factor(abs(nfeltnorm(bnf, a) * nfeltnorm(bnf, b)))[,1]~, factor(abs(bnf.disc))[,1]~)));
    foreach (pl, p, foreach (idealprimedec(bnf, p), pr, s *= nfhilbert(bnf, lift(a), lift(b), pr)));
    if (s != 1, bad++));
  print("product-formula check of nfhilbert on ", ntests, " random pairs: ", bad, " failures"); if (bad, error("nfhilbert inconsistent")); };
\\ ---------- local image of the curve at p by disc subdivision
\\ chart data: pol (polynomial in x), rootel (its root in L), cst (class of the chart constant, a coordinate vector)
inspan(v, W) = { if (#W == 0, return(vecmax(lift(Mod(v, 2))) == 0)); my(M = Mod(matconcat(W), 2)); matrank(matconcat([M, Mod(v, 2)])) == matrank(M); };
realok(w) = { my(sg = nfeltsign(bnf, lift(w)), v = vectorv(r1, i, sg[RPERM[i]] < 0)); for (j = 1, #RPTS, if (inspan(v - RPTS[j], [ALL1]), return(1))); 0; };
locok(w) = { my(v = resv(w, PCUR)); for (j = 1, #CLS, if (inspan(v - CLS[j], DIAG[PCUR]), return(1))); 0; };
addclass(lst, v, p) = { for (i = 1, #lst, if (inspan(v - lst[i], DIAG[p]), return(lst))); concat(lst, [v]); };
disc_image(a, n, pol, rootel, cst, p, depth) = {
  my(inside = List(), allok = 1, out = [], PRp = PR[p], prec = 80, v, ee, ok);
  if (depth > 40, error("disc recursion too deep"));
  for (k = 1, #PRp, my(pr = PRp[k]); ee = pr.e; v = idealval(bnf, lift(a - rootel), pr);
    if (pr.e * pr.f == 1 && v >= n, listput(inside, k); next);              \\ a Q_p-root of this factor lies in the disc
    ok = (ee * n - v > 2 * ee * valuation(2, p)); if (!ok, allok = 0));
  if (#inside >= 2 || !allok,
    for (b = 0, p - 1, out = concat(out, disc_image(a + b * p^n, n + 1, pol, rootel, cst, p, depth + 1))); return(out));
  if (#inside == 1,
    \\ the disc contains exactly one Q_p-Weierstrass x-coordinate; all points of the disc (and the Weierstrass point) have one class:
    \\ find any x in the disc, not the root, with pol(x) a nonzero square
    my(found = 0, xx);
    for (m = n, n + 6, for (u = 1, p^2, if (u % p == 0, next); xx = a + u * p^m; my(fx = subst(pol, x, xx)); if (fx != 0 && issquare(fx + O(p^prec)), found = 1; break)); if (found, break));
    if (!found, error("no point found near a Weierstrass point"));
    return([cst + resv(xx - rootel, p)]));
  \\ no root in the disc, class constant: points iff pol(a) is a square
  my(fa = subst(pol, x, a)); if (fa == 0, error("unexpected root"));
  if (issquare(fa + O(p^prec)), [cst + resv(a - rootel, p)], []); };
localset(p) = { my(cls = [], vecs, frev = polrecip(f), cstinf = resv(-th, p));
  vecs = disc_image(0, 0, f, th, 0 * resv(Mod(1, P), p), p, 0);
  foreach (vecs, v, cls = addclass(cls, v, p));
  vecs = disc_image(0, 1, frev, thinv, cstinf, p, 0);        \\ x = 1/u, u in pZ_p: x - theta = (-theta)(u - 1/theta) mod Q_p^*
  foreach (vecs, v, cls = addclass(cls, v, p));
  cls; };
{
W = setup(FPOL);
if (ISEMPTY, write("fs_result.txt", TAG, " W_empty_by_norm_condition"); print("done"); quit);
PR = vector(vecmax(SPRIMES)); BAS = vector(vecmax(SPRIMES)); DIAG = vector(vecmax(SPRIMES));
}
{
foreach (SPRIMES, p, PR[p] = idealprimedec(bnf, p); BAS[p] = vector(#PR[p], k, mkbasis(PR[p][k]));
  DIAG[p] = apply(q -> resv(Mod(q, P), p), if (p == 2, [-1, 2, 5], [p, nonres(p)])));
prodcheck(40);
}
{
\\ real place
RTH = []; for (i = 1, bnf.sign[1], RTH = concat(RTH, [real(subst(lift(th), y, bnf.roots[i]))]));
RPERM = vecsort(RTH, , 1); r1 = #RTH;
if (r1 >= 2,
  my(k0 = (pollead(f) < 0), pts = []);
  forstep (k = k0, r1, 2, pts = concat(pts, [vectorv(r1, i, i > r1 - k)]));
  ALL1 = vectorv(r1, i, 1);
  RPTS = pts; survivors = select(w -> realok(w), W);
  print("real place (", r1, " real roots): ", #W, " -> ", #survivors, " candidates"),
  survivors = W; print("real place: no real roots, no condition"));
}
{
foreach (SPRIMES, p, my(cls = localset(p));
  print("p = ", p, ": mu_p(C(Q_p)) has ", #cls, " classes (mod Q_p^*)");
  CLS = cls; PCUR = p; survivors = select(w -> locok(w), survivors);
  print("   candidates surviving: ", #survivors));
}
{
print("fake 2-Selmer set (computed with places S u {oo}): ", #survivors, " elements", if (#survivors == 0, "  =>  C(Q) is EMPTY", ""));
if (#survivors > 0 && #survivors <= 8, print("   representatives: ", apply(w -> lift(w), survivors)));
write("fs_result.txt", TAG, " |W|=", #W, " survivors=", #survivors, if (#survivors == 0, " C(Q)_EMPTY", " nonempty"));
}
\q
