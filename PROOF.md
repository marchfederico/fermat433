# The primitive solutions of x⁴ + 2y³ + z³ = 0

*Proof write-up, September 2026. All computations referred to are in this directory (scripts) and in `logs/`;
NOTE.md is the narrative companion, RESULTS.md the chronological record.*

## Theorem

The integer solutions of

  x⁴ + 2y³ + z³ = 0,  gcd(x, y, z) = 1,

are exactly (x, y, z) = (±1, 0, −1), (±1, −1, 1), (±43, −203, 237).

The proof has four parts: (A) a descent over Q(∛2) reducing the equation to rational points on six genus-2 curves;
(B) the four "easy" curves; (C) the two hard curves, B⁻: y² = −C₃(x) and C⁺: y² = 2C₃(x), where
C₃(x) = 17x⁶ − 72x⁵ + 90x⁴ + 40x³ − 180x² + 144x − 40, whose Jacobians have rank 2 = genus, handled by a
quadratic Chabauty argument whose extra Néron–Severi class is defined only over a field of degree 12; (D) the rank
bounds used in (C). Part (C) is the new contribution.

**Status of each part.** (A) proved here (exact arithmetic, including the twist set); (B) proved here (A⁻, B⁺, C⁻ by
the norm condition of the fake 2-Selmer set; A⁺ by a rank-1 Chabauty argument at the inert prime 5 through the
bielliptic quotients, plus a Mordell–Weil sieve); (C) proved here, conditional on the
theory cited in §3 and on the rank bounds; (D) rank J(Q) = 2 proved here for both curves by a 2-descent over Q, with the
implementation validated on 24 database curves. Nothing is imported any more; Villines' independent Magma results (June 2026) agree with ours throughout.

Throughout, ι denotes the hyperelliptic involution (x, y) ↦ (x, −y).

## A. Reduction

Let θ = ∛2, K = Q(θ). K has class number 1 (bnfcertify), fundamental unit ε = θ − 1 of norm 1, and 2 and 3 are
totally ramified.

**Lemma A.1.** For a primitive solution, gcd(y, z) = 1, and α := z + yθ satisfies N_{K/Q}(α) = z³ + 2y³ = −x⁴.
The three conjugates of α are pairwise coprime away from the primes above 2 and 3, and primitivity forces the
common factors there to be trivial; hence (α) = 𝔞⁴ for an ideal 𝔞, and since h_K = 1 and O_K^× = ⟨−1, ε⟩,
α = ±ε^k γ⁴ with γ ∈ Z[θ], k ∈ {0, 1, 2, 3}; absorbing signs into γ⁴ is impossible, but replacing (x, y, z) by
(x, y, z) with x ↦ ±x shows the sign can be normalised to α = −ε^k γ⁴. *(descent_explore.py; the ideal argument
is the standard one for norm forms of cubic fields.)*

**Lemma A.2.** Writing γ = a + bθ + cθ² and expanding −ε^k γ⁴, the coefficient of θ² must vanish; this is a
plane quartic C_k(a, b, c) = 0 over Q (genus 3, smooth). Primitivity forces γ to be a unit at the primes above 2
and 3, i.e. a odd and a + 2b + c ≢ 0 (mod 3). C₃ has no 2-adic points; C₂ has no 2-adic points with a odd. Hence
every primitive solution comes from a rational point on C₀ or C₁ satisfying the unit conditions, with x = N(γ) and
z + yθ = −ε^k γ⁴. *(descent_explore.py, diagonal.py; explicit equations in RESULTS.md.)*

**Lemma A.3 (étale double covers and the twist set).** Let δ = γ². The condition "[θ²](−ε^k δ²) = 0" is a
smooth conic Q_k(d₀, d₁, d₂) = 0 in the coordinates of δ = d₀ + d₁θ + d₂θ² (Gram determinant 1 for both k), with the
rational point (1 : 0 : 0). Parametrising by the lines through this point,

  k = 0: Q₀ = −d₁² − 2d₀d₂,  δ₀(s, t) = (s², −2st, −2t²),  f₀(s, t) = N(δ₀) = s⁶ − 40s³t³ − 32t⁶;
  k = 1: Q₁ = d₁² − 2d₀d₁ + 2d₀d₂ − 2d₂²,  δ₁(s, t) = (2t² − s², 2s(t − s), 2t(t − s)),  f₁(s, t) = −t⁶C₃(s/t).

Every rational point of the conic is δ_k(s : t) for a unique (s : t) ∈ P¹(Q); with (s, t) coprime integers,
δ = μ·δ_k(s, t) for a unique μ ∈ Q^×, and taking norms, μ f_k(s, t) = (N(γ)/μ)². Thus every point of C_k(Q) gives a
rational point (s/t, N(γ)/(μt³)) on H_μ: w² = μ f_k(x, 1), and the point of C_k is recovered from it (δ = μδ_k(s,t),
γ = √δ). *The twist class of μ:* (i) for coprime (s, t) the content of δ_k(s, t) is 1 if s is odd and 2 if s is even:
an odd prime dividing all three coordinates would divide s and t (k = 0: it divides s² and 2t²; k = 1: it divides
2s(t − s) and 2t(t − s), hence t − s, hence 2t² − s² ≡ t²), and modulo 4 the coordinates are (s², 2st, 2t²),
resp. (2t² − s², …) with the other two even. (ii) γ² is primitive: γ is primitive, and if p divided all
coordinates of γ² then γ would be nilpotent in Z[θ]/(p), which for p ∤ 6 is reduced, while for p = 2, 3 the
nilpotents are (θ) and (θ + 1), excluded by the unit conditions a odd and a − b + c ≢ 0 (mod 3) of Lemma A.2.
Hence μ = ±1/content(δ_k(s, t)) ∈ {±1, ±1/2}. (iii) For k = 0 the θ⁰-coordinate of δ = γ² is a² + 4bc, odd, while
that of μ δ₀(s, t) is μs²; so s is odd, the content is 1 and μ = ±1. For k = 1 both contents occur. Therefore
every primitive solution gives a rational point on one of exactly six curves:

  k = 0, μ = ±1: A±: y² = ±(x⁶ − 40x³ − 32);
  k = 1, μ = ±1: B∓: y² = ∓C₃(x);  k = 1, μ = ±1/2: C∓: y² = ∓2C₃(x)  (multiply w² = ±½f₁ by 4),

with C₃(x) = 17x⁶ − 72x⁵ + 90x⁴ + 40x³ − 180x² + 144x − 40. These are Villines' six curves. *(twistset.py, which also
checks the content and primitivity claims numerically; etale.py maps the known points: (0,1,0), (1,0,−1), (1,0,0)
on C₀ go to (0 : 1) and (1 : −1), (1 : 0) on A⁺ [x = 0 gives w² = −32, not a point of A⁺ but of A⁻·(1/2)… see below],
and (1,−2,0), (1,0,0) on C₁ to (−1, ±15), (1, ±1) on B⁻, (1,−1,2), (1,1,0) to (6/5, ±172/125), (2, ±12) on C⁺;
(6/5, ±172/125) is the 43-solution.)*

*Remark.* The sign of μ is the sign of f_k(s, t); the point of C₀ with γ = θ (δ = θ², (s, t) = (0, 1)) has s even and
is excluded by the unit condition a odd — it corresponds to the imprimitive solution (x, y, z) = (2·…) — so the
content-2 chart for k = 0 (which would land on the twists y² = ±2(x⁶ − 40x³ − 32)) never arises from primitive
solutions.

## B. The four other curves

**Proposition B.1.** A⁻, B⁺ and C⁻ have no rational points.

*Proof.* Let C: y² = f(x) be one of them, f₆ ∈ {−1, 17, −34} its leading coefficient, L = Q[x]/(f) (the field
L_A ≅ Q[y]/(y⁶ − 3y⁴ − 2y³ + 3y² + 6y + 1) for A±, L₆ ≅ Q[y]/(y⁶ − 3y⁴ + 3y² − 3) for B±, C±; both of class number 1,
certified by bnfcertify), θ the image of x, and S = {2, 3} resp. {2, 3, 17}, the primes dividing 2·disc(f)·f₆.
f has no rational root and f₆ is not a square, so C has no Weierstrass or infinite rational points; for an affine
point (x, y) ∈ C(Q), N_{L/Q}(x − θ) = f(x)/f₆ = y²/f₆ ≡ f₆ (mod Q^{×2}), and the class of x − θ in L^×/L^{×2}Q^× is
unramified outside S (Bruin–Stoll Lemma 4.3: for p ∉ S, f is squarefree mod p with unit leading coefficient, so x
mod p is a root of exactly one (linear) factor of f mod p, one prime 𝔭 | p divides x − θ, and v_𝔭(x − θ) =
v_p(y²/f₆) is even; if v_p(x) < 0 then (x − θ)/x ≡ 1 mod every prime above p). Multiplying by an element of Q^×
changes the norm by a sixth power, so there would be an S-unit δ of L with N(δ) ∈ f₆Q^{×2}. But the norms of the
S-units modulo squares span the subgroup ⟨−2, −3⟩ of Q(S, 2) for L_A and ⟨−2, −3, −17⟩ for L₆
(sel2/certify.gp, logs/sel2/certify.log), which contain −1 (A⁻), 17 (B⁺), −34 (C⁻) in no case — while they do contain
−17 (B⁻) and 34 (C⁺), as they must. Hence C(Q) = ∅. □

This is the emptiness of the fake 2-Selmer set of Bruin–Stoll (their step 7) and reproduces Villines' result;
sel2/fakeselmerset.gp implements the full fake Selmer set (norm condition, real place, and the exact local images
μ_p(C(Q_p)) by recursive subdivision of p-adic discs) and returns W = ∅ for these three curves at the norm step.

**Proposition B.2.** A⁺(Q) = {∞±, (−1, ±3)}.

*Proof.* (a) *Rank.* f = x⁶ − 40x³ − 32 is irreducible, so J(Q)[2] = 0, and sel2/pipeline.gp (logs/aplus/descent_Aplus.log)
gives dim Sel²(J/Q) = 1 (the sextic field L_A has the quadratic subfield Q(√3), since f = (x³ − 20)² − 432, so here
Sel² = Sel²_fake), whence rank J(Q) ≤ 1. The class D = [(−1, 3) − ∞₊] has infinite order (its images on the elliptic
quotients below have infinite order, ellorder over M), so rank J(Q) = 1. The torsion subgroup is Z/3, generated by
T = [∞₋ − ∞₊]: gcd of #J(F_ℓ) over 5 ≤ ℓ < 400 is 3, and T has order 3.

(b) *Bielliptic structure.* Since f(c/x) = −32f(x)/x⁶ for c³ = −32, X has the involution τ(x, y) = (c/x, 4√−2·y/x³) over
M = Q(∛2, √−2) = Q(⁶√−2) (w⁶ = −2, ∛2 = −w², √−2 = −w³, c = −2w⁴), with fixed points x± = ±w⁵. In the coordinates
X = (x − x₊)/(x − x₋), Y = y(1 − X)³ the curve is Y² = F₀(X) = AX⁶ + BX⁴ + CX² + D with A = −64 + 160w³,
B = −960 − 480w³, C = −960 + 480w³, D = −64 − 160w³ (coefficients in Q(√−2)), and τι is (X, Y) ↦ (−X, Y). The quotients
E₁: v² = u³ + Bu² + ACu + A²D (φ₁ = (AX², AY)) and E₂: v² = u³ + Cu² + BDu + AD² (φ₂ = (D/X², DY/X³)) have j = 8000
(CM by Z[√−2]), conductor of norm 9 over M, E_i(M)_tors ≅ Z/6, and E₂ is the quadratic twist of E₁ by −2. J is
isogenous to E₁ × E₂ over M (aplus/bi_Aplus.gp).

(c) *Chabauty at p = 5.* 5 is inert in Q(√−2) and has three primes of degree 2 in M; fix 𝔭 | 5, M_𝔭 = Q₂₅ = Q₅(√2). Let
L_i(z) = Log_{E_i,𝔭}(φ_i(z)) ∈ Q₂₅ be the formal-group logarithms (computed from the formal group law of the a₁ = a₃ = 0
model, after multiplication by #E_i(F₂₅) = 36; aplus/chab5_Aplus.gp). The differentials φ_i^*ω_{E_i} form a basis of
H⁰(X_M, Ω¹), so for z ∈ X(Q), with [z − ∞₊] = λD + εT, λ ∈ Q, ε ∈ Z/3 (Log(T) = 0):
  (L₁(z), L₂(z)) = λ·(L₁(D), L₂(D)) with λ ∈ Q₅,  where L_i(D) := L_i((−1, 3)) (Log(∞₊) = 0).
Consistency: at (−1, ±3) this holds with λ = ±1 exactly (to O(5⁴⁴)), and ρ(z) := L₂(D)L₁(z) − L₁(D)L₂(z) vanishes at all
four known points. On each of the six residue discs of X(Q₅) (x ≡ 1, 4 mod 5 with two signs of y, and the two discs at
infinity) we expand L_i along the disc by termwise integration of φ_i^*ω_{E_i} (tiny integrals) and solve ρ = 0. Because
E₂ ≅ E₁ over Q₂₅, the Q₅-component of ρ vanishes identically and the condition is the √2-component; its Strassman
indices are 1, 1, 2, 2, 1, 1, giving exactly 8 zeros in X(Q₅), each with λ ∈ Q₅:
  ∞±, (−1, ±3) (λ = 0, 0, ±1);  (−2∛2, ±12√6), λ = 0, a torsion class of order 3 (verified exactly over Q(⁶√−2, √−3),
  aplus/tors12.gp, so no rational point lies in its disc, the disc having a unique zero);  and one pair z₁, ιz₁ in the disc
  x ≡ 1 (mod 5) with λ ≡ ±8316 (mod 5⁶), λ ≢ 0, ±1 (mod 25).
(d) *Sieve.* A rational point z in the disc x ≡ 1 would have λ(z) = n/m ∈ Q with 5 ∤ m: the logarithms of
E_i(Q₂₅) have valuation ≥ 1 (formal group, and #E_i(F₂₅) = 36 is a 5-unit) while L_i(D) has valuation exactly 1, so if
D = mG for a generator G then 5 ∤ m. Hence for every prime 𝔮 of M with 5^k | #E_i(F_𝔮), the 5-primary parts satisfy
π_i(φ_i(z̄) − φ_i(∞₊)) = λ(z)·π_i(φ_i(D̄)) in E_i(F_𝔮) (the torsion class T has order 3), with λ(z) ≡ λ(z₁) (mod 5⁶) if
z lies in the disc of z₁. aplus/sieve5_Aplus.gp enumerates A⁺(F_q) and collects the residues λ mod 5⁴ realised by its
points: at the three degree-2 primes above q = 149 (#E_i(F_𝔮) = 22500 = 2²·3²·5⁴) 175 of 625 residues occur, and at a
degree-2 prime above q = 599 (#E_i = 360000 = 2⁶·3²·5⁴) 275 of 625; the residues 0, ±1 of the known points occur at both,
while λ(z₁) ≡ 191 and λ(ιz₁) ≡ 434 (mod 625) do not occur at q = 599 (logs/aplus/sieve5.log). So the disc x ≡ 1 contains no
rational point. The discs x ≡ 4 have Strassman index 2 and contain the two exhibited zeros (−1, ±3) and (−2∛2, ±12√6),
the discs at infinity have index 1 and contain ∞±.
Hence X(Q) = {∞±, (−1, ±3)}. □

*Remarks.* (i) At a prime split in Q(√−2) (we first used p = 43, aplus/linchab_Aplus.gp) the same computation has 66
zeros: the 4 rational points, 12 algebraic points with torsion classes (x³ = 2, x³ = −16, over Q(⁶√−2, √−3); exact orders 3
and 6, aplus/tors12.gp), and 50 others of which the 43-part sieve (aplus/sieve_Aplus.gp) removes all but 14 — the survivors
include the Q(√−2)-points (2, ±12√−2), (±2√−2, ±(16 ± 20√−2)), whose classes have 43-adic logarithms on the line of J(Q)
because the CM action of Z[√−2] on E_i commutes with the 43-adic logarithms when 43 splits in Q(√−2): Chabauty at a split
prime sees J(Q(√−2)) rather than J(Q). This is why the inert prime 5 (Villines' choice) is the right one. (ii) The
formal-group logarithms and the group law over Q₂₅ are written out in aplus/chab5_Aplus.gp, since PARI's ellpadiclog is
restricted to Q_p.


## C. The hard pair

Let X be B⁻ (the argument for C⁺ is identical with the twisted data; all numbers below are for B⁻ unless stated).
X has the rational points P₁ = (1, 1), P₂ = (−1, 15) and their ι-images; J = Jac(X).

### C.1 Structure

**Proposition C.1.** (i) Aut(X_Q̄) ≅ GL₂(F₃), of order 48; X is a Q-twist of the Bolza curve y² = x⁵ − x.
(ii) The Möbius maps permuting the six roots of C₃ form S₄; nine of them are involutions; the six that lift to
involutions τ of X are x ↦ (−x + b)/(cx + 1) with 81b⁶ − 540b⁵ + 1494b⁴ − 2240b³ + 1980b² − 1008b + 232 = 0, the
lift being (x, y) ↦ (μ(x), κs·y/(cx + 1)³), κ = 1 + bc, s² = κ. (iii) The Möbius parts are defined over
K₆ = Q(∛2, √(∛2 − 1)) and the involutions over L = K₆(√κ), a field of degree 12, signature (2, 5),
discriminant 2²⁸3¹³, class number 1, in which 2 is totally ramified and 3 = 𝔭₁³𝔭₂⁶𝔭₃³. (iv) Over L, X is
bielliptic: with x± = (−1 ± s)/c the fixed points of μ, X = (x − x₊)/(x − x₋), Y = y(X − 1)³, the curve becomes
Y² = F(X) = AX⁶ + BX⁴ + CX² + D with A = f(x₋), D = f(x₊), and τ(X, Y) = (−X, Y). The quotients
E₁: Y'² = X'³ + BX'² + ACX' + A²D (via φ₁ = (AX², AY)) and E₂: Y'² = X'³ + CX'² + BDX' + AD² (via
φ₂ = (D/X², DY/X³)) have j = 8000 (CM by Z[√−2]), global minimal models over L with minimal discriminants
supported on the prime above 2 and one prime above 3, and E_i(L)_tors ≅ Z/2.

*Proof.* Exact computation: invol.gp finds the 24 Möbius maps numerically and invol4.gp/invol8.gp identify them
exactly by resultants (the nine involutory maps have b a root of (b³ − 18b² + 36b − 20)·(81b⁶ − …)·(−C₃(b)); the
last factor is spurious); λ/(1+bc)³ = +1 for the six genuine involutions and −1 for the three order-4 lifts
(invol4.gp). Fields, discriminants, class numbers, minimal models and torsion: invol8.gp, step2a.gp. □

**Proposition C.2 (Galois action on NS).** Let M = N·F where N is the S₄-field (Galois closure of
Q(∛2, ω, √(−1 − ∛2))) and F = Q(√−2); [M : Q] = 48, Gal(M/Q) ≅ S₄ × Z/2, and
NS(J_Q̄) ⊗ Q ≅ 1 ⊕ (sgn_F ⊗ sgn ⊗ std). In particular ρ(J/Q) = 1, ρ(J/F) = 1, and complex conjugation has
eigenvalues (1, 1, 1, −1): exactly one anti-invariant class, the class Z = τ_* of an involution, defined over L.

*Proof.* Frobenius traces (nschar2.gp): every prime inert in F has trace 0, so V_ℓ(J) = Ind_F^Q ψ; at split primes
the Frobenius polynomial factors over F but over Z only when even, so End⁰_F(J) = F, whence ρ(J/F) = 1 (the Rosati
involution on an imaginary quadratic field is conjugation). The traces of Frobenius on NS(J_Q̄) ⊗ Q_ℓ (the
root-of-unity eigenvalues among α_iα_j/p; at inert primes the 2-dimensional transcendental part contributes 0) depend
only on the splitting of p in F and N and give the stated character; the class densities match the orders of the
conjugacy classes (RESULTS.md table). The element (transposition, σ_F) is complex conjugation and has trace 2. □

### C.2 The identity

**Theorem (Balakrishnan–Dogra).** [BD, *Quadratic Chabauty and rational points II*, IMRN 2021, Prop. 2; quoted
in Dogra, *Unlikely intersections and the Chabauty–Kim method over number fields*, remark after Prop. 1.1]
For X/Q of genus g with Jacobian J, the depth-2 Chabauty–Kim set X(Q_p)₂ is finite whenever
rk J(Q) < g − 1 + rk NS(J) + rk NS(J_Q̄)^{c=−1}. Here 2 < 2 − 1 + 1 + 1.

**Theorem (Balakrishnan–Besser–Bianchi–Müller).** [BBBM, *Explicit quadratic Chabauty over number fields*, Israel J.
Math. 2021, Thm. 1.5] For a bielliptic genus-2 curve over a number field L with quotients E₁, E₂ and any non-trivial
continuous idele class character χ: A_L^×/L^× → Q_p, the function
ρ^χ(z) = Σ_{𝔭|p} (h^χ_𝔭(φ₁(z_𝔭)) − h^χ_𝔭(φ₂(z_𝔭)) − 2χ_𝔭(x(z_𝔭))) − Σ α q₁(φ₁(z)) + Σ β q₂(φ₂(z))
maps X(L) into an explicitly computable finite set T^χ.

We apply BBBM's theorem to X_L, restricted to X(Q) ⊂ X(L), with a specific χ. The role of BD's term
rk NS(J_Q̄)^{c=−1} is that for z ∈ X(Q) all Galois-conjugate places contribute the same local terms, so the
identity survives on Q-points only for pairs (class, character) lying in the same Galois-isotypic component; the
cyclotomic character pairs with the trivial component and gives 0 = 0.

**Proposition C.3 (the character).** Let p = 499, the smallest prime splitting completely in M. Under the twelve
embeddings σ_i: L → Q_p, the involutions act on H⁰(X, Ω¹) (basis dx/y, x dx/y) by A_i = s_i⁻¹[[−1, −c_i],[−b_i, 1]].
Because H⁰(Ω¹) is one of the two CM eigenspaces of Frobenius on H¹_dR, NS(J) ⊗ Q_p ≅ M₂(Q_p) through this action
and the A_i span sl₂, the non-trivial 3-dimensional part. Let R ⊂ Q_p¹² be the orthogonal complement of
ker((c_i) ↦ Σ c_iA_i) (dimension 3, the isotypic component of sgn_F ⊗ sgn ⊗ std in the permutation representation on
the places above p). The six fundamental units of L have p-adic logarithms of rank 6 meeting R in a 2-dimensional
space. Hence there is, up to scalar, exactly one idele class character χ_Z of L with local components at the
places above p in R: χ_Z = (c_1, …, c_{12}) with c_1 = 1, extended to all places by class number 1
(χ_w(π_w) = Σ_i c_i log_p σ_i(α_w) for a generator α_w). Moreover **χ_Z vanishes at the uniformisers of every prime
above 2 and 3.**

*Proof.* step1_character.gp: ker has dimension 9, R dimension 3, R ⊥ (1, …, 1), unit logs of rank 6,
dim(R ∩ span(unit logs)) = 2; the values at the four uniformisers are O(499³⁰). □

**Proposition C.4 (the identity).** Let D₁ = [P₁ − ιP₁], D₂ = [P₂ − ιP₂] ∈ J(Q); their images φ₁(P_i) on E₁ have
independent p-adic logarithms, so D₁, D₂ span J(Q) ⊗ Q (rank ≥ 2; rank = 2 by §4). Write, for z ∈ X(Q),
[z − ιz] = a₁D₁ + a₂D₂ in J(Q) ⊗ Q, and let G_ij = ⟨φ₁P_i, φ₁P_j⟩_χ − ⟨φ₂P_i, φ₂P_j⟩_χ (χ_Z-height pairings on
E₁(L), E₂(L)). Then for every z ∈ X(Q),

  ρ(z) := Σ_{i=1}^{12} c_i[λ_i(φ₁z) − λ_i(φ₂z)] − 2 Σ_i c_i log_p σ_i(X(z)) − a(z)ᵀ G a(z) = −Ω₃₉₇,

where λ_i is the canonical (Mazur–Tate) local height at the i-th place above p on the b-model of E_k, and Ω₃₉₇ is
the constant 2χ'_{w₁}(π) − 2χ'_{w₂}(π) for the two degree-1 primes above 397 (defined in the proof).

*Proof.* Since φ₁(z) = a₁Q₁ + a₂Q₂ + T with T ∈ E₁(L)[2] and heights kill torsion, h_χ(φ₁z) − h_χ(φ₂z) = aᵀGa.
Decompose h_χ into local terms: at the twelve places above p, c_wλ_w(Q) + d_w m_w(Q) (m_w = max(0, −v(x(Q)))) ;
at a place w ∤ p of good reduction of the minimal model, χ'_w(π_w)m_w(Q); at the places above 2 and 3 nothing, by
Prop. C.3. On the natural quotient models x(φ₁z) = AX², x(φ₂z) = D/X², so at places w not above 2, 3, 397 (where
A, D are units and the models minimal), m_w(φ₁z) − m_w(φ₂z) = −2v_w(X(z)); the same holds at w | p. Summing
χ'_w(π_w)·(−2v_w(X(z))) over w ∤ p and using that χ_Z kills the global element X(z) ∈ L^× gives
−2Σ_i c_i log σ_i(X(z)) + 2Σ_i d_i v_p(σ_iX(z)); the d_i-terms cancel against the d_i(m_i(φ₁z) − m_i(φ₂z)) terms.
What remains is the contribution of the two primes above 397, where the natural models are non-minimal.
*Lemma.* At each such w, with v(u₁) = −2, v(u₂) = −1 the scalings to the minimal models (discriminant exponents
−24, −12), v_w(A) = −6 at one prime and v_w(D) = −6 at the other, one has, on the minimal models,
m_w(φ₁z) − m_w(φ₂z) + 2v_w(X(z)) = +2 at the first prime and −2 at the second, for every 397-adic point z
(case analysis on v_w(X): for v ≤ 0, m_w(φ₁) = 2 − 2v, m_w(φ₂) = 0; for v = 1 both vanish; for v ≥ 2,
m_w(φ₁) = 0, m_w(φ₂) = 2v − 2). Hence the correction is the stated constant. Numerically, ρ(P_k) + Ω₃₉₇ = O(499¹⁹)
at both known points, and the opposite sign of the log term fails (step2b.gp). □

The heights were computed as follows (step2b.gp): E_k ⊗_{σ_i} Q_p replaced by an integer model congruent to it
modulo 499³⁰ (so PARI's ellpadics2 gives the sigma constant); σ from the formal group; ψ_m(Q), m = #E(F_p) = 514,
by the classical recurrences, calibrated by log σ(kQ₀) − k² log σ(Q₀) = log ψ_k(Q₀) to O(499¹⁹);
λ(Q) = −(2/m²)(log σ(mQ) − log ψ_m(Q)). **Validation:** the χ_Z-height satisfies the parallelogram law on both
quotients to O(499¹⁹) and h(2Q₁) = 4h(Q₁).

### C.3 Zeros and sieve

**Proposition C.5.** ρ extends to a locally analytic function on X(Q_p) (on the disks where some σ_i(X(z)) tends to
0 or ∞ the singular pair of terms is replaced by its analytic form 2c_i[log(s/X) + v(s)], s the formal parameter,
as in Bianchi–Padurariu, Remark 2.5). On each of the 528 residue disks of X(Q₄₉₉) (no Weierstrass disks: C₃ has no
root mod 499), expanded to O(T¹⁴) with 14-digit coefficients, ρ has Strassman index 2 with coefficient valuations
[·, 1, 1, 2, 3, …]; the Z₄₉₉-roots of the truncated series are 524 in number for B⁻ (262 disks with two, 266 with
none) and 504 for C⁺. Recomputation with 20 digits and O(T²⁰) reproduces the roots to 8 digits and the counts, the
valuations continuing linearly, so the truncation loses nothing. ρ vanishes to O(499¹³) at the known points.
*(step3_*.gp; logs/step3_disks.txt; logs/step3_precision_check.log.)*

**Proposition C.6 (sieve).** Every point of J(Q₄₉₉) has a 499-integral coefficient vector a (all logarithms lie in
499Z₄₉₉ and the log matrix of Q₁, Q₂ has determinant of valuation 2). Hence [J(Q) : ⟨D₁, D₂⟩ + torsion] is a
499-unit, and for a degree-1 prime 𝔮 of L above q with 499 | #E₁(F_𝔮) = #E₂(F_𝔮), projecting to the 499-parts
ξ: E_k(F_𝔮) → Z/499, a rational point z must satisfy ξ(a(z)·(Q̄, Q̄')) ∈ {ξ(φ₁(w), φ₂(w)) : w ∈ X(F_q)} ⊂ (Z/499)²,
with no torsion or index ambiguity (2-torsion translates and unit indices vanish mod 499). Such primes: four above
997 (#E = 998), four above 12973, two above 47903, two above 59879, twelve above 88339. The first prime above 997
eliminates 518 of the 524 zeros on B⁻ (494 of 504 on C⁺), the primes above 12973 the rest except four; the four
survivors are the four known points, on each curve. *(step4_scan.gp, step4_sieve.gp; logs/step4_sieve.log.)*

**Second prime (independent check of C.3–C.6).** The whole computation was repeated at p = 1459, the next prime that
splits completely in L and at which C₃ has no root (second_prime/make_p1459.py; logs/p1459/). The character is again
unique in its isotypic component and vanishes at the uniformisers above 2 and 3; the χ_Z-heights satisfy the
parallelogram law to O(1459¹⁹); ρ(P₁) = ρ(P₂) = −Ω₃₉₇ to O(1459¹⁹) on both curves; #E_k(F_𝔭) = 1462 at all twelve
places (ordinary reduction). Each curve has 1464 residue disks, all with Strassman index 2 except the two disks at
infinity (index 1); ρ has 1546 zeros on B⁻ and 1426 on C⁺. The sieve primes are the degree-1 primes of L above
q = 2917, 26261, 96293 (all ≡ −1 mod 1459, with #E₁(F_𝔮) = #E₂(F_𝔮) = q + 1); the first prime above 2917 removes
1538 of the 1546 zeros on B⁻ and 26261 the rest but four; the four survivors are the known points. On C⁺ the same
primes leave the four known points plus the two zeros of each of the two disks x ≡ 103 (mod 1459), whose coefficient
vectors had come out with no significant digits in the 14-digit run (the logarithms at places 1, 2 lose all precision
on that disk); recomputing those disks with 22 digits (logs/p1459/Cplus/disk103.log, fix103.log, fix103b.log) gives the
same two zeros to five digits and ordinary coefficient vectors a ≡ (243, 104), (1453, 735), (1216, 1355), (6, 724)
(mod 1459), which the prime above 2917 removes (sieve103.out). So at p = 1459 too, B⁻(Q) and C⁺(Q) are exactly the
four known points each.

**Corollary C.7.** B⁻(Q) = {(1, ±1), (−1, ±15)} and C⁺(Q) = {(2, ±12), (6/5, ±172/125)}, given rank J(Q) = 2
for both Jacobians.

## D. The rank bounds

**Proposition D.1.** For X = B⁻: J(Q)[2] = 0 and dim_{F₂} Sel²(J/Q) = 2. Hence rank J(Q) ≤ 2, so rank J(Q) = 2 and
Ш(J/Q)[2] = 0.

**Proposition D.2.** The same holds for X = C⁺.

*Proof.* Write f for the sextic (−C₃ for B⁻, 2C₃ for C⁺), L₆ = Q[x]/(f) the sextic field, θ the image of x. L₆ has
class number 1, signature (2, 2) and Galois group 2 ≀ S₃ (order 48); it has no quadratic subfield (nfsubfields).

*(a) Torsion.* J[2](Q̄) is the group of even-cardinality subsets of the roots of f modulo complement; a Q-rational
2-torsion point is a Galois-stable such subset, i.e. a union of irreducible factors. f is irreducible, so J(Q)[2] = 0.

*(b) The fake Selmer group.* Let H = ker(N: L₆^×/L₆^{×2}Q^× → Q^×/Q^{×2}). The map D = Σ n_P P ↦ Π(x_P − θ)^{n_P}
induces the homomorphism x − T: J(Q) → H (and likewise over every completion Q_v), and the fake 2-Selmer group is
Sel²_fake(J) = {δ ∈ H : δ_v ∈ (x − T)(J(Q_v)) for all v} (Poonen–Schaefer §12–13; Stoll 2001 §5). It is a quotient
of the true Selmer group: there is an exact sequence μ₂ → Sel²(J) → Sel²_fake(J) → 0 (Stoll–van Luijk, *Explicit
Selmer groups for cyclic covers of P¹*, Acta Arith. 159 (2013), §5, and [PS, Thm. 13.2] for the injectivity of the
first map). Hence
  dim Sel²(J) ≤ dim Sel²_fake(J) + 1.
(Here the inequality is in fact an equality: the first map is injective iff f has no odd-degree factor over Q and is
not a constant times a product of two conjugate cubics over a quadratic field [PS 13.2, quoted as Prop. 3.3 of
Bruin–Stoll], which is the case, and the image of μ₂ is the class of [P − ιP] for any rational point P, which is a
Selmer element; only the inequality is used.)

*(c) Local images.* For v finite let m_v be the number of irreducible factors of f over Q_v and o_v ∈ {0, 1}
indicate an odd-degree factor. Then dim J(Q_v)[2] = m_v − 1 − o_v (the same count as in (a)) and
dim J(Q_v)/2J(Q_v) = d_v := dim J(Q_v)[2] + 2·[v = 2]. The kernel of x − T on J(Q_v)/2J(Q_v) is generated by the
class c_v of [P − ιP], P ∈ X(Q_v), which is independent of P (the difference of two such classes is 2[P − P']), and
c_v = 0 iff the canonical class κ is twice a Q_v-rational degree-1 class, i.e. iff one of the 16 theta
characteristics (the six [w_i] and the ten [w_i + w_j − w_k], one for each partition of the Weierstrass points into
two triples) is Galois-invariant, i.e. iff o_v = 1 or all local factors of f have a common quadratic subfield
Q_v(√d) (then the two orbits of Gal(Q̄_v/Q_v(√d)) on the roots of each factor assemble into a stable partition into
triples). Writing ε_v = 1 in the remaining case, the image (x − T)(J(Q_v)) has dimension exactly d_v − ε_v; the
computation below generates it by Q_v-points and conjugate pairs of quadratic points and stops when this dimension
is reached, so the local conditions imposed are exactly the fake Selmer conditions. At the real place the image is
given by sign vectors (Bruin–Stoll §5) and is trivial when f has two real roots, as here. At primes p ∤ 2·disc(f)
the image is the unramified subgroup, so Sel²_fake(J) ⊆ H(S) := {δ ∈ H : v_𝔭(δ) even for 𝔭 ∤ S} for
S ⊇ {p | 2 disc(f)} = {2, 3}; we used S = {2, 3, 17} (17 divides the leading coefficient; harmless).

*(d) Computation* (sel2/pipeline.gp; logs/sel2/descent_Bminus.log, descent_Cplus.log). L₆ is taken in a reduced
model (polredbest; this matters: in the model c⁵f(y/c) PARI's local Hilbert symbols at the primes above 2 are
unreliable, see RESULTS.md). H(S) is computed from the S-units (class number 1) as the norm-square subgroup of
L₆(S, 2) modulo the image of Q(S, 2), with an assertion that the exponent vectors reconstruct −1 and the primes of
S. Local square classes at 𝔓 | p are coordinates with respect to a basis of L₆,𝔓^×/L₆,𝔓^{×2} chosen by the rank of
the Hilbert pairing matrix (nfhilbert), and the local symbols are checked against the product formula on 60 random
pairs. For B⁻: dim H(S) = 2. At p = 3, f is irreducible over Q₃ and 3 is a square in L₆ ⊗ Q₃: d = 0, ε = 0, image 0.
At p = 17: factors of degrees 1, 1, 4, d = 1, ε = 0, image of dimension 1 from Q₁₇-points. At p = 2: f irreducible
over Q₂ and no non-square of Q₂ becomes a square in L₆ ⊗ Q₂: d = 2, ε = 1, image of dimension 1, generated by
conjugate pairs of quadratic points (72289 pairs tested; the Q₂-points give nothing). The subgroup of H(S)
satisfying the three conditions has dimension 1, so dim Sel²_fake(J) = 1 and dim Sel²(J) ≤ 2. Since rank J(Q) ≥ 2
(the independent points of §C.3) and J(Q)[2] = 0, dim Sel²(J) = 2 and Ш[2] = 0. For C⁺: dim H(S) = 2, the same
local data (image 1 at 2 from 151 quadratic pairs, 0 at 3, 1 at 17), dim Sel²_fake = 1, dim Sel² = 2. □

**Validation of the implementation.** The pipeline was run on 24 curves of the Booker–Sijsling–Sutherland–Voight–
Yasaki database with rational points and irreducible sextic models (sel2/validation_curve_*.gp; scorecard in
RESULTS.md and logs/sel2/validation_scorecard.txt). For a curve with a rational point and no 2-torsion,
dim Sel²(J) = rank J(Q) + dim Ш[2] with dim Ш[2] even (Poonen–Stoll), so dim Sel² ≥ rank with equality iff Ш[2] = 0.
On all 24 curves the computed dim Sel² equals the database's analytic rank — including curves with four real roots,
class groups Z/2 and Z/3, a quadratic subfield, and ranks 1, 2, 3. (Two curves with leading coefficient 4, a 2-adic
square, needed the Q₂-points near infinity, x with denominator up to 2⁹, to complete the 2-adic local image; the
pipeline searches that chart when the standard search falls short, and flags any image that stays incomplete, in which
case its output is only a lower bound.) Three earlier bugs (the exponent ordering of
bnfissunit, the Hilbert symbols in the non-reduced model, an empty local image at a prime with trivial target) had
produced rank + 1 on ten curves, which the parity of dim Ш[2] rules out; that is how they were found. (An earlier
version of this text compared with a quantity mislabelled as the database's 2-Selmer rank; the raw data file
contains the analytic rank, and that is what the comparison is.)

## E. Conclusion

By A, every primitive solution gives a rational point on one of the six curves; by B the four easy
curves contribute only (±1, 0, −1); by C and D, B⁻(Q) and C⁺(Q) consist of the known points, which give
(±1, −1, 1) (from (1, ±1)), an imprimitive point (from (−1, ±15) and (2, ±12)), and (±43, −203, 237) (from
(6/5, ±172/125)). This proves the theorem, subject to the
cited theorems of Balakrishnan–Dogra and BBBM, the standard theory of Coleman integration used in B.2 and C, and the theory of p-adic heights on elliptic curves
over number fields (Mazur–Tate; the sigma-function local heights used here were validated against PARI's canonical
heights over Q in the parallel session's qc_sigma.py). The p-adic computations carry PARI's rigorous precision
tracking; the only truncation is the series tail on each residue disk, controlled by the observed linear growth of
coefficient valuations and confirmed at higher precision.

## References

- J. S. Balakrishnan, N. Dogra, *Quadratic Chabauty and rational points II: Generalised height functions on Selmer
  varieties*, IMRN 2021 (arXiv 1705.00401).
- N. Dogra, *Unlikely intersections and the Chabauty–Kim method over number fields* (arXiv 1903.05032).
- J. S. Balakrishnan, A. Besser, F. Bianchi, J. S. Müller, *Explicit quadratic Chabauty over number fields*, Israel
  J. Math. 243 (2021) (arXiv 1910.04653).
- F. Bianchi, O. Padurariu, *Rational points on rank 2 genus 2 bielliptic curves in the LMFDB* (arXiv 2212.11635).
- N. Bruin, M. Stoll, *Two-cover descent on hyperelliptic curves*, Math. Comp. 78 (2009) (arXiv 0803.2052).
- B. Creutz, *Explicit descent in the Picard group of a cyclic cover of the projective line* (2012).
- M. Stoll, *Implementing 2-descent for Jacobians of hyperelliptic curves*, Acta Arith. 98 (2001).
- B. Poonen, E. Schaefer, *Explicit descent for Jacobians of cyclic covers of the projective line*, J. reine angew.
  Math. 488 (1997).
- G. Villines, *The Diophantine equation x⁴ + 2y³ + z³ = 0: reduction and partial resolution*, Zenodo
  10.5281/zenodo.20672504 (June 2026).
- A. Ratcliffe, B. Grechuk, *Generalised Fermat equation: a survey of solved cases* (arXiv 2412.11933).
