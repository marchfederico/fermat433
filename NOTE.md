# The equation x⁴ + 2y³ + z³ = 0 and quadratic Chabauty through a hidden involution

*Working note, September 2026. Companion to RESULTS.md (the chronological record) and the scripts in this directory.*

## 1. Statement

**Claim.** The primitive integer solutions of x⁴ + 2y³ + z³ = 0 are exactly
(±1, 0, −1), (±1, −1, 1), (±43, −203, 237),
conditional on the two external inputs listed in §7 (the rank bound for the hard pair and the results imported
for the four other twists).

The equation is the smallest "uninvestigated" generalised Fermat equation (H = 40) in the survey of Ratcliffe and
Grechuk (arXiv 2412.11933). G. Villines (github.com/gvillines-hub/h40-x4-2y3-z3, June 2026) reduced it, with Magma,
to two genus-2 curves whose Jacobians have Mordell–Weil rank equal to the genus, where classical Chabauty fails; he
left the problem open. This note closes that gap by a quadratic Chabauty computation whose extra Néron–Severi class is
only defined over a field of degree 12.

## 2. The reduction

Let θ = ∛2, K = Q(θ) (class number 1, fundamental unit ε = θ − 1, 2 and 3 totally ramified). For a primitive
solution, z + yθ has norm −x⁴ and is coprime to its conjugates outside 2 and 3, so z + yθ = −ε^k γ⁴ with
γ = a + bθ + cθ² ∈ Z[θ] and k ∈ {0, 1, 2, 3}. Reading off the coefficient of θ² gives four plane quartics C_k over Q
(genus 3). Primitivity forces γ to be a unit above 2 and 3; local conditions at 2 kill C_2 and C_3. Every primitive
solution therefore comes from C_0(Q) or C_1(Q) (descent_explore.py, diagonal.py).

Each C_k carries an involution over K with quotient a j = 1728 elliptic curve E_k/K, and an étale double cover: the
square of the norm form of γ lies on a conic, giving genus-2 twists y² = λ·f₆(s, t). For k = 0 this produces the
curves A±: y² = ±(x⁶ − 40x³ − 32); for k = 1 the curves y² = λC₃(x), λ ∈ {±1, ±2}, with
C₃ = 17x⁶ − 72x⁵ + 90x⁴ + 40x³ − 180x² + 144x − 40 (etale.py; the models agree with Villines' A±, B±, C±).
Villines settles A± (classical Chabauty at p = 5; empty fake 2-Selmer set), B+ and C− (empty fake 2-Selmer sets).
The **hard pair** is

  B−: y² = −C₃(x), known points (1, ±1), (−1, ±15);   C+: y² = 2C₃(x), known points (2, ±12), (6/5, ±172/125),

quadratic twists of each other by −2, with rank J(Q) = 2 = g (independent generators exhibited by Villines and, below,
by us; the upper bound by a 2-descent over Q, ours in sel2/pipeline.gp, PROOF.md Part D). The point (6/5, ±172/125) is the 43-solution.

## 3. Structure of the hard pair

**Endomorphisms (nschar2.gp, splitF.gp).** For every prime inert in F = Q(√−2) the Frobenius trace vanishes; at
split primes the Frobenius polynomial factors over F with constant terms ±π², ±π̄² but over Z only when it is even.
Hence V_ℓ(J) = Ind_F^Q ψ with End⁰_F(J) = F, and since the Rosati involution on an imaginary quadratic field is
conjugation, **ρ(J/F) = 1**: quadratic Chabauty over Q(√−2), the route suggested in Villines' notes, has no class to
use. The traces of Frobenius on NS(J_Q̄) ⊗ Q (rank 4) depend only on the splitting of p in F and in the S₄-field
N = Galois closure of Q(∛2, ω, √(−1−∛2)); the values (table in RESULTS.md) are the character of
1 ⊕ (sgn_F ⊗ sgn ⊗ std) for Gal(M/Q) ≅ S₄ × Z/2, M = NF of degree 48, with class densities matching. Complex
conjugation has trace 2, i.e. eigenvalues (1, 1, 1, −1): **exactly one Néron–Severi class on which complex conjugation
acts by −1**.

**Automorphisms (invol.gp, invol4.gp, invol8.gp).** The Möbius maps permuting the six roots of C₃ form S₄, so
Aut(X_Q̄) ≅ GL₂(F₃) of order 48: the hard pair, and A±, are Q-twists of the Bolza curve y² = x⁵ − x. Nine involutory
Möbius maps x ↦ (−x + b)/(cx + 1); the three with b a root of b³ − 18b² + 36b − 20 lift to automorphisms of order 4,
the six with b a root of 81b⁶ − 540b⁵ + 1494b⁴ − 2240b³ + 1980b² − 1008b + 232 lift to genuine involutions
τ: (x, y) ↦ (μ(x), κs·y/(cx+1)³), κ = 1 + bc, s = √κ. Their Möbius parts are defined over
K₆ = Q(∛2, √(∛2 − 1)) — the square root of the fundamental unit labelling the hard descent class — and the
involutions themselves over L = K₆(√κ): L = Q(t)/(t¹² + 6t¹⁰ + 3t⁸ − 28t⁶ − 33t⁴ + 6t² − 3), signature (2, 5),
discriminant 2²⁸3¹³, class number 1, 2 totally ramified, 3 = 𝔭₁³𝔭₂⁶𝔭₃³, κ a {2,3}-unit. This is the degree-12 field
predicted by the Néron–Severi character (the stabiliser of the anti-invariant class has order 4 in a group of order 48).

**The bielliptic model (step2a.gp).** With x± = (−1 ± s)/c the fixed points of μ, X = (x − x₊)/(x − x₋),
Y = y(X − 1)³, the curve becomes Y² = F(X) = AX⁶ + BX⁴ + CX² + D with A = f(x₋), D = f(x₊), and τ: (X, Y) ↦ (−X, Y).
Following Bianchi–Padurariu, E₁: Y'² = X'³ + BX'² + ACX' + A²D via φ₁ = (AX², AY) and
E₂: Y'² = X'³ + CX'² + BDX' + AD² via φ₂ = (D/X², DY/X³); both have j = 8000 (CM by Z[√−2]). Global minimal models
over L exist (h_L = 1); their minimal discriminants are supported on the prime above 2 and one prime above 3, and
E_i(L)_tors = Z/2. The natural models are non-minimal at two degree-1 primes above 397 (A and D have valuation −6
at one each), which produces the correction term of §5.

## 4. The identity for rational points

Let D₁ = [(1,1) − (1,−1)], D₂ = [(−1,15) − (−1,−15)] ∈ J(Q) and Q_i = φ₁(P_i), Q'_i = φ₂(P_i) ∈ E₁(L), E₂(L).
The 499-adic logarithms of Q₁, Q₂ at two places are independent, so D₁, D₂ span J(Q) ⊗ Q (rank 2).

**Theoretical basis.** Balakrishnan–Dogra (*Quadratic Chabauty and rational points II*, IMRN 2021) set, for K = Q,
ρ_f(J) = rk NS(J) + rk NS(J_Q̄)^{c=−1}, and their Proposition 2 (quoted in Dogra, *Unlikely intersections and the
Chabauty–Kim method over number fields*, Remark after Prop. 1.1) gives finiteness of the depth-2 Chabauty–Kim set
X(Q_p)₂ whenever rk J < g − 1 + rk NS(J) + rk NS(J_Q̄)^{c=−1}. Here 2 < 2 − 1 + 1 + 1. The "sign rule" derived in
RESULTS.md — that for rational points only classes and characters in the same Galois-isotypic component pair
non-trivially, and that the usable classes are the complex-conjugation-anti-invariant ones — is precisely the origin of
the term rk NS(J_Q̄)^{c=−1}. The explicit function is the bielliptic quadratic Chabauty function of
Balakrishnan–Besser–Bianchi–Müller (*Explicit quadratic Chabauty over number fields*, Israel J. Math. 2021,
Theorem 1.5), for the base field L and a non-cyclotomic idele class character, restricted to X(Q) ⊂ X(L); the
normalisation of the logarithmic term follows Bianchi–Padurariu (arXiv 2212.11635, Theorem 2.3).

**The character (step1_character.gp).** Take p = 499, the smallest prime splitting completely in M, so that
L ⊗ Q_p = Q_p¹² and every endomorphism is p-rational. The classes of the twelve involutions act on the holomorphic
differentials by A_i = s_i⁻¹[[−1, −c_i],[−b_i, 1]]; because the Hodge filtration is one of the two CM eigenspaces of
Frobenius, NS(J) ⊗ Q_p ≅ M₂(Q_p) through this action and the A_i span sl₂ = the 3-dimensional non-trivial part. The
kernel of (c_i) ↦ Σ c_i A_i has dimension 9; its orthogonal complement R is the isotypic component of the
3-dimensional representation. The six fundamental units of L have 499-adic logs of rank 6 meeting R in a 2-dimensional
space, so the space of idele class characters in R is one-dimensional: χ_Z = (c_1, …, c_{12}), normalised c_1 = 1,
extended to all places of L by class number 1 (χ_w(π_w) = Σ_i c_i log σ_i(α_w) for a generator α_w). The local
components at p are −c_w log_p + d_w v_p. **χ_Z vanishes at the uniformisers of every prime above 2 and 3.**

**The identity.** For z ∈ X(Q) with [z − ιz] = a₁D₁ + a₂D₂ in J(Q) ⊗ Q, φ₁(z) = a·Q + T with T ∈ E₁(L)[2], and
h_χ(φ₁ z) − h_χ(φ₂ z) = aᵀGa, where G_ij = ⟨Q_i, Q_j⟩_χ − ⟨Q'_i, Q'_j⟩_χ. Decomposing both heights into local
terms — the sigma-function local height λ_w at the twelve places above p (Mazur–Tate, with the canonical constant),
m_w(Q)·χ'_w(π_w) at good places away from p, nothing at 2 and 3 — and using that χ kills the global element
X(z) ∈ L^×, the away-from-p terms collapse to −2Σ_i c_i log σ_i(X(z)) up to contributions of the two primes above 397.
The d_w-terms at p cancel exactly against the 2d_w v_p(σ_w X) produced by the same manipulation (because
m_w(φ₁z) − m_w(φ₂z) = −2v_w(X(z)) also holds at w | p). Hence, for every z ∈ X(Q),

  ρ(z) := Σ_{i=1}^{12} c_i [λ_i(φ₁z) − λ_i(φ₂z)] − 2Σ_i c_i log σ_i(X(z)) − a(z)ᵀ G a(z) = −Ω₃₉₇,

with a(z) determined by the logarithms at two places. ρ extends analytically across the disks where some σ_i(X(z))
tends to 0 or ∞ (the logarithmic singularities of λ_i and of log X cancel; the analytic form 2c_i[log(s/X) + v(s)] is
used there, as in Bianchi–Padurariu, Remark 2.5).

## 5. The 397 correction is a constant

At a degree-1 prime w above 397, v_w(A) = −6, v_w(x₋) = −1, x₊ integral, v_w(u₁) = −2, v_w(u₂) = −1 (from the
discriminant exponents −24 and −12 of the natural models). With m_w the minimal-model denominator exponent:
for v_w(X) ≤ 0, m_w(φ₁) = 2 − 2v_w(X) and m_w(φ₂) = 0; for v_w(X) = 1 both vanish; for v_w(X) ≥ 2, m_w(φ₁) = 0 and
m_w(φ₂) = 2v_w(X) − 2. In every case m_w(φ₁) − m_w(φ₂) + 2v_w(X) = 2, and by the conjugation symmetry the bracket is
−2 at the other prime. Thus Ω₃₉₇ = 2χ'_{w₁}(π) − 2χ'_{w₂}(π) is a single constant, computed from a generator of the
primes and X(P₁). Numerically: ρ(P_k) + Ω₃₉₇ = O(499¹⁹) at both known points with the −2 log X sign, and not with
the opposite sign (step2b.gp).

## 6. The computation

**Heights (step2b.gp).** Each E_k ⊗_{σ_i} Q₄₉₉ is replaced by an integer model congruent to it modulo 499³⁰, so PARI's
ellpadics2 supplies the sigma constant; ψ₅₁₄(Q) is evaluated by the classical division-polynomial recurrences
(calibrated by log σ(kQ₀) − k² log σ(Q₀) = log ψ_k(Q₀) to O(499¹⁹)); λ(Q) = −(2/m²)(log σ(mQ) − log ψ_m(Q)),
m = #E(F₄₉₉) = 514. The χ_Z-height is a quadratic form: h(Q₁+Q₂) + h(Q₁−Q₂) − 2h(Q₁) − 2h(Q₂) = O(499¹⁹) on both
quotients and h(2Q₁) = 4h(Q₁) (the relative sign between the p-adic and away-from-p terms was wrong at first and
this test caught it).

**Disks (step3_*.gp, four parallel chunks, 0.74 s per disk).** X(Q₄₉₉) has 528 residue disks (no Weierstrass disks).
ρ, expanded to O(T¹⁴) with 14 digits, has Strassman index 2 on every disk, with coefficient valuations
[·, 1, 1, 2, 3, …]: the quadratic term dominates because every logarithm lies in 499Z₄₉₉ and the inverse log-matrix
has valuation −1. The Z₄₉₉-roots of the truncated series: **524 zeros** on B− (262 disks with two, 266 with none),
**504 on C+**. ρ vanishes to O(499¹³) at the known points. A recomputation with 20 digits and O(T²⁰) reproduces the
roots to 8 digits and the counts, with valuations continuing linearly to 18, so the truncation loses nothing.

**Sieve (step4_scan.gp, step4_sieve.gp).** Every point of J(Q₄₉₉) has a 499-integral coefficient vector (logarithms
in 499Z₄₉₉, log-matrix determinant of valuation 2), so [J(Q) : ⟨D₁, D₂⟩ + tors] is a 499-unit, and in the
499-parts of E₁(F_𝔮) × E₂(F_𝔮) both the index and the 2-torsion translate disappear: a rational point z must satisfy
ξ(a(z)) ∈ {ξ(φ₁(w), φ₂(w)) : w ∈ X(F_q)} ⊂ (Z/499)² at every degree-1 prime 𝔮 of L with 499 | #E₁(F_𝔮) = #E₂(F_𝔮).
Such primes: four above 997 (#E = 998), four above 12973, two above 47903, two above 59879, twelve above 88339.
The first prime above 997 eliminates 518 of the 524 zeros on B− (494 of 504 on C+); the primes above 12973 eliminate
the rest except four; **the four survivors are the known points** on each curve: (1, ±1), (−1, ±15) with a = (±1, 0),
(0, ±1), and (2, ±12), (6/5, ±172/125) likewise.

## 7. What the result depends on

1. **rank J(Q) = 2** for B− and C+. We prove ≥ 2 by exhibiting points and ≤ 2 by a 2-descent over Q
   (sel2/pipeline.gp, PROOF.md Part D: dim Sel²(J) = 2, J(Q)[2] = 0, so also Ш[2] = 0), agreeing with Villines' Magma
   2-descent. The implementation was validated on 24 database curves (dim Sel² = analytic rank on all of them); an
   earlier attempt via Simon's 2-isogeny descent on E₁ over the degree-12 field L is recorded in RESULTS.md.
2. The four easy curves: A−, B+, C− are empty (norm condition on S-units; certified class groups) and A⁺(Q) = {∞±, (−1, ±3)}
   (rank 1 by our 2-descent, Chabauty at the inert prime 5 through the bielliptic quotients, 5-adic Mordell–Weil sieve);
   both agree with Villines' Magma computations (PROOF.md Part B).
3. The theory: Balakrishnan–Dogra's finiteness theorem with ρ_f (the c = −1 classes), BBBM's bielliptic identity for a
   general idele class character, Bianchi–Padurariu's normalisation; the local-height formulas at p (validated by the
   parallel session's implementation against PARI's canonical heights) and the standard away-from-p formulas on
   minimal models with good reduction.
4. PARI's rigorous p-adic error tracking; the series tail bounded by the observed linear growth of coefficient
   valuations (confirmed at higher precision).

## 8. What is new

- An explicit quadratic Chabauty computation whose extra Néron–Severi class is defined only over a degree-12 field:
  the hidden involution of a twist of the Bolza curve, found from the automorphism group, with the field of definition
  matching the Galois character of NS(J_Q̄).
- The character in the isotypic component, obtained by linear algebra from the involutions' action on holomorphic
  forms and the p-adic logs of the units, with the vanishing at 2 and 3 as a by-product.
- p-adic heights at twelve places of a degree-12 field through integer models congruent modulo p³⁰, and the
  division-polynomial recurrences for ψ₅₁₄ in place of a degree-130,000 polynomial.
- An index-free sieve: 499-integrality of the coefficient vector removes the saturation hypothesis usually needed.
- The observation that Villines' proposed endgame over Q(√−2) cannot work (ρ(J/Q(√−2)) = 1), while the
  complex-conjugation-anti-invariant class over M does.

## 9. Files

descent_explore.py, diagonal.py, etale.py (reduction) · splitF.gp, nschar2.gp (Galois structure) · invol*.gp
(automorphisms) · step1_character.gp · step2a.gp, step2b.gp · step3_setup.gp, step3_disk.gp, step3_run.gp,
step3_aggregate.py, step3_precision_check.gp · step4_scan.gp, step4_sieve.gp · twist/ (same for C+) · logs/.
