# x^4 + 2y^3 + z^3 = 0: an independent attempt (September 2026)

*Note (repository split, 2026-09-12): scripts named below without a path that are not part of the proof (searches, the Simon descent over L, prime scans, early Chabauty attempts) now live in exploration/; the proof scripts are listed in README.md.*

Status: **open**. Smallest "uninvestigated" equation (H = 40) in Ratcliffe–Grechuk, *Generalised Fermat
equation: a survey of solved cases* (arXiv 2412.11933, v2 April 2025). An independent campaign by
G. Villines (github.com/gvillines-hub/h40-x4-2y3-z3, Zenodo 10.5281/zenodo.20672504, June 2026) reaches the
same obstruction with Magma. This attempt used PARI/GP 2.17.4 and Denis Simon's ell.gp (from the Sage tree).

## Known primitive solutions
(±1, 0, −1), (±1, −1, 1), (±43, −203, 237)   [43^4 + 237^3 = 2·203^3]

## Reduction (proved)
K = Q(θ), θ^3 = 2: class number 1 (bnfcertify), fundamental unit ε = θ − 1 (norm +1), 2 and 3 totally ramified.
A primitive solution has gcd(y, z) = 1 and α = z + yθ with N(α) = −x^4; ideal coprimality gives (α) = 𝔞^4, so
α = −ε^k γ^4 with k ∈ {0,1,2,3}, γ = a + bθ + cθ^2 ∈ Z[θ]. Hence (a:b:c) is a rational point on the plane quartic
C_k : [θ^2](−ε^k γ^4) = 0 (smooth, genus 3, good reduction at 31 and 43), with x = N(γ), z + yθ = −ε^k γ^4.
Primitivity forces γ to be a unit at the primes above 2 and 3 (a odd, a + 2b + c ≢ 0 mod 3).

* C_3 has no primitive solutions mod 8: no Q_2-points.
* C_2 has no points mod 2 with a odd: no primitive solutions.
* Hence every primitive solution comes from C_0(Q) or C_1(Q):
  - C_0 : −4a^3c − 6a^2b^2 − 24abc^2 − 8b^3c − 4c^4 = 0, known points (1:0:0) [trivial], (0:1:0), (1:0:−1) [imprimitive]
  - C_1 : −4a^3b + 4a^3c + 6a^2b^2 − 12a^2c^2 − 24ab^2c + 24abc^2 − 2b^4 + 8b^3c − 16bc^3 + 4c^4 = 0,
    known points (1:0:0) [(1,−1,1)], (1:−1:2) [(43,−203,237)], (1:−2:0), (1:1:0) [imprimitive]
  The unit conditions at 2 and 3 separate primitive from imprimitive points exactly.

## Structure
In coordinates r = γ(θ), s + tζ = γ(ζθ) over K, C_k becomes A r^4 + G(s,t) = 0, so the involution r ↦ −r is
defined over K with quotient E_k : W^2 = −A·G(s,t), a j = 1728 curve; J(C_k) ~ Res_{K/Q} E_k and
rank J(C_k)(Q) = rank E_k(K).

| | rank over K (Simon 2-descent) | notes |
|---|---|---|
| E_0 | 2 (Selmer bound attained) | base change of y^2 = x^3 − 36x (conductor 576, rank 1 over Q) |
| E_1 | 3 (lower bound 3, 2-Selmer rank 4, E(K)[2] = Z/2) | agrees with Villines' "rank 3 = [K:Q]" |

Étale double covers: δ = γ^2 lies on a conic; γ^2 = λ·δ(s,t) forces λ·N(δ(s,t)) to be a square, giving genus-2 twists.
All known points lie on λ ∈ {1, −2}:
* C_0 → y^2 = λ(x^6 − 40x^3 − 32)  (Villines' A±, up to x ↦ −x)
* C_1 → y^2 = −C_3(x) (λ = 1) and y^2 = 2C_3(x) (λ = −2), C_3 = 17x^6 − 72x^5 + 90x^4 + 40x^3 − 180x^2 + 144x − 40:
  exactly Villines' hard pair B−, C+ (rank 2 = genus by his Magma computations).
  PARI: odd conductor 3^6, torsion bound gcd #J(F_q) = 1, no real multiplication over Q (Frobenius discriminants vary).
  lfungenus2's analytic ranks are unreliable here (functional equation error 1e-4; conductor at 2 unknown).

## Computations
* Thue equations z^3 + 2y^3 = −x^4 solved completely for every 1 ≤ x ≤ 3000 (thueinit(x^3+2, 1)): only the known solutions.
* C_0, C_1: no other primitive points with max |a|,|b|,|c| ≤ 250.
* Chabauty–Coleman on C_0 at p = 31 (rank 2 < genus 3), with global integrals as p-adic elliptic logarithms on
  the three embeddings of E_0 and tiny integrals of the canonical basis G·dx/F_y: pullback identities hold to 30 digits;
  the three disks with known points get bound 1; 27 disks without known points get bound 1 (2 get 0), total 30.
  Closing C_0 needs a Mordell–Weil sieve over K on those 27 disks (not done).
* C_1: rank 3 = genus, Chabauty does not apply; the genus-2 route needs rank ≤ 1 but the hard pair has rank 2.

## What would finish it
Villines lists: quadratic Chabauty over Q(√−2) (the GL2(F)-type structure gives Néron–Severi rank ≥ 2 there),
or a refined descent combining the conic factor with the quartic cover.

## Files
descent_explore.py (descent, quartics, searches, local tests) · diagonal.py (diagonalization over K) ·
gen_qcoeffs.py → qcoeffs.gp (quartic models) · simon_rank.gp, simon_e1.gp + simon/ (2-descents over K) ·
e0q.gp · chab433.gp (Chabauty via elliptic logs; run with `KK = 0; PP = 31;` prepended) · etale.py (conics,
sextics, twists) · g2data.gp, g2struct.gp, ic.gp (genus-2 data) · thue_search.gp · bigsearch.py · logs/.
Note: an early export of the C_1 quartic skipped the θ^3 = 2 reduction and duplicated E_0; simon_rank.log's
"E1" line is that bug; simon_e1.log is the corrected run.

## Galois structure of the Néron–Severi group of the hard pair (Sept 11, from Frobenius data)
Scripts: splitF.gp (primes to 1500), nschar2.gp → logs/nschar.log (primes to 2500), look499.gp.
Facts read off the Frobenius polynomials of y² = −C3(x) (identical for the −2-twist):
* Every prime inert in F = Q(√−2) has trace 0; at split primes the quartic factors over F (constant terms ±π², ±π̄²)
  but over Z only when it is even. Hence V_ℓ(J) = Ind_F^Q ψ with End⁰_F(J) = F. The Rosati involution on an imaginary
  quadratic field is conjugation, so **ρ(J/F) = 1: quadratic Chabauty over Q(√−2) has no class to use** (contra the
  "ρ(J/F) ≥ 2" in Villines' README).
* The trace of Frobenius on NS(J_Q̄) ⊗ Q (rank 4; the transcendental part contributes 0 at inert primes and has no
  root-of-unity eigenvalues at split primes) depends only on the splitting of p in F and in the S_4-field
  N = Galois closure of Q(∛2, ω, √(−1−∛2)):
    p ≡ 1 (3), x³−2 irreducible mod p (3-cycles):             trace 1 (both F-classes)
    p ≡ 1 (3), three roots, (−1−r|p) = [−1,−1,1] (double transp.): 0 if F-split, 2 if F-inert
    p ≡ 1 (3), three roots, all (−1−r|p) = 1 (identity in N):    4 if F-split (square Frobenius polynomial), −2 if F-inert
    p ≡ 2 (3), (−1−r|p) = −1 (transpositions):                     0 if F-split, 2 if F-inert
    p ≡ 2 (3), (−1−r|p) = +1 (4-cycles):                            2 if F-split, 0 if F-inert
  Consistent with Gal(M/Q) ≅ S_4 × Z/2 (M = N(√−2), degree 48: the endomorphism field) and
  NS(J_Q̄) ⊗ Q ≅ 1 ⊕ (sgn_F ⊗ sgn_{S_4} ⊗ std). Densities match (identity class 16/365 ≈ 1/24 in N, independent of F).
* Complex conjugation = (transposition, σ_F) has trace 2, i.e. eigenvalues (1,1,1,−1): exactly one anti-invariant class
  Z, defined over a degree-12 subfield L_Z of M (up to sign over the sextic N^{⟨(12),(34)⟩}).
* Reduction: at 3 the stable model is smooth (potentially good reduction) → no local height contributions at 3.
  At 2 the stable model is two supersingular elliptic curves → 2 is the only prime that can contribute.

### Consequence for a quadratic-Chabauty attack on the rational points
Sign rule (derived here, not yet checked against the literature; Dogra, "Unlikely intersections and the Chabauty–Kim
method over number fields", is the reference to check): for x ∈ X(Q) the identity attached to (Z, χ) survives only if
the NS class Z and the p-adic idele class character χ lie in the same Galois-isotypic component. The cyclotomic
character (trivial component) never helps for a curve over Q; here the useful component is the 3-dimensional
ρ_W = sgn_F ⊗ sgn ⊗ std, in which characters exist unconditionally (the character space contains
1 ⊕ Ind_{⟨c⟩}(sign) and c has a −1 eigenvalue on ρ_W). The resulting function on X(Q_p) (p splitting completely in M,
e.g. 499, 1459, 1579, 1723, 1753) is h_p^{Z_eff}(x) − B(log x, log x) with Z_eff ∈ NS ⊗ Q_p a χ-weighted sum of the
12 conjugates of Z and B a symmetric bilinear form on J(Q) ⊗ Q_p (3 unknowns; the two known x-values on each curve
give only 2 equations, so one global height value is needed). Whether the places above 2 drop out depends on whether
the decomposition group at 2 has fixed vectors on ρ_W (not computed). Still missing: double Coleman integrals and
local heights at p, the class Z on H¹_dR, and the character's local coefficients (units of L_Z).

## Automorphisms of the hard pair (Sept 11; invol.gp, invol4.gp, invol8.gp)
* The Möbius maps permuting the six roots of C3 form a group of order 24 (S_4), so Aut(X_Q̄) has order 48: the
  hard pair (and A±) are Q-twists of the Bolza curve y² = x⁵ − x. Nine involutory Möbius maps x ↦ (−x+b)/(cx+1):
  three (b a root of b³ − 18b² + 36b − 20) lift to automorphisms of order 4; six lift to genuine involutions τ
  (λ = (1+bc)³), with b a root of 81b⁶ − 540b⁵ + 1494b⁴ − 2240b³ + 1980b² − 1008b + 232.
* Field of the six Möbius maps: K6 = Q(t)/(t⁶ − 3t⁴ − 3t² − 1) = Q(∛2, √(∛2 − 1)) — the square root of the
  fundamental unit ε of the k = 1 descent class (signature (2,2), disc 2¹⁰3⁶; 2 totally ramified, 3 = 𝔮₁³𝔮₂³).
* Field of the involution itself: L = K6(√(1+bc)), t¹² + 6t¹⁰ + 3t⁸ − 28t⁶ − 33t⁴ + 6t² − 3, degree 12,
  signature (2,5), disc 2²⁸3¹³, 2 totally ramified, 3 = 𝔭₁³𝔭₂⁶𝔭₃³; 1+bc is a {2,3}-unit. L contains none of
  √−2, i, √−3, √2, √3, √(±θ), √(±(1+θ)), √−ε. This is the degree-12 field predicted by the Néron–Severi character.
* Quotients: E_τ = X/τ and E_ιτ = X/ιτ both have j = 8000 (CM by Z[√−2]); they are quadratic twists over L of
  E0: y² = x³ + 4x² + 2x by classes d with no representative among ±1, ±2, ±3, ±6 times {1, ε, 1+θ, θ, √(1+bc)}…
  The class Z of the sign rule is τ_*; over L the curve is bielliptic.
* Linear methods via E_τ do not help: X(Q) → E_τ(L) ⊂ Res_{L/Q}(E_τ)(Q) lands in the image of J (2-dimensional),
  where rank = dimension again. Only quadratic Chabauty or a descent to a larger Jacobian can work.
* Plan (bielliptic quadratic Chabauty over L, restricted to Q-points): p ∈ {499, 1459, 1579, 1723, 1753} (split
  completely in the endomorphism field), χ_Z from the units of L, Mazur–Tate local heights on E_τ at the 12 places
  above p, local heights at 2 (3 contributes nothing), the bilinear form from generators of J(Q), Strassman, sieve.

## Step 1 (Sept 11): the p-adic character on L in the Néron–Severi component — step1_character.gp
p = 499 (splits completely in the endomorphism field; f1 has no root in Q_499). With the twelve embeddings
σ_i: L → Q_p, the involutions act on holomorphic forms (basis dx/y, x dx/y) by A_i = s_i^{-1} [[−1, −c_i], [−b_i, 1]]
(A_i² = 1, trace 0). NS(J) ⊗ Q_p ≅ M_2(Q_p) via the action on H⁰(Ω¹) (the Hodge filtration is one CM eigenspace of
Frobenius), so the classes of the involutions are the A_i, spanning sl_2 = the 3-dimensional non-trivial part.
Verified numerically: ker(c ↦ Σ c_i A_i) has dimension 9; its orthogonal complement R (dim 3) is the isotypic
component; R ⊥ (1,…,1); the six fundamental units of L (class number 1) have 499-adic logs of rank 6 and
Σ_i log σ_i(u) = 0; dim(R ∩ span(unit logs)) = 2; so the character space inside R is one-dimensional:
χ_Z = (c_1, …, c_12), c_1 = 1 (logs/step1_data.txt). **χ_Z vanishes at the uniformisers of the prime above 2 and of
the three primes above 3** (to O(499^30)): the local heights at 2 and 3 contribute nothing to the identity.
Z_eff = Σ c_i A_i is a traceless 2×2 matrix (the effective class on holomorphic forms).
Next: images of the generators of J(Q) on E_τ(L); their χ_Z-heights (sigma at the 12 places, denominators at good
primes via class number 1); the bilinear form; the 499-adic function; Strassman; sieve. The parallel session's
qc_sigma.py / qc_local.py / qc_solve.py (bielliptic QC over Q, Bianchi–Padurariu) supply the sigma-function local
heights, applicable because each E_τ ⊗_{σ_i} Q_p is isomorphic over Q_p to E0: y² = x³ + 4x² + 2x or to its
unramified twist, both defined over Q.

## Step 2 (Sept 11): the bilinear form — step2a.gp (over L), step2b.gp (499-adic)
Bielliptic model over L: X = (x − x₊)/(x − x₋) with x± = (−1 ± s)/c the fixed points of the Möbius map, Y = y(X−1)³,
Y² = F(X) = A X⁶ + B X⁴ + C X² + D (F even, A = f1(x₋), D = f1(x₊)); τ: (X,Y) ↦ (−X, Y). Quotients (Bianchi–Padurariu
normalisation) E1: Y'² = X'³ + B X'² + AC X' + A²D via φ1 = (AX², AY), E2: Y'² = X'³ + C X'² + BD X' + AD² via
φ2 = (D/X², DY/X³); both j = 8000. Global minimal models exist (h_L = 1); minimal discriminants supported on the prime
above 2 (exp. 36) and one prime above 3 (exp. 6) only; torsion Z/2 each. The natural models are non-minimal at two
degree-1 primes above 397 (disc exponents −24/−12 and −12/−24).
Generators: D₁ = [(1,1) − (1,−1)], D₂ = [(−1,15) − (−1,−15)] of J(Q); images Q_i = φ1(P_i), Q'_i = φ2(P_i) have
denominator ideals only at primes above 2, 3, 31 (Q₁±Q₂), 99431 (Q₂). Their elliptic logs at two places are
independent (det ≠ 0), so D₁, D₂ span J(Q) ⊗ Q (rank 2).
499-adic local heights: each E_k ⊗_{σ_i} Q₄₉₉ replaced by an integer model congruent mod 499³⁰ so PARI's ellpadics2
applies; σ from the formal group; ψ_m(Q) (m = #E(F₄₉₉) = 514) evaluated by the classical recurrences (calibrated:
log σ(kQ₀) − k² log σ(Q₀) = log ψ_k(Q₀) to O(499¹⁹) for k = 2,3,4); λ_p(Q) = −(2/m²)(log σ(mQ) − log ψ_m(Q)).
Character convention: with λ_p as above, the away-from-p term is m_w(Q)·χ'_w(π_w) with χ'_w(π_w) = +Σ_i c_i log σ_i(α_w)
(α_w a generator of 𝔭_w), i.e. the idele character has components (−c_w log_p, χ'_w) — the relative sign was wrong
at first and the parallelogram law caught it.
**Validation:** h_χ(Q₁+Q₂) + h_χ(Q₁−Q₂) − 2h_χ(Q₁) − 2h_χ(Q₂) = O(499¹⁹) on both quotients; h(2Q₁) = 4h(Q₁).
Bilinear form G_ij = ⟨Q_i,Q_j⟩^{E1} − ⟨Q'_i,Q'_j⟩^{E2} in logs/step2b_data.txt (with χ, λ's, logs, d_w).
Identity at rational z (X(z) a unit at the places above p):
  ρ(z) := Σ_i c_i[λ_i(φ1 z) − λ_i(φ2 z)] − 2 Σ_i c_i log σ_i(X(z)) − a(z)ᵀ G a(z) = −Ω₃₉₇,
where a(z) solves Log_w(φ1 z) = a₁ Log_w(Q₁) + a₂ Log_w(Q₂), and Ω₃₉₇ = 2χ'_{w₁}(π) − 2χ'_{w₂}(π) is a CONSTANT:
at the 397-primes the bracket m_w(φ1) − m_w(φ2) + 2v_w(X) equals +2 at w₁ and −2 at w₂ for every 397-adic point
(valuation analysis with v(u₁) = −2, v(u₂) = −1; no other prime outside {2,3} is non-minimal). Verified numerically
at P₁ and P₂: ρ(P_k) + Ω₃₉₇ = O(499¹⁹) with the −2 log X sign (the +2 log X sign fails).
Remaining: expand ρ on the residue disks of X(Q₄₉₉) (no Weierstrass disks: f1 has no root mod 499; special disks
where X(z) is a non-unit at some place need the d_w correction), Strassman bounds, Mordell–Weil sieve; then the same
for the −2-twist y² = 2C3(x).

## Steps 3–4 (Sept 11): residue disks, zeros of ρ, Mordell–Weil sieve — y² = −C3(x) (the curve B−)
step3_setup.gp / step3_disk.gp / step3_run.gp (four parallel chunks), step3_aggregate.py; results in logs/step3_disks.txt.
* X(Q₄₉₉) has 528 residue disks (526 finite, 2 at infinity; no Weierstrass disks since f1 has no root mod 499).
  ρ was expanded to O(T¹⁴) with 14-digit coefficients on every disk (0.74 s each); the 24 special disks (an embedding
  of X(z) tending to 0 or ∞) use the analytic form 2c_i[log(s/X) + v(s)] of the singular pair of terms. No errors.
* Every disk has Strassman index 2 with coefficient valuations [·, 1, 1, 2, 3, …]: the quadratic term
  a(z)ᵀGa(z) dominates because all logarithms lie in 499Z₄₉₉ and the inverse log-matrix has valuation −1, so
  Strassman alone gives ≤ 2 zeros per disk. The Z₄₉₉-roots of the truncated series: 524 in total (262 disks with
  two, 266 with none — the truncation error O(499¹³) is far below the coefficient valuations, so these are all the
  zeros of ρ). ρ vanishes to O(499¹³) at the known points.
* Of the 524 zeros exactly four have a coefficient vector a(z) that is rational with small height (algdep): the
  known points, a = (±1, 0) at (1, ±1) and (0, ±1) at (−1, ±15).
* Sieve (step4_scan.gp, step4_sieve.gp): a is 499-integral for every point of J(Q₄₉₉) (logs in 499Z₄₉₉, det of the
  log matrix of valuation 2), so the index [J(Q) : ⟨D₁, D₂⟩ + torsion] is a 499-unit and, projecting to the 499-parts,
  a rational point z must satisfy ξ(a(z)) = ξ(φ₁(z̄), φ₂(z̄)) ∈ (Z/499)² at every degree-1 prime 𝔮 of L with
  499 | #E₁(F_𝔮) = #E₂(F_𝔮) — with no torsion or index ambiguity (2-torsion and unit indices vanish mod 499).
  Primes found (scan to 3·10⁵): four above 997 (#E = 998 = 2·499), four above 12973, two above 47903, two above 59879,
  twelve above 88339. Result: the first prime above 997 eliminates 518 of the 524 zeros, the primes above 12973 two
  more; four candidates survive every prime — necessarily the four known points (rational points cannot be sieved out).
  ⇒ Modulo the correctness of the derivation and the precision analysis, **X(Q) = {(1, ±1), (−1, ±15)} for y² = −C3(x)**.
* Same pipeline launched for the −2-twist y² = 2C3(x) (the same involution, field L and character; the quotient
  curves are twisted and the known points are (6/5, ±172/125), (2, ±12)): twist/ subdirectory.

## Steps 3–4 for the −2-twist y² = 2C3(x) (the curve C+), and the conclusion (Sept 11)
twist/ (same scripts with f1 ↦ −2·f1, known points (6/5, ±172/125), (2, ±12)); logs in logs/twist/.
* Same involution, field L and character; the quotient curves are the −2-twists. 528 disks, no errors; ρ vanishes
  at the known points; Strassman index 2 everywhere; 504 zeros of ρ in X(Q₄₉₉) (252 disks with two, 276 with none);
  exactly four rational-looking coefficient vectors: a = (0, ±1) at (2, ±12) and (±1, 0) at (6/5, ±172/125).
* Sieve: the first prime above 997 kills 494 of 504, the primes above 12973 kill 6 more; the four survivors of all
  24 primes are the four known points.
* Precision check (step3_precision_check.gp, logs/step3_precision_check.log): recomputing ρ with 20 digits and O(T²⁰)
  reproduces the same Z₄₉₉-roots (to 8 digits) and the same zero counts on the tested disks; the coefficient
  valuations continue [·,1,1,2,3,…,18], so the truncation at O(T¹⁴) loses nothing.

### Conclusion
Combining: (i) the descent over Q(∛2) (every primitive solution comes from C₀ or C₁; §above), (ii) the étale double
covers sending C₁'s points to the hard pair, (iii) the quadratic-Chabauty determination X(Q) = {(1,±1), (−1,±15)} for
y² = −C3(x) and X(Q) = {(2,±12), (6/5, ±172/125)} for y² = 2C3(x), and (iv) Villines' classical Chabauty/2-Selmer
results for the four remaining twists (A± solved, B+ and C− empty), the primitive solutions of x⁴ + 2y³ + z³ = 0 are
exactly (±1, 0, −1), (±1, −1, 1), (±43, −203, 237) — **conditional on**:
  1. rank J(Q) = 2 for the hard pair (we proved ≥ 2; the upper bound is Villines' Magma 2-descent, not reproduced here);
  2. the imported facts in (iv) (Magma, Villines);
  3. the standard theory of p-adic heights behind the identity (Coleman–Gross/Nekovář heights, Bianchi–Padurariu's
     bielliptic formula generalised to a non-cyclotomic character over L — derived in this record, validated by the
     quadraticity tests, the 397 analysis and the sign test at the known points, but not yet checked against the
     literature: Dogra, "Unlikely intersections and the Chabauty–Kim method over number fields", is the reference);
  4. the usual QC precision conventions (PARI's rigorous p-adic error tracking; the series tail bounded by the observed
     linear growth of coefficient valuations, confirmed at higher precision).
What is new relative to the literature as far as we know: a quadratic Chabauty identity for Q-points built from a
Néron–Severi class that is only defined over a degree-12 field (the hidden Bolza involution), using the unique p-adic
character in its Galois-isotypic component, with the prime-2 and prime-3 contributions vanishing and the sieve made
index-free by the 499-integrality of the coefficient vector.

## 2-descent over Q for the hard pair (Sept 11–12): sel2/pipeline.gp — bugs found, final result, validation
Stoll's fake 2-Selmer group of J = Jac(y² = f(x)) for f irreducible of degree 6, implemented on PARI alone. Global part:
H(S) = (norm-square subgroup of L₆(S,2))/Q(S,2), from the S-units of the sextic field (class number 1; for a nontrivial
class group the pipeline adds primes generating its 2-part and re-imposes even valuations there). Local part at p ∈ S:
the image of J(Q_p)/2J(Q_p) under x − θ, in Hilbert-symbol coordinates w.r.t. a basis of ⊕_{P|p} L_P^×/L_P^{×2},
generated by Q_p-points and conjugate pairs of quadratic points until the theoretical dimension
d_p − ε_p = dim J(Q_p)/2J(Q_p) − [no odd-degree factor and no common quadratic subfield of the local factors] is
reached; at the real place, sign vectors. dim Sel²(J) = dim(fake group) + 1 (exact sequence μ₂ → Sel² → Sel²_fake → 0,
the kernel being nonzero here since f has no odd factor and L₆ no quadratic subfield; only ≤ is needed).
* **Result (logs/sel2/descent_Bminus.log, descent_Cplus.log).** B⁻: dim H(S) = 2 (S = {2,3,17}); local image dims
  1 (p = 2, from 72,289 quadratic pairs; f irreducible over Q₂, d = 2, ε = 1), 0 (p = 3), 1 (p = 17); fake Selmer
  group of dimension 1; **dim Sel²(J) = 2, J(Q)[2] = 0 ⇒ rank J(Q) ≤ 2**, so rank = 2 and Ш[2] = 0. C⁺: the same
  numbers (151 quadratic pairs at 2). This replaces the external rank bound (Villines' Magma) in the conclusion.
* **Three bugs found by validation, all fixed.** (1) PARI's bnfissunit orders exponents as [fundamental units,
  torsion, S-units]; the code assumed torsion first, so the quotient by Q(S,2) used shifted vectors (H(S) off by one
  on many curves). Now asserted by reconstructing −1 and the primes of S from the exponent vectors. (2) nfhilbert at
  primes above 2 gave a degenerate pairing (rank 2 of 6) in the defining polynomial c⁵f(y/c) (index divisible by 2⁵²
  on curve c20) but the correct rank 6 in the polredbest model; the pipeline now works in the reduced model and checks
  the local symbols against the product formula on 60 random pairs. (3) an empty local image at a prime with target
  dimension 0 crashed the imposition step and left the candidate space uncut (c13). Also added: the real-place
  condition (needed when f has ≥ 4 real roots: it cut c12, c16, c18 by one) and class-group support (c07: Z/2; c11: Z/3).
* **What the validation compares.** The database file gce_1000000_lmfdb.txt has 17 fields and no 2-Selmer column;
  field 13 is the analytic rank (earlier text called it "two_selmer_rank"; the tags "stollN" carry the analytic rank,
  and "cond" in the tags is the absolute discriminant). For a curve with a rational point and no 2-torsion,
  dim Sel² = rank + dim Ш[2] with dim Ш[2] even (Poonen–Stoll), so computed dim Sel² must be ≥ rank and ≡ rank (mod 2);
  the buggy versions gave rank + 1 on ten curves, which is impossible — that is how the bugs were caught.
* **Scorecard (logs/sel2/validation_scorecard.txt):** all 24 curves give dim Sel² = analytic rank (so Ш[2] = 0 for all
  of them, as expected for small conductors), including curves with 0, 2 and 4 real roots, class groups Z/2 and Z/3, a
  quadratic subfield of L₆ (c02, c21: no +1), and ranks 1, 2, 3. c00 and c17 (leading coefficient 4, a square in Q₂, so
  the curve has Q₂-points near infinity) at first had incomplete 2-adic images (flagged complete=[0,1,1]; 5.3 million
  quadratic pairs did not help): the standard search only samples x with denominator ≤ 4. Sampling x = a/2^j up to
  j = 9 completes both images at once (logs/sel2/validation_c00_rerun.log, validation_c17_rerun.log); the pipeline
  now falls back to this chart (and to quadratic points on x = 1/u) whenever the standard search falls short. The hard
  pair is unaffected: −17 and 34 are not squares in Q₂, so B⁻ and C⁺ have no Q₂-points with v(x) < 0, and their images
  had reached the theoretical dimension anyway.

## The twist set of Lemma A.3 and the three empty curves (Sept 12): twistset.py, sel2/fakeselmerset.gp, sel2/certify.gp
* **Twist set, derived (replaces the import from Villines).** δ = γ² lies on a smooth conic (Gram determinant 1 for
  k = 0, 1) parametrised through (1:0:0) by δ_k(s,t); with (s,t) coprime, δ = μ δ_k(s,t). The content of δ_k(s,t) is 1
  for s odd and 2 for s even (an odd common prime would divide s and t), γ² is primitive under the unit conditions
  (γ nilpotent mod p is excluded: Z[θ]/(p) is reduced for p ∤ 6, and the nilpotents mod 2, 3 are (θ), (θ+1)), so
  μ = ±1/content ∈ {±1, ±1/2}; for k = 0 the θ⁰-coordinate a² + 4bc of δ is odd while that of μδ₀(s,t) is μs², forcing
  s odd and μ = ±1. Result: exactly A± (k = 0), B∓ (k = 1, μ = ±1), C∓ (k = 1, μ = ±1/2) — Villines' six curves.
* **A⁻, B⁺, C⁻ have no rational points.** Bruin–Stoll fake 2-Selmer set: the norm condition alone is unsatisfiable —
  the S-unit norms of L_A (S = {2,3}) span ⟨−2, −3⟩ ∌ −1, those of L₆ (S = {2,3,17}) span ⟨−2, −3, −17⟩ ∌ 17, −34
  (while −17 and 34, the leading coefficients of B⁻ and C⁺, are in it). Both class groups certified trivial
  (bnfcertify; logs/sel2/certify.log). sel2/fakeselmerset.gp implements the full fake Selmer set (norm condition, real
  place, exact local images by disc subdivision): W = ∅ at the norm step for the three curves; for A⁺, B⁻, C⁺ it returns
  2, 1, 1 classes respectively (nonempty, as they must be — a check of the local machinery).
* **Remaining import:** A⁺(Q) = {∞±, (−1, ±3)} (Villines: rank 1, Chabauty at p = 5). Plan: rank ≤ 1 from
  sel2/pipeline.gp; Chabauty via the bielliptic structure over M = Q(∛2, √−2) (involution x ↦ −2∛4/x, fixed points
  ±∛2·√−2 ∈ M), linear in the elliptic logarithms at a prime split in M (p = 43), zeros on residue discs + sieve.

## A⁺(Q) = {∞±, (−1, ±3)} (Sept 12): aplus/, logs/aplus/
* **Rank 1.** sel2/pipeline.gp on f = x⁶ − 40x³ − 32 (S = {2, 3}): dim Sel²(J) = 1 (L_A has the quadratic subfield Q(√3), so
  no +1), J(Q)[2] = 0; D = [(−1,3) − ∞₊] has infinite order (ellorder of its images on the quotient curves over M);
  J(Q)_tors = Z/3 = ⟨[∞₋ − ∞₊]⟩ (gcd of #J(F_ℓ), ℓ < 400, is 3).
* **Bielliptic structure** (aplus/bi_Aplus.gp): the involution x ↦ −2∛4/x, lifted with 4√−2, over M = Q(⁶√−2) (degree 6);
  fixed points ±w⁵; even model Y² = AX⁶ + BX⁴ + CX² + D with A, B, C, D ∈ Q(√−2); quotients E₁, E₂ with j = 8000 (CM by
  Z[√−2]), quadratic twists of each other by −2, conductor norm 9, E_i(M)_tors = Z/6.
* **Chabauty at p = 43 (split in Q(√−2)) fails structurally** (aplus/linchab_Aplus.gp, sieve_Aplus.gp): 66 zeros of the
  linear Chabauty function on the 64 residue discs; 4 rational, 12 algebraic torsion classes (x³ = 2, x³ = −16; exact over
  Q(⁶√−2, √−3), aplus/tors12.gp), 50 others; the 43-part Mordell–Weil sieve (q ≤ 60000) leaves 14, among them the
  Q(√−2)-points (2, ±12√−2), (±2√−2, ±(16 ± 20√−2)). Reason: 43 splits in Q(√−2), the CM action of Z[√−2] on E_i is
  compatible with the 43-adic logarithms, and J(Q(√−2)) ⊗ Q₄₃ maps onto the same line as J(Q) — Chabauty at a split prime
  sees the Q(√−2)-points. (The zeros come in consecutive-coefficient families a, a ± 1: translates by D.)
* **Chabauty at p = 5 (inert in Q(√−2)) succeeds** (aplus/chab5_Aplus.gp; M_𝔭 = Q₂₅, formal-group logarithms and group law
  written out, E₂ ≅ E₁ over Q₂₅ so one component of ρ vanishes identically): A⁺(F₅) has 6 points, hence 6 discs; the
  condition (L₁, L₂)(z) = λ (L₁(D), L₂(D)), λ ∈ Q₅, holds at (−1, ±3) with λ = ±1 exactly; Strassman indices 1,1,2,2,1,1; 8
  zeros: ∞±, (−1, ±3), the torsion point (−2∛2, ±12√6) (λ = 0), and one pair in the disc x ≡ 1 with λ ≡ ±8316 (mod 5⁶).
* **Sieve** (aplus/sieve5_Aplus.gp): 5 ∤ index (v₅(L_i(D)) = 1); primes of M with 5⁴ | #E_i: q = 149 (|S| = 175/625),
  q = 599 (|S| = 275/625) — the pair is excluded at 599, the known points' residues 0, ±1 survive. Hence
  **A⁺(Q) = {∞±, (−1, ±3)}**, as Villines found with Magma (his model has x ↦ −x).
* With this, every ingredient of the theorem is proved in this record (modulo the cited theorems of Balakrishnan–Dogra and
  BBBM and standard Coleman-integration / p-adic-height theory); Villines' Magma results are now all reproduced.

## Second-prime check of Part C (Sept 12): p = 1459 — second_prime/make_p1459.py, logs/p1459/
* Same pipeline with p = 1459 (next completely split prime of L with no root of C₃ mod p): character unique and zero
  above 2, 3; calibration and parallelogram law to O(1459¹⁹); ρ(P₁) = ρ(P₂) = −Ω₃₉₇ to O(1459¹⁹) on both curves;
  #E(F_𝔭) = 1462 at all places. 1464 disks per curve; Strassman index 2 everywhere except the two infinity disks
  (index 1); zeros: 1546 (B⁻), 1426 (C⁺). Sieve primes: degree-1 primes above 2917, 26261, 96293 (q ≡ −1 mod 1459).
* **B⁻: exactly the four known points survive** (2917 kills 1538, 26261 the remaining impostors).
* **C⁺: exactly the four known points survive**, after one fix: in the two disks x ≡ 103 the 14-digit run reported the
  two zeros with coefficient vectors of zero precision (the logarithms at places 1, 2 collapse there; the disk is not
  one of the 24 special disks). Recomputing the disk with 22 digits reproduces the zeros to five digits and gives
  ordinary coefficient vectors, which the prime above 2917 removes. Lesson for the write-up: the precision of the
  coefficient vectors must be checked disk by disk, not only the precision of ρ.
* This is the independent-prime confirmation of Props. C.3–C.6 asked for in step 2 of the publication plan.
