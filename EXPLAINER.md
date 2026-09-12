# How we solved x⁴ + 2y³ + z³ = 0, for a general reader

*This is the story of the proof in PROOF.md, told without the heavy machinery. Where I use a technical word I try to
say what it means and, more importantly, what it is for.*

## 0. The problem and the answer

We want all whole numbers x, y, z with

  x⁴ + 2y³ + z³ = 0

that have no common factor (if x, y, z share a factor you can divide it out, so "primitive" solutions are the only
interesting ones). A few solutions are easy to find by hand or by a small computer search:

| x | y | z | check |
|---|---|---|---|
| ±1 | 0 | −1 | 1 + 0 − 1 = 0 |
| ±1 | −1 | 1 | 1 − 2 + 1 = 0 |
| ±43 | −203 | 237 | 3418801 − 16730854 + 13312053 = 0 |

The theorem is that these are the only ones. The last one is a warning: solutions can be much bigger than you would
guess, so "we searched up to a billion and found nothing else" is not a proof.

Equations of the form x^a + y^b + z^c = 0 (with coefficients allowed) are called generalized Fermat equations. A 2024
survey by Ratcliffe and Grechuk listed the smallest ones that were still open, ordered by a size measure H, and this
one, with H = 40, was the smallest open case. Greg Villines had attacked it in June 2026 and got most of the way; we
finished it, and along the way found a trick that may be useful for other equations.

## 1. Why a small equation can be hard

For x² + y² = z² you can write down all solutions with a formula. For xⁿ + yⁿ = zⁿ with n ≥ 3 there are none, but
proving that took 350 years. Mixed exponents like (4, 3, 3) are in a strange middle zone: a deep theorem (Faltings,
Darmon–Granville) says there are only finitely many primitive solutions, but it gives no way to find them. Every
equation needs its own attack, and the standard attacks come in two flavours:

- **Factor cleverly**, in a bigger number system where the equation splits into pieces, and use the arithmetic of that
  number system to force the pieces to have a special shape. This reduces the equation to finding rational points on
  a handful of curves.
- **Find all rational points on those curves.** For curves of "genus 2" (explained below) there are powerful but
  finicky methods, and they only work when a certain number, the rank, is smaller than the genus. When it is not,
  you are stuck. That is exactly where this equation got stuck.

## 2. Step A: factoring with the cube root of 2

Write θ for the real cube root of 2. In the number system Z[θ] = {a + bθ + cθ² : a, b, c whole numbers} the cubic part
of our equation factors:

  z³ + 2y³ = (z + yθ)(z + yθω)(z + yθω²)

where ω is a complex cube root of 1. So the equation says: the "norm" of the number α = z + yθ (the product of its
three conjugates) equals −x⁴, a fourth power up to sign.

Z[θ] behaves a lot like the ordinary integers: it has unique factorisation (in the language of the trade, "class
number 1"), and its only "units" (numbers that divide 1) are ±1 and powers of ε = θ − 1. Because the three factors
above share no common prime (that is where "primitive" is used), the fourth power on the right forces each factor to
be a unit times a fourth power:

  z + yθ = −εᵏ·γ⁴,  with γ ∈ Z[θ] and k ∈ {0, 1, 2, 3}.

Now write γ = a + bθ + cθ² and expand −εᵏγ⁴. The left side has no θ² term, so the θ²-coefficient of the right side
must be zero. That is one polynomial equation in a, b, c of degree 4: a plane curve C_k. There are four of them (one
per k); two are ruled out by looking at the equation modulo powers of 2. So every primitive solution comes from a
rational point on C₀ or C₁, with two extra "unit conditions" (a odd, and a − b + c not divisible by 3) that record
the fact that γ shares no factor with 2 or 3.

## 3. Step A, continued: from quartics to six genus-2 curves, and the twist set

C₀ and C₁ have genus 3, which is too high for our tools. But they have a hidden structure: set δ = γ². The condition
on γ becomes a condition on δ that is only quadratic, a conic. Conics are the friendliest curves there are: once you
know one rational point, you can write down all of them with a formula in two parameters (s, t), exactly like the
formula for Pythagorean triples. So

  δ = μ·δ_k(s, t)  for some rational number μ and coprime integers s, t,

where δ_k(s, t) is an explicit quadratic expression. Taking norms of both sides (remember δ = γ², so its norm is a
square) gives

  w² = μ·f_k(s, t),  with f_k a polynomial of degree 6.

An equation w² = (degree 6 polynomial) defines a curve of genus 2. So each rational point of C_k lands on one of the
genus-2 curves H_μ: w² = μ f_k(x) (x = s/t), and which curve depends on μ.

Here is the first small trick, and it is elementary. The number μ is forced by a "content" argument: δ_k(s, t) is a
triple of integers whose greatest common divisor can only be 1 or 2 (an odd prime dividing all three would divide
both s and t). Since δ = γ² has coprime coordinates (this uses the unit conditions), μ must be ±1 or ±1/2. For k = 0
even ±1/2 is impossible, by looking at one coordinate modulo 2. So we end up with exactly six curves:

| name | equation | points we know |
|---|---|---|
| A⁺ | y² = x⁶ − 40x³ − 32 | two points at infinity, (−1, ±3) |
| A⁻ | y² = −(x⁶ − 40x³ − 32) | none |
| B⁺ | y² = C₃(x) | none |
| B⁻ | y² = −C₃(x) | (1, ±1), (−1, ±15) |
| C⁺ | y² = 2C₃(x) | (2, ±12), (6/5, ±172/125) |
| C⁻ | y² = −2C₃(x) | none |

with C₃(x) = 17x⁶ − 72x⁵ + 90x⁴ + 40x³ − 180x² + 144x − 40. The point (6/5, ±172/125) on C⁺ is the 43-solution in
disguise. Villines had found these same six curves with Magma; we re-derived the list from scratch so that nothing in
the proof depends on software we could not run.

## 4. Interlude: the toolkit for genus-2 curves

- **Genus.** If you draw a curve over the complex numbers you get a surface; the genus is its number of holes. A line
  or a conic has genus 0 (a sphere), an elliptic curve y² = cubic has genus 1 (a doughnut), and y² = sextic has genus 2
  (a pretzel with two holes). Faltings' theorem: genus ≥ 2 means only finitely many rational points.
- **Elliptic curves and the Jacobian.** Points on an elliptic curve can be "added": the line through two points meets
  the curve in a third, and that defines a group law. A genus-2 curve does not have a group law itself, but it comes
  with a two-dimensional object, its Jacobian J, that does. Rational points of J form a group of the form
  Zʳ × (finite). The number r is the **rank**: how many independent "generators" you need.
- **Chabauty's method.** Instead of ordinary numbers use p-adic numbers, where p is a prime: numbers written in base
  p with possibly infinitely many digits to the left of the point, and where two numbers are "close" when they agree
  in many low digits. In the p-adic world the Jacobian becomes a smooth 2-dimensional space, and the rational points
  of J form an r-dimensional "sheet" inside it. The curve itself is a 1-dimensional sheet. If r < 2, a 1-dimensional
  thing and a (less than 2)-dimensional thing inside a 2-dimensional space meet in only finitely many points, and you
  can write down a p-adic analytic function (a power series) that vanishes exactly at those meeting points. Then you
  find its zeros disk by disk and check which ones are actual rational points. This is Chabauty–Coleman. When r = 2 =
  genus the two sheets can meet in a curve and the method gives nothing. That is "the wall".
- **Quadratic Chabauty.** When r = genus, one can sometimes still write down a function that vanishes at all rational
  points, using **p-adic heights**: a p-adic measurement of the arithmetic size of a point that behaves like a
  quadratic form (like |v|² for vectors). The catch is that this only works if the Jacobian has an extra symmetry of a
  specific kind, a "Néron–Severi class" beyond the obvious one. Over Q, our hard curves have no such class. That is
  where Villines stopped, and where the new idea comes in.

## 5. Step B: the four easy curves

**A⁻, B⁺, C⁻ have no rational points at all.** The argument is a souped-up version of "there is no solution because
the two sides have different remainders modulo 4". A rational point (x, y) on y² = f(x) gives the algebraic number
x − θ (θ now a root of f) whose norm is y² divided by the leading coefficient of f. One shows that x − θ must be a
unit-like element (an "S-unit") of the number field defined by f, up to squares, and then computes all the norms such
elements can have modulo squares. For these three curves the required norm class (−1, 17 and −34 respectively) is not
on the list. So there is no point. (For B⁻ and C⁺ the required classes −17 and 34 are on the list, as they must be,
since those curves do have points.)

**A⁺ has rank 1**, so Chabauty works, but it taught us a lesson. A⁺ has a hidden symmetry x ↦ −2∛4/x defined over the
field Q(⁶√−2) that makes it a double cover of two elliptic curves with "complex multiplication" by Z[√−2]. We first
ran Chabauty at the prime p = 43 and found 66 zeros of the function on 64 residue disks, of which only 4 were rational
points. A sieve removed most of the rest but a stubborn few survived, including points with coordinates in Q(√−2).
The reason is pretty: 43 splits in Q(√−2), and at such a prime the complex multiplication makes the p-adic logarithms
of all Q(√−2)-points line up with those of the Q-points, so Chabauty "sees" Q(√−2)-points as if they were rational.
At p = 5, which does not split in Q(√−2), the same computation has only 8 zeros: the 4 rational points, one algebraic
point whose class is torsion (verified exactly), and one pair that a sieve kills. So A⁺(Q) has exactly the four known
points. Villines had used p = 5 too, which in hindsight was the right call.

## 6. Step C: the hard pair and the wall

B⁻ and C⁺ (they are twists of each other, so everything said about one applies to the other) have Jacobians of rank 2,
equal to the genus. Chabauty–Coleman is useless. Quadratic Chabauty needs an extra Néron–Severi class over Q, and there
is none: we computed the Galois action on the Néron–Severi group from Frobenius traces at many primes, and over Q, and
even over Q(√−2), there is only the trivial class. Villines had suggested trying quadratic Chabauty over Q(√−2); this
computation shows that route cannot work.

## 7. The new trick, and how we found it

The curves B⁻ and C⁺ are secretly very symmetric. Over the complex numbers each has 48 automorphisms (they are twists
of the famous Bolza curve y² = x⁵ − x). Over Q only the boring symmetry y ↦ −y survives. But we asked: over which
fields do the other symmetries appear? We computed the six extra involutions explicitly. Each is a Möbius map
x ↦ (−x + b)/(cx + 1) permuting the six roots of C₃, and each is defined over a specific number field L of degree 12,
L = Q(∛2, √(∛2 − 1), √(1 + bc)). Over L the curve becomes "bielliptic": the involution has two fixed points, and
dividing by it (and by its composite with y ↦ −y) gives two elliptic curves E₁, E₂. Quadratic Chabauty for bielliptic
curves over number fields is well understood (Balakrishnan, Besser, Bianchi and Müller wrote down the explicit
function). But their function lives on the L-points of the curve, and there are infinitely many things that can go
wrong when you only care about Q-points: the extra symmetry is not defined over Q, so how can it constrain Q-points?

The discovery came from a computation, not from a theorem. When we worked out how the Galois group of the big field
acts on the Néron–Severi group (a 4-dimensional space), we found the pattern 1 ⊕ (a specific 3-dimensional irreducible
piece), and that complex conjugation acts on it with eigenvalues (1, 1, 1, −1). Exactly one class is flipped by
complex conjugation, and it is the class Z of our involution. That single −1 turned out to be the key.

Here is the idea in plain words. The quadratic Chabauty function over L is a sum over the twelve embeddings of L into
the p-adic numbers (we chose p = 499, a prime that splits completely in L). Each term is weighted by the local value
of a "p-adic character" χ of L, a kind of p-adic logarithm on the ideals of L, and there are many such characters to
choose from. For a Q-point of the curve, the twelve embeddings are permuted among themselves by Galois symmetry, so
most of the character is "averaged away". What survives is exactly the part of the character that transforms under
Galois in the same way as the class Z. We called this the **sign rule**: the class and the character must live in the
same Galois-symmetry type, or the identity collapses to 0 = 0. We then checked how many characters live in that
symmetry type: the p-adic logarithms of the six fundamental units of L cut the 3-dimensional space down to exactly one
character, up to scaling. So there is precisely one candidate function, and it is completely determined.

Then a small miracle: that character vanishes at all the primes above 2 and 3, which are the only primes where the
elliptic curves E₁, E₂ have bad reduction. Normally the hardest part of a quadratic Chabauty computation is working out
what happens at bad primes. Here those terms are simply zero, and the only correction comes from two primes above 397
where our chosen equations for E₁, E₂ are not in their simplest form. That correction is a constant Ω₃₉₇ that we
computed by a short case analysis.

Only after we had the identity working did we check the literature properly, and found that our sign rule is a special
case of a finiteness theorem of Balakrishnan and Dogra: quadratic Chabauty gives a finite set of p-adic points when
rank < (genus − 1) + (number of independent classes over Q) + (number of classes flipped by complex conjugation).
For us that is 2 < 1 + 1 + 1. So the finiteness was predicted by their theorem; the new part is making the function
explicit and computable, by combining the bielliptic structure over L with the unique matching character. As far as we
know this is the first time a quadratic Chabauty identity for Q-points has been built from a class that is only defined
over a bigger field.

## 8. Making it compute

The function ρ(z) has three pieces: p-adic heights of the images of z on E₁ and E₂ (computed with Mazur–Tate's
"sigma function", one for each of the twelve embeddings), a logarithm term, and a quadratic term aᵀGa that records
where [z − ιz] sits among the two generators of the Jacobian's rational points. We tested every piece separately: the
heights satisfy the parallelogram law h(P + Q) + h(P − Q) = 2h(P) + 2h(Q) to 19 digits, h(2P) = 4h(P), and the whole
identity ρ(z) = −Ω₃₉₇ holds at the known points to 19 digits, while the version with the opposite sign of the log term
fails. (That sign test caught a real error in our first derivation.)

Then the main computation: the curve has 528 "residue disks" over the 499-adic numbers (one for each point modulo
499, with the two square roots of y counted separately, plus two disks at infinity). On each disk we expanded ρ as a
power series in the disk coordinate and used Strassman's theorem, which bounds the number of zeros of a p-adic power
series by looking at the sizes of its coefficients. Every disk allowed at most 2 zeros, and we found 524 zeros in total
for B⁻ and 504 for C⁺. Only 4 of them on each curve are rational points; the rest are 499-adic points that happen to
satisfy the identity.

To get rid of the other 520 we used a Mordell–Weil sieve: a rational point must also make sense modulo other primes q,
and its "coordinates" a(z) in terms of the generators must be consistent between what we see 499-adically and what we
see modulo q. This works well when 499 divides the number of points on E₁ and E₂ modulo q, which happens for q = 997,
12973, 47903, 59879, 88339. The prime 997 alone kills 518 of the 524 candidates; 12973 kills the last two impostors.
The four survivors are the four known points, on each curve. A normally delicate issue, the "index" of the subgroup
generated by our two known points inside the full group of rational points, disappears here because all the p-adic
logarithms are divisible by 499 in just the right way.

## 9. Step D: proving the rank really is 2

Everything above assumes rank J(Q) = 2 for the hard pair. Finding two independent points shows rank ≥ 2. For the upper
bound we implemented Stoll's 2-descent ("fake 2-Selmer group") ourselves on PARI/GP: it computes a finite group that
contains J(Q)/2J(Q), by combining global information (units of the degree-6 field defined by C₃) with local
information at the primes 2, 3, 17 (which classes are hit by actual 2-adic, 3-adic, 17-adic points). The result is
dim Sel²(J) = 2, hence rank ≤ 2.

This is where honesty about mistakes matters. Our first implementation gave answers that were off by one on about
half of a set of 24 test curves from the LMFDB database. We had misread what we were comparing against (the file
column we took for a 2-Selmer rank was the analytic rank), but that made the test sharper, not weaker: for these
curves the dimension of the 2-Selmer group must have the same parity as the rank, so "rank + 1" was impossible.
Chasing that parity violation exposed three genuine bugs: PARI orders the exponents of S-units differently from what
we assumed, PARI's local Hilbert symbols at primes above 2 misbehave unless the number field is given by a reduced
polynomial, and an empty local image at one prime crashed a step silently. After the fixes, all 24 test curves agree
with the database, including curves with four real roots, nontrivial class groups and ranks 1, 2 and 3. Two test curves
also revealed that our point search missed 2-adic points near infinity; the fix did not change anything for the hard
pair, whose leading coefficients make such points impossible, but the pipeline is now complete.

## 10. Checking ourselves

- The whole quadratic Chabauty computation was repeated at a second prime, p = 1459, the next prime with the right
  splitting behaviour. Everything reproduced: the character is again unique and vanishes above 2 and 3, the heights
  again satisfy the parallelogram law, the identity again holds at the known points to 19 digits, and after the sieve
  (this time with primes above 2917, 26261 and 96293) exactly the four known points survive on each curve. The numbers
  are bigger, 1464 disks per curve and 1546 resp. 1426 zeros of ρ, because the number of disks grows with p.
- That rerun also taught us something. On C⁺ one disk came out of the standard 14-digit computation with two zeros
  whose "coefficient vectors" a(z), the numbers the sieve needs, had no correct digits at all, so the sieve could not
  touch them and for an hour they looked like mysterious extra points. Redoing that single disk with 22 digits gave the
  same two zeros to five digits and perfectly ordinary coefficient vectors, which the first sieve prime removed. The
  lesson, now written into the proof: check the precision of a(z) on every disk, not only the precision of ρ.
- We wrote a referee's checklist (REFEREE_NOTES.md) that states exactly which published results the new step relies
  on, with the hypotheses used, what is proved versus verified numerically, and five questions for an expert.
- Villines' independent Magma computations agree with ours wherever they overlap: the six curves, the ranks, the
  emptiness of A⁻, B⁺, C⁻, and the four points of A⁺.
- Each numerical convention (signs, factors of 2, PARI's division-polynomial quirks) is pinned by an explicit test
  rather than assumed.

## 11. What is proved, what is assumed, what is next

Proved in the record, by exact computation or by argument: the reduction to six curves including the twist set, the
emptiness of three curves, the points of A⁺, the rank bounds, the identity, the zeros, the sieve. Assumed from the
literature: the theory of p-adic heights on elliptic curves over number fields (Mazur–Tate; Balakrishnan–Besser–
Bianchi–Müller), Coleman integration on residue disks, and the correctness of PARI/GP. What remains before this can be
called a publication: an expert look at Part C (REFEREE_NOTES.md lists exactly what to check; the second-prime check
is done), a second independent implementation of the delicate pieces, coordination with Villines, and a proper paper.

If there is one thing to take away: the wall was "no extra symmetry over Q". The way through was to notice that the
symmetry existed over a bigger field, to compute exactly how Galois shuffles the symmetries, and to see that the one
class flipped by complex conjugation can be paired with the one p-adic character of the same type to produce an
equation that rational points must obey.
