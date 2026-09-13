# How I got here: from a paper about AI to x⁴ + 2y³ + z³ = 0

I've always loved puzzles and knowing how things work, and AI has made it easier to dig into new things. This is the
story of how, over four days in September 2026, a wish to understand one paper about artificial intelligence turned
into a probable solution of a hundred-year-old kind of number puzzle. It was not planned. Most of it happened because
each experiment answered one question and raised a better one.

## The paper I wanted to understand

In October 2025 Pedro Domingos published "Tensor Logic: The Language of AI". Its central claim is simple and bold: a
logical rule and an Einstein summation are the same operation, so neural networks and symbolic reasoning can be
written in one language, and reasoning can be done in "embedding space" without the hallucinations of language
models. I wanted to know whether that was true, not just read that it was.

Ten years ago that would have meant weeks of coding before the first result. Now I could describe the experiment I
had in mind and have it running in an hour. On September 9 I asked Claude for a set of experiments extending the
paper and said "go ahead with the first three". By that night we had formulas: the error of a superposed embedding
is exactly Φ(−√(D/N)/2), you need about ninety dimensions per stored item for one error in a million, and chaining
rules in embedding space has a sharp cliff, a critical dimension around two hundred times the largest closure degree,
below which nothing works. The next day we tested the paper's "temperature dial" for analogical reasoning and found
it maximally hallucinatory at every temperature; the only reliable corner was the purely deductive one. The kindest
honest summary of the first five experiments was that the advantage the paper describes belongs to computing the
logical closure exactly, not to the embeddings.

That was the first lesson of the whole adventure: with an AI collaborator that can implement and run an experiment
while you think about the next one, you can test a paper's claims instead of taking them on faith.

## Learning rules, and then learning arithmetic

If embedding-space reasoning was the weak part, the learning part was stronger than I expected. A learnable rule
tensor recovered all 62 kinship rules of a standard benchmark from about four hundred stories. Then came the
experiment that changed my sense of what was possible: from 25 examples of addition and 16 of multiplication in unary
notation, gradient descent through an exact rewriting engine learned the Peano axioms, the true ones and only the
true ones. Given only multiplication examples and a spare symbol, the system invented addition, because addition is
the unique helper function that makes multiplication computable. Given exponentiation, it invented multiplication.
We added equality saturation, Knuth–Bendix completion, Gröbner bases; a loop that conjectures in finite models and
proves by saturation found and proved 22 theorems about groups on its own. Along the way we wrote the tensor-logic
findings up as a paper of their own.

By then a different question was nagging me. All of this proved things that were already known. Could the machinery
prove something new?

## Trying to prove something new

The first attempt was the OEIS, the online encyclopedia of integer sequences. We built a machine for sequences that
satisfy linear recurrences: it validated 35,857 recurrences against the listed terms, proved 108,547 identities
between sequences in eight minutes, and proved 5,779 closed forms unconditionally. It solved exactly zero open
conjectures. The lesson was worth having: the machinery was real, and the open problems were open for a reason.

So we went where the open problems are stated precisely: Diophantine equations. We built a verifier for Chabauty's
method, the classical way to find all rational points on a curve of genus 2 when the rank of its Jacobian is
smaller than 2, and turned it into a "certificate factory" on a public database of 66,158 genus-2 curves. It
determined the rational points on 108 of the first 200 eligible curves.

And it had a bug. The Mordell–Weil sieve, the step that eliminates false candidates, assumed two things it should
have proved: that it had found all the torsion, and that its generator was not a multiple of a smaller point. A batch
check comparing bounds with known points could never have caught this, because a false exclusion looks exactly like a
correct one. We found it by asking what each step actually assumed, fixed it with certified saturation witnesses,
and 21 of 46 earlier sieve claims had to be withdrawn. That was the most important lesson of the whole project, and
it shaped everything that followed: every input to a sieve must be proved, and a computation that has not been
validated against an independent source is not evidence.

Two more experiments mattered later. One was a proposer for "bielliptic" curves, curves with a hidden symmetry that
splits their Jacobian into two elliptic curves: it computed the roots of the defining polynomial to sixty digits,
searched pairings of roots for a Möbius symmetry, rationalised the result and verified it exactly. It found the
symmetry on 1,111 of 1,111 candidate curves in 34 seconds, including deliberately disguised ones, and pushed 63 curves
past what Chabauty alone could do. A language-model arm of the same experiment produced no output in an hour and was
stopped; the numerical method had solved the problem completely. The other was writing the sieve itself as one of
the paper's tensor equations: correct, elegant, and useless, slower than the plain exact version. I recorded that
too.

## The equation

A 2024 survey by Ratcliffe and Grechuk lists generalized Fermat equations ordered by a size measure H and marks the
ones nobody has solved. The smallest open one was

  x⁴ + 2y³ + z³ = 0,

with H = 40. Three primitive solutions are known: (±1, 0, −1), (±1, −1, 1) and (±43, −203, 237). The last one is a
warning that a computer search proves nothing.

On September 11 we started a separate line of work on it. The classical attack went smoothly: factor in the number
field Q(∛2), which has unique factorisation and a single fundamental unit; conclude that z + y∛2 is a unit times a
fourth power; expand and get four plane quartic curves; kill two of them by 2-adic arguments; pass to a conic and its
Pythagorean-style parametrisation; arrive at six curves of genus 2. Halfway through, we found that Greg Villines had
done exactly this in June 2026, with Magma, and had solved four of the six curves. The other two had rank 2, equal to
the genus, and everything stopped there. His notes suggested trying quadratic Chabauty over Q(√−2). We computed the
Galois action on the Néron–Severi group and showed that route cannot work: over Q(√−2) there is still no extra class.

We were at the same wall, with better tools than I had expected to own.

## The trick

I asked a naive question: is there a way to use the paper and our learning techniques to develop a new method for
quadratic Chabauty? The honest answer, in hindsight, is that the paper had nothing to say, but the habit from the
bielliptic experiment did. The two hard curves are twists of the Bolza curve, which has 48 symmetries over the complex
numbers. We found them numerically, exactly as the proposer had done for the database curves, and identified them
exactly. Six of them are involutions, and each is defined over a field of degree 12. Over that field each hard curve
is bielliptic, and quadratic Chabauty for bielliptic curves over number fields exists, in work of Balakrishnan,
Besser, Bianchi and Müller. But their function lives on the points over the big field, and we only cared about
rational points.

The computation that turned into the idea was counting points modulo many primes to work out how the Galois group
shuffles the 48 symmetries. The Néron–Severi group turned out to be one trivial class plus a three-dimensional
irreducible piece, and complex conjugation flips exactly one class: the class of our involution. That single flipped
sign suggested a rule. The quadratic Chabauty function over the big field is a sum over the twelve embeddings,
weighted by a p-adic character of the field; for a rational point the twelve contributions are permuted by Galois,
and only the part of the character that transforms like the flipped class survives. We called it the sign rule. The
units of the field then cut the candidates down to exactly one character. Then a small miracle: that character
vanishes at every prime above 2 and 3, exactly the primes where the elliptic quotients have bad reduction, so the
usually painful bad-prime terms simply disappear.

We built the function at p = 499. It took the same value at both known points to nineteen digits, and the version
with the opposite sign of one term failed, which told us the derivation was right rather than lucky. On the 528
residue disks it had 524 zeros; a Mordell–Weil sieve, made index-free by a divisibility property we could prove,
removed all but the four known points. The twisted curve behaved the same way. Only afterwards did we find that a
theorem of Balakrishnan and Dogra predicts finiteness from exactly the count we had computed. The finiteness was
theirs; the explicit identity for Q-points, built from a class defined only over an extension field, appears to be
new.

## Closing every gap

A proof that borrows its hardest inputs is not a proof, so the next day went into removing every import. We wrote our
own 2-descent in PARI/GP to bound the rank, following Stoll's 2001 algorithm, and validated it against 24 database
curves. Our first version was off by one on half of them. It turned out I had misread a column of the database file:
what I took for a 2-Selmer rank was the analytic rank. That made the test sharper, not weaker, because for those
curves the two numbers must have the same parity, and "rank + 1" is impossible. Chasing the parity violation exposed
three genuine bugs, including one in how PARI orders the exponents of S-units and one where its local symbols
misbehave unless the number field is given by a reduced polynomial. After the fixes, 24 of 24 curves agreed.

We re-derived the list of six curves from first principles with an elementary argument about common factors. We
proved three of the easy curves empty with a norm condition on certified class groups. The fourth easy curve taught
one more lesson: at the prime 43 the method kept insisting on ghost points with coordinates in Q(√−2), because 43
splits in that field and the complex multiplication makes those points indistinguishable from rational ones; at the
inert prime 5 the ghosts vanished, which is the prime Villines had used. We repeated the entire hard-pair computation
at a second prime, 1459, and it gave the same four points, after one disk taught us to check the precision of every
quantity the sieve consumes and not only of the function itself.

Then the writing: a formal proof record, a narrative companion, a chronological lab record with every bug in it, a
referee's checklist stating exactly which published theorems the argument rests on and what an expert should check
first, explanations for a general reader, and finally a fifteen-page paper with licences chosen. The proof, its code
and its logs now live in a repository of their own.

## Where it stands

I am careful to say "probable solution". Every part of the proof is in the record and reproducible on free software,
and the two computations that could be cross-checked against Villines' independent Magma work agree with it. What
remains is what always remains: an expert should read the new step, someone should redo the delicate computations
with different software, and the paper should go through review. Until then it is a complete argument that has not
yet been refereed, and I would rather say that plainly than claim more.

## What I learned

The AI did not "solve" the equation, and neither did I. What happened is that a curious person could run a four-day
research program that would have taken a small team months: read the papers, implement a twenty-five-year-old
algorithm, run tens of thousands of computations, catch its own mistakes by validation, and write everything up at
three levels of difficulty. My part was steering: choosing the target, insisting on checks, refusing to import what
could be proved, and asking for the explanation "like I'm 12" often enough to be sure I understood what I was
signing. The best idea in the whole story came from a computation, not from a theory, and the second-best from
distrusting a computation. That is how puzzles have always worked; the difference is how far one person can now dig.
