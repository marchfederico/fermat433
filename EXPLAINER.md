# How we solved x⁴ + 2y³ + z³ = 0

*An explanation of the proof in PROOF.md for someone who knows school algebra and is curious about the rest. You
don't need calculus. When a technical word appears, it comes with what it means and why it matters.*

## 1. The puzzle

Find all whole numbers x, y, z (positive, negative or zero) with

  x⁴ + 2y³ + z³ = 0.

If x, y and z share a common factor, you can divide it out and get a smaller solution, so we only look for solutions
with no common factor. Mathematicians call these *primitive*.

A few solutions turn up quickly:

| x | y | z | check |
|---|---|---|---|
| ±1 | 0 | −1 | 1 + 0 − 1 = 0 |
| ±1 | −1 | 1 | 1 − 2 + 1 = 0 |
| ±43 | −203 | 237 | 3,418,801 − 16,730,854 + 13,312,053 = 0 |

**The theorem: there are no others.**

That third row is a warning. Nobody would guess 43, −203, 237. So a computer search ("we tried everything up to a
billion and found nothing new") proves nothing: the next solution could be bigger than a billion. We need a proof
that covers every number at once.

## 2. Why such a short equation is hard

You know x² + y² = z². It has infinitely many solutions (3, 4, 5; 5, 12, 13; …) and there is a formula for all of
them. You may also have heard of Fermat's Last Theorem: xⁿ + yⁿ = zⁿ has no solutions in positive whole numbers once
n is 3 or more. It took 350 years to prove.

Equations like ours, with different powers (4, 3, 3), sit in between. A deep theorem says there are only finitely many
primitive solutions, but it doesn't say how to find them. Each equation needs its own proof.

A 2024 survey by Ratcliffe and Grechuk listed the simplest equations of this kind that nobody had solved, ordered by a
"size" score. Ours, with score 40, was the smallest unsolved one. Greg Villines got most of the way in June 2026. We
finished it, and found a trick along the way that might help with other equations.

The proof has the shape of a funnel. Step by step, the infinitely many possible (x, y, z) get squeezed through
narrower and narrower checks, until only the known solutions fit through.

## 3. Step A: a bigger number system

### Factoring with ∛2

Let θ be the cube root of 2, so θ³ = 2. Allow yourself numbers of the form a + bθ + cθ², with a, b, c whole numbers.
You can add and multiply these, and whenever θ³ appears you replace it with 2. In this number system z³ + 2y³ splits
into factors, just as a² − b² = (a − b)(a + b) does with ordinary numbers.

This number system behaves like the ordinary integers in one crucial way: every number factors into "primes" in only
one way. (That fails in many similar systems, which is part of what made Fermat's Last Theorem so hard.) Using it, the
equation forces z + yθ to have a very particular shape:

  z + yθ = −(a unit)·γ⁴, for some γ = a + bθ + cθ².

A *unit* is a number that divides 1, like ±1 in ordinary integers. Here there are more units, but only four cases
matter. And γ⁴ is a fourth power, which echoes the x⁴ in the original equation.

### From one equation to six curves

Now expand the right-hand side. The left side, z + yθ, has no θ² term, so the θ² part of the right side must be zero.
That gives a new equation in a, b, c. After some algebra, two of the four cases die immediately: look at everything
modulo 2, and the equation simply can't balance. That's the same kind of argument as "an odd number can't equal an
even number", just dressed up.

More algebra (a trick with δ = γ², and the same formula idea that produces all Pythagorean triples) turns what's left
into equations of the form

  y² = (a polynomial of degree 6 in x),

where x and y are now *fractions*, not just whole numbers. We get exactly six of them:

| name | equation | points we know |
|---|---|---|
| A⁺ | y² = x⁶ − 40x³ − 32 | (−1, ±3), and two "at infinity" |
| A⁻ | y² = −(x⁶ − 40x³ − 32) | none |
| B⁺ | y² = C₃(x) | none |
| B⁻ | y² = −C₃(x) | (1, ±1), (−1, ±15) |
| C⁺ | y² = 2C₃(x) | (2, ±12), (6/5, ±172/125) |
| C⁻ | y² = −2C₃(x) | none |

Here C₃(x) = 17x⁶ − 72x⁵ + 90x⁴ + 40x³ − 180x² + 144x − 40.

Every solution of the original puzzle produces a point with fraction coordinates on one of these six *curves*. So if we
can find **every** fraction point on all six curves, we're done. The point (6/5, 172/125) on C⁺ is the 43-solution in
disguise.

## 4. The toolkit: what makes a curve easy or hard

**The genus.** If you draw a curve allowing complex numbers, you get a surface, and the genus counts its holes:

- a straight line or circle has genus 0 (a sphere);
- y² = (cubic) has genus 1 (a doughnut);
- y² = (degree 6), like our six curves, has genus 2 (a pretzel with two holes).

Genus 0 curves can have infinitely many fraction points, given by a formula. Genus 2 curves are guaranteed to have only
finitely many (a famous theorem of Faltings), but again the theorem doesn't tell you what they are.

**Adding points.** On a genus-1 curve you can "add" two points: draw the line through them, see where it hits the
curve a third time, and reflect. This makes the points into a *group*: they combine like numbers do. Genus-2 curves
can't do this directly, but each comes with a bigger companion object, its *Jacobian*, where adding works.

**The rank.** The fraction points of the Jacobian can all be built from a few "generator" points by adding and
subtracting, plus a few special points of finite order. The number of generators needed is the *rank*.

**The rule of thumb.** There is a powerful method, Chabauty's method, that finds all fraction points on a genus-2
curve when the rank is smaller than the genus. Rank 0 or 1: usually fine. **Rank 2 = genus 2: the method breaks.**
We'll call that "the wall".

## 5. Steps B and D: the four easy curves, and measuring the rank

**Three curves with no points at all.** For A⁻, B⁺ and C⁻ we prove there are no fraction points whatsoever. The idea
is a much more powerful cousin of "a square can't end in 7". A point on the curve would produce a number in yet another
number system whose "size" has to be of a particular kind. We list every kind that can actually occur, and the one
needed isn't on the list.

**A⁺ has rank 1.** Rank 1 is below the wall, so Chabauty's method works. It's worth knowing how it works, because the
hard part reuses the idea.

### p-adic numbers

Pick a prime p. Two numbers are "p-adically close" if their difference is divisible by a high power of p. For example,
with p = 5, the numbers 1 and 626 are very close, because 626 − 1 = 625 = 5⁴. In this world you can write numbers in
base p with digits going on forever to the *left*.

It sounds strange, but it's a real number system: you can add, multiply and divide, and you can even do something like
calculus.

Chabauty's method builds a function in this p-adic world that is zero at every fraction point of the curve. Then it
finds all the zeros. There are only finitely many, and each zero is either one of the known points or an "impostor" to
be ruled out some other way.

Choosing p mattered here. At p = 43 the method was flooded with impostors: the curve has a hidden symmetry involving
√−2, and at p = 43 that symmetry makes points involving √−2 look rational. At p = 5 the trouble vanishes. The answer is
exactly the four known points.

**The rank of the hard pair.** For B⁻ and C⁺ we show the rank is exactly 2. Finding two independent points shows it's
at least 2. Showing it's at most 2 takes a computation called 2-descent, which we programmed ourselves and tested on
24 curves whose answers are known. The testing caught three real bugs before we trusted it.

## 6. The wall

B⁻ and C⁺ have rank 2 = genus 2. Chabauty's method gives nothing.

There is a newer method, *quadratic Chabauty* (developed since about 2015), that sometimes gets past the wall. It measures points by
a p-adic "height" that behaves like a squared length, which is where "quadratic" comes from. But it needs the curve to
have an extra kind of symmetry, which for this purpose mathematicians call an extra *Néron–Severi class*.

We checked: over the ordinary fractions our two curves have no such extra symmetry. They don't even have one if you
allow √−2, which was the route Villines had suggested trying. Stuck.

## 7. The new trick

### Symmetry hiding in a bigger field

Allowing complex numbers, B⁻ and C⁺ are among the most symmetric curves of their kind. Each is a disguised copy of the
famous *Bolza curve*, with 48 symmetries. Over the ordinary fractions, though, only one boring symmetry survives:
flipping the sign of y.

So we asked: what number system do you need before the other symmetries appear? The answer is a specific number system
L built from ∛2 and two square roots, with 12 "dimensions" (every number in it has 12 coordinates). In L, the curve has
a symmetry that splits it into two genus-1 curves, E₁ and E₂. Quadratic Chabauty for curves that split like this is
well understood. The catch: it works for points with coordinates in L, and we only care about ordinary fractions. How
can a symmetry that doesn't exist over the fractions tell us anything about fraction points?

### The −1

We computed how the 48 symmetries get shuffled when you move between the different versions of L (this shuffling is
called *Galois symmetry*). One fact jumped out: complex conjugation, the operation that turns i into −i, flips the
sign of exactly one of the curve's hidden symmetry classes and leaves the others alone.

That single −1 is the key. The quadratic Chabauty function over L is built from twelve pieces, one for each way of
fitting L inside the p-adic numbers, mixed together with a set of weights. For an ordinary fraction point, Galois
symmetry shuffles those twelve pieces, and almost every choice of weights cancels out to the useless equation 0 = 0.
Only weights that shuffle *the same way as the flipped class* survive.

When we searched for such weights, there was exactly one choice, up to scaling. So there is exactly one equation that
every fraction point must satisfy, and we could write it down.

Two lucky breaks made it computable:

- **The usual hard part vanished.** Normally the trickiest part of quadratic Chabauty is handling a few "bad" primes.
  Here our weights happen to be zero at exactly those primes, so most of that work disappears.
- **What was left was small.** One small correction, from the prime 397, remained, and we computed it by hand.

Only afterwards did we find that a 2017 theorem of Balakrishnan and Dogra predicts that something like this *should*
work. Roughly, it does whenever

  rank < (genus − 1) + (ordinary symmetry classes) + (classes flipped by complex conjugation),

which here is 2 < 1 + 1 + 1. Their theorem says a solution exists; our contribution is building it explicitly from a
symmetry that only exists over a bigger field. As far as we know, that hadn't been done before.

## 8. Running the machine

With p = 499, the curve breaks into 528 small p-adic regions ("residue disks"), one for each possible remainder of x
modulo 499, with a little bookkeeping. On each region, our function becomes a power series: an infinite polynomial. A
classical theorem (Strassmann's) lets you count its zeros just by looking at the sizes of its coefficients.

Result: 524 zeros on B⁻ and 504 on C⁺. Only four of each are real fraction points. The rest are impostors: p-adic
points that satisfy our equation but aren't fractions.

**The sieve.** To kill the impostors we use a *Mordell–Weil sieve*. A genuine fraction point must also make sense
modulo other primes q: it has a remainder, and that remainder has to be consistent with where the point sits relative
to the two generators. Each impostor makes a prediction about what it should look like modulo q. We check whether any
actual point modulo q matches. If none does, the impostor is dead.

The primes q = 997 and q = 12973 do the job. On B⁻, 997 alone kills 518 of the 524 candidates, and 12973 kills the
last two impostors. What survives is exactly the four known points, on each curve.

Put everything together and the funnel closes: the only primitive solutions are the ones in the table at the top.

## 9. Checking our own work

A proof that depends on large computer calculations is only as good as the calculations. So we checked them in several
independent ways.

- **A second prime.** We redid the whole quadratic Chabauty calculation with p = 1459 instead of 499. The numbers are
  bigger (1546 and 1426 candidates, sieved at q = 2917 and 26261), but the outcome was the same: only the known points
  survive.
- **A near miss, written down.** In that rerun, one region on C⁺ first produced two "candidates" whose key numbers had
  no correct digits at all. Recomputing that region more carefully gave ordinary numbers, and the sieve removed them.
  The lesson (check precision everywhere, not just where you expect trouble) is now part of the written proof.
- **An outside comparison.** Villines' independent computations, done with different software (Magma), agree with ours
  wherever they overlap.
- **A proof checker.** Parts of the proof are now checked by Lean, a program that verifies mathematical proofs line by
  line and refuses to accept any step that doesn't follow. More on this below.

## 10. A computer that checks the proof

Ordinary software can have bugs; our 2-descent code had three. A *proof assistant* like Lean is different. You write the
proof in a precise language, and a small, carefully built core (the "kernel") checks that every single step follows
from the ones before. If it accepts the proof, you don't have to trust the person who wrote it, only that small core.

Here is what Lean has now checked:

- **The funnel's first half.** Everything from "z + yθ is a unit times a fourth power" down to the six curves, and the
  last step from the curves' points back to the solutions.
- **The sieve.** This works like a puzzle with a printed answer key. The original program found the answers (which
  impostors die at which prime) the slow way. We had it print out evidence, a *certificate*, that is quick to check.
  Lean's kernel then checks every piece of that evidence itself: about half a minute for p = 499, and about a minute for
  p = 1459.
- **The checker itself.** We also proved, in Lean, that the certificate checker is correct: that its arithmetic really
  is the arithmetic of these curves, as defined in Lean's library of mathematics (Mathlib). So "the program says the
  impostors are dead" becomes "it is a theorem that the impostors are dead".
- **Spotting a loophole.** Writing that proof caught a real loophole in the first version of the checker: a cleverly
  faked certificate could have listed the same point twice in disguise. The checker now rejects that, and there's a
  test proving it does.

The main Lean theorem, `fermat433_qc`, says: *if* the quadratic Chabauty step produced the right list of candidates,
and the steps not yet formalized hold (the factoring step and the four easy curves), *then* the solutions are exactly
the ones in the table. The
quadratic Chabauty step itself, the new idea, is not checked by Lean yet. Building the mathematics needed for that is a
much bigger project.

## 11. What's proved, and what's next

**Proved, by exact computation or by argument:**

- the reduction to six curves;
- that three of the curves have no points;
- the points on A⁺;
- the ranks of the hard pair;
- the new equation, its zeros, and the sieve.

**Assumed from the published literature:** the general theory behind p-adic heights and quadratic Chabauty, written
by experts. Our calculations rely on it; they don't re-prove it.

**What's next:** the proof hasn't been checked by an independent expert yet. That's what referees are for, and it's the
next step before anyone should call this settled. The file REFEREE_NOTES.md lists exactly what an expert should look at
first.

**The one idea to remember.** The wall was "no extra symmetry". The way through was to look for symmetry in a bigger
number system. There, by working out exactly how that symmetry gets shuffled, we found the one combination that still
says something about ordinary fractions.

---

*This work was done by Marcello Federico in collaboration with Claude, an AI system made by Anthropic. Every claim is
backed by a script and a log in this repository, so anyone can check it.*
