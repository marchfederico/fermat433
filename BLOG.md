# How I got here

I've always loved puzzles and knowing how things work, and AI has made it easier to dig into new things.

That sentence is the whole reason this happened. Four days in September 2026, starting with a paper about
artificial intelligence I wanted to understand properly, ending somewhere I had no business ending up: a proof of
a number puzzle nobody had solved. I didn't set out to do that. I set out to find out whether a paper was right.

## Reading with my hands

The paper was Pedro Domingos's "Tensor Logic: The Language of AI". Its big claim is that logic and neural networks
are secretly the same mathematics, and that if you write them in one language you can reason inside an AI's
"embedding space" without the machine making things up.

I've read a lot of papers like that and mostly had to take them on faith. Checking a claim used to mean weeks of
setup before the first honest result, and life is short. This time I described the experiment I wanted and had it
running before I lost interest. That's the part people underestimate. It isn't that the AI knows things I don't.
It's that the gap between "I wonder whether" and "here's the answer" collapsed from weeks to an afternoon, and
curiosity survives an afternoon.

The first results were clean and mostly negative. The paper's headline feature was the weak part; its reliability
came from computing logical consequences exactly, not from the embeddings. I wrote that down, including the
unflattering parts, because a result you only keep when it agrees with you isn't a result.

## The part that surprised me

Then something happened I still think about. We gave the system 25 examples of adding small numbers and 16 of
multiplying them, written as tally marks, nothing else. It worked out the rules of arithmetic. Not approximately,
not "a pattern that usually works". The actual axioms, and only the true ones.

Then we gave it multiplication examples and a blank symbol to fill in, and it worked out that it needed addition
first, and invented it. Give it exponentiation, it invents multiplication.

That was the moment this stopped being a book review. If a machine can rediscover arithmetic from tally marks, what
else is sitting there waiting? Which is really one question: could any of this find something genuinely new, or was
it only ever going to hand me back things humanity already knew?

## The bug that taught me the most

Trying to answer that took me into equations: find every whole-number solution of some polynomial, prove there are
no others. We built a big automated pipeline producing proofs about thousands of curves. It ran clean. Every sanity
check passed.

It was wrong. One step was quietly assuming two things it had never verified, and the failure mode was vicious: a
false result looked exactly like a true one from the outside. No batch check could have caught it, because there was
nothing to compare against. The only way to find it was to stop and ask, of each step, what does this actually
assume? We found it, fixed it, and had to withdraw about half of a batch of earlier claims.

I've had that experience in every technical thing I've ever done and the lesson never changes. The danger is never
the part you know is shaky. It's the part that looks finished. After that, the rule for the whole project was: if we
can prove it ourselves, we don't borrow it, and anything a machine tells us gets checked against something that
doesn't come from the same machine. That rule is why I believe the rest of this.

## The equation

There's a survey that lists equations of this family by size and marks the ones nobody has solved. The smallest
unsolved one was

  x⁴ + 2y³ + z³ = 0.

Three solutions are known. Two are small and obvious. The third is x = 43, y = −203, z = 237, which is the whole
problem in one line: you cannot search your way to confidence. A computer can check billions of possibilities, find
nothing, and the answer is still sitting out there past where you looked.

The classical machinery took us a long way in a day. Follow where the equation forces things and the puzzle turns
into a question about six specific curves. Four we could handle. Two hit a wall, and it's a real wall, not a
"try harder" one: there's a beautiful classical method that finds every solution, and it works only when a certain
number attached to your curve is small enough. Ours was exactly too big. The method doesn't struggle. It says
nothing at all.

Halfway through I found that a mathematician named Greg Villines had walked the same road in June, with
professional software, reached the same six curves and the same two survivors, and stopped at the same wall. He'd
left a note suggesting a way around it. We tested his suggestion and showed it couldn't work. So: same wall, months
later, with a smaller toolkit.

## The way through

What broke it open was a naive question. Our two stubborn curves look plain, but only because of where you're
standing. Seen from a larger number system they have 48 hidden symmetries. I asked whether we could use one, even
though it lives somewhere the problem doesn't.

There's a known method that uses exactly such a symmetry, but it answers a bigger question than mine: it finds
solutions in the larger number system, and I only wanted ordinary whole numbers. Those symmetries get shuffled
around as you move between number systems, and the natural worry is that anything built from them averages away to
nothing when you ask about ordinary solutions.

So we counted. We worked out exactly how the shuffling acts, and the answer had one strange feature: one single
symmetry gets flipped where all the others stay put. One minus sign in a table.

That minus sign was the whole thing. It meant that if you built the machinery with a matching flip, the
contributions wouldn't cancel — they'd survive and say something about ordinary solutions. And when we asked how
many ways there were to build it that way, the answer was exactly one. Not a family to search. One candidate,
forced.

We built it. It gave the same answer at both known solutions, agreeing to nineteen digits, and the variant with the
sign the other way round failed, which is how you know you understood it rather than got lucky. Then the grind:
chop the space into 528 pieces, solve on each, get 524 candidates, sieve away the impostors. Four survivors. The
four we already knew.

Afterwards I found that two mathematicians had proved a general theorem saying a count like ours guarantees this
kind of thing is possible. The possibility was known. What seems to be new is actually doing it, with a symmetry
that only exists somewhere else.

## Making it honest

A proof that leans on someone else's software for its hard parts isn't really yours, so the next day went into
removing every borrowed piece. That meant implementing a twenty-five-year-old algorithm from a paper and testing it
against 24 curves whose answers were published.

Half came out wrong by one.

The embarrassing part: I'd misread a column in the reference data and was comparing against the wrong number
entirely. But the mistake made the test better, not worse, because the numbers I was accidentally comparing had to
match in a way that made "wrong by one" impossible. Chasing that impossibility turned up three real bugs, all
subtle, all of the kind that quietly poisons a result. Fixed, all 24 agreed. Then we ran the whole main computation
again from a different starting point, to be sure the answer wasn't an artifact of a choice we'd made. Same four
solutions.

And I kept asking for the explanation like I was twelve. Repeatedly, not as a joke. If I can't say a step in plain
words, I don't know whether I believe it, and "the computer said so" isn't something I'll sign my name to.

## Where it stands

I say "probable solution" on purpose. Everything is written down, everything runs on free software anyone can
install, and the parts that overlap with Villines' independent work agree with it. What's left is what's always
left: an expert needs to read the new step, someone should redo the delicate parts with different tools, and it
needs review. Until then it's a complete argument nobody outside the room has checked. I'd rather say that clearly
than oversell it and be corrected later.

## What I take from this

The AI didn't solve it. Neither did I, alone. What happened is that one curious person could run a research program
that used to need a small team and a year.

My job in it was judgment, not cleverness. Choose what to aim at. Refuse to borrow what we could prove. Check
things against sources that can't be wrong in the same direction. Ask for it in plain words until it's plain. Say
"probably" when it's probably.

The two best moments weren't moments of brilliance. One was a computation quietly showing us a minus sign we
weren't looking for. The other was refusing to believe a pipeline that looked perfect. That's what puzzles have
always been like. The only thing that changed is how far one person can get before the puzzle wins.
