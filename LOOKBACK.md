# Proving x⁴ + 2y³ + z³ = 0: how I got here

I've always loved puzzles and knowing how things work, and AI has made it easier to dig into new things.

That sentence is the whole reason this happened. Four days in September 2026, starting with a paper about
artificial intelligence that I wanted to understand properly, ending somewhere I had no business ending up: a
proof of a number puzzle that nobody had solved. I did not set out to do that. I set out to find out whether a
paper was right.

## Reading with my hands

The paper was Pedro Domingos's ["Tensor Logic: The Language of AI"](https://arxiv.org/abs/2510.12269). Its big claim is that logic and
neural networks are secretly the same mathematics, and that if you write them in one language you can reason inside an
AI's "embedding space" without the machine making things up.

I've read a lot of papers like that over the years and mostly had to take them on faith. Checking a claim used to
mean weeks of setup before the first honest result, and life is short. This time I described the experiment I
wanted and had it running before I lost interest. That is the part people underestimate. It isn't that the AI knows
things I don't. It's that the gap between "I wonder whether" and "here's the answer" collapsed from weeks to an
afternoon, and curiosity survives an afternoon.

So we tested it. The first results were clean and mostly negative. Not because the paper was wrong, but because we
were working out how best to represent the knowledge, and most of what you try doesn't work. What the numbers said
was that the reliability came from computing the logical consequences exactly rather than from the embeddings. I
wrote that down as it came out. Trial and error is the process, and a result you only keep when it agrees with you
isn't a result.

## The part that surprised me

Then something happened that I still think about. We gave the system 25 examples of adding small numbers and 16 of
multiplying them, written as tally marks, nothing else. It worked out the rules of arithmetic. Not approximately,
not "learned a pattern that usually works". It produced the actual axioms, and only the true ones.

Then we gave it multiplication examples and a blank symbol to fill in, and it discovered that it needed addition
first, and invented it. Give it exponentiation, it invents multiplication.

I sat with that one for a while. It was the moment the project stopped being a book review and started being
something I cared about. If a machine can rediscover arithmetic from tally marks, what else is sitting there
waiting to be rediscovered? Which is really the question: could any of this find something genuinely new, or was
it only ever going to give me back things humanity already knew?

## Failing at that, usefully

The first attempt was a flop, and a good one. There's a giant catalogue of number sequences online, with a few
hundred unsolved guesses recorded in it. We built a machine to settle them. It proved a hundred thousand facts in
eight minutes. It solved zero of the open problems.

Zero is a real answer. The open ones are open because they're hard, not because nobody got around to them, and the
machinery being genuinely good at proving things is not the same as it being good at proving the things that are
left. I kept the machine and changed the target.

Where I went next was equations: find all the whole-number solutions of some polynomial, prove there are no others.
That field has a precise wall in it, a beautiful one. There's a classical method that finds every solution, and it
works only when a certain number attached to your equation is small enough. When that number is too big, the method
says nothing at all. Not "try harder", nothing.

Before we got anywhere near that wall, we hit the episode that taught me the most.

## The bug

We had a big automated pipeline producing proofs about thousands of curves. It was running clean. Every sanity
check passed.

It was wrong. One step was quietly assuming two things it had never verified, and the failure mode was vicious: a
false result looked exactly like a true one from the outside. No batch check could have caught it, because there
was nothing to compare against. The only way to find it was to stop and ask, of each step, what does this actually
assume? We found it, fixed it, and had to withdraw about half of a batch of earlier claims.

I've had that experience in every technical thing I've ever done, and the lesson is always the same. The danger is
never the part you know is shaky. It's the part that looks finished. After that, the rule for the whole project was:
if we can prove it ourselves, we don't borrow it, and anything a machine tells us gets checked against something
that doesn't come from the same machine. That rule is why I believe the rest of this.

## The equation

There's a [survey](https://arxiv.org/abs/2412.11933) that lists equations of this family by size and marks the ones nobody has
solved. The smallest unsolved one was

  x⁴ + 2y³ + z³ = 0.

Three solutions are known. Two are small and obvious. The third is x = 43, y = −203, z = 237, which is the whole
problem in one line: you cannot search your way to confidence. A computer can check billions of possibilities and
find nothing, and the answer can still be sitting out there past where you looked.

The classical machinery took us a long way in a day. Factor the equation inside a number system that includes the
cube root of 2, follow where that forces things, and the original puzzle turns into a question about six specific
curves. Four of them we could handle. Two of them hit the wall: that number was exactly too big, and the method
went silent.

Halfway through this I found that a mathematician named [Greg Villines](https://github.com/gvillines-hub/h40-x4-2y3-z3) had walked the
same road in June, with professional software, and had got to the same six curves and the same two survivors. He'd stopped at the same
wall, and left a note suggesting a way around it. We tested his suggestion and showed it couldn't work. So: same
wall, several months later, with a smaller toolkit.

## The way through

What broke it open was a naive question. Our two stubborn curves look plain, but only because of where you're
standing. Seen from a larger number system they turn out to have 48 hidden symmetries. I asked whether we could
use one of those, even though it lives somewhere the problem doesn't.

There's a known method that uses exactly such a symmetry, but it answers a bigger question than mine: it finds
solutions in the larger number system, and I only wanted the ordinary whole-number ones. Those extra symmetries
come in a group that gets shuffled around when you move between number systems, and the natural worry is that
anything you build from them gets averaged away to nothing when you ask about ordinary solutions.

So we counted. We worked out exactly how the shuffling acts, and the answer had one strange feature: one single
symmetry gets flipped where all the others stay put. One minus sign in a table.

That minus sign was the whole thing. It meant that if you built the method's machinery with a matching flip, the
contributions wouldn't cancel; they'd survive and say something about ordinary solutions. And when we asked how
many ways there were to build it that way, the answer was exactly one. Not a family to search through. One
candidate, forced.

We built it. It gave the same answer at both known solutions, agreeing to nineteen digits, and the variant with the
sign the other way round failed, which is how you know you understood it rather than got lucky. Then a small gift:
the construction happened to vanish in exactly the places where these problems normally get ugly, so the worst part
of the computation simply wasn't there.

Then the grind: chop the space into 528 pieces, solve on each, get 524 candidate solutions, and sieve away the 520
impostors. Four survivors. The four we already knew.

Afterwards I found that two mathematicians had proved a general theorem saying that a count like ours guarantees
this kind of thing is possible. So the possibility was known. What seems to be new is actually doing it: building
the thing with a symmetry that only exists somewhere else.

## Making it honest

A proof that leans on someone else's software for its hard parts isn't really yours, so the next day went into
removing every borrowed piece. That meant implementing a twenty-five-year-old algorithm from a paper, and testing
it against 24 curves whose answers were published.

Half of them came out wrong by one.

The embarrassing part: I had misread a column in the reference data. I was comparing against the wrong number
entirely. But the mistake made the test better, not worse, because the numbers I was accidentally comparing had to
match in a way that made "wrong by one" impossible. Chasing that impossibility turned up three real bugs in our
code, all subtle, all of the kind that would have quietly poisoned the result. Fixed, all 24 agreed.

Then we did the whole main computation over again with a different starting prime, to make sure the answer wasn't
an artifact of a choice we'd made. Same four solutions. One piece of it threw a small scare, which turned out to be
our own numbers being rounded too aggressively in one spot. Fixed that too, and wrote down the lesson.

And I kept asking for the explanation like I was twelve. Repeatedly. Not as a joke. If I can't explain a step in
plain words, I don't know whether I believe it, and "the computer said so" is not a thing I'm willing to sign my
name to. Those explanations are in the repository now, next to the formal ones.

## Where it stands

I say "probable solution" on purpose. [Everything is written down](https://github.com/marchfederico/fermat433), everything runs on
free software anyone can install, and the parts that overlap with Villines' independent work agree with it. What's left is what's always
left: an expert needs to read the new step, someone should redo the delicate parts with different tools, and it
needs to go through review. Until then it's a complete argument that hasn't been checked by anyone outside the room.
I'd rather say that clearly than oversell it and be corrected later.

## What I actually take from this

The AI didn't solve it. Neither did I, alone. What happened is that one curious person with a full-time job could
run a research program that used to need a small team and a year: read the literature, build the tools, run tens of
thousands of computations, catch its own errors, write it all up.

My job in it was judgment, not cleverness. Choose what to aim at. Refuse to borrow what we could prove. Insist on
checking things against sources that couldn't be wrong in the same direction. Ask for it in plain words until it's
plain. Say "probably" when it's probably.

And the two best moments weren't moments of brilliance. One was a computation quietly showing us a minus sign we
weren't looking for. The other was refusing to believe a pipeline that looked perfect. That's what puzzles have
always been like. The only thing that changed is how far a person can now get before the puzzle wins.

Now back to the original paper.
