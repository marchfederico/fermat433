# The minus sign that cracked x⁴ + 2y³ + z³ = 0

I've always loved puzzles and knowing how things work, and AI has made it easier to dig into new things.

Four days in September. Started with an AI paper I wanted to understand. Ended with a proof of a math problem
nobody had solved. I didn't plan that. I just wanted to see if I could implement some of what was in the paper.

## Trying it out

The paper was Pedro Domingos's ["Tensor Logic: The Language of AI"](https://arxiv.org/abs/2510.12269). The claim is that logic and neural
networks are the same math underneath, and that you can reason inside an AI without it making things up.

I've read a lot of papers like that and mostly had to take them on faith. Trying one used to mean weeks of setup
before you learned anything. This time I described the experiment I wanted and it was running in an hour.

That's the part I'd underline. It's not that the AI knows things I don't. It's that the distance between "I wonder"
and "here's the answer" went from weeks to an afternoon. Curiosity survives an afternoon.

The results were mostly negative. Not because the paper was wrong, but because we were working out how best to
represent the knowledge, and most of what you try doesn't work. Trial and error is the process.

## Then it learned arithmetic

We gave it 25 examples of adding small numbers and 16 of multiplying them, written as tally marks. Nothing else. It
worked out the rules of arithmetic. Not a pattern that usually works. The actual rules, and only the true ones.

Then we gave it multiplication examples and a blank symbol to fill in. It worked out that it needed addition first,
and invented it.

That's when I stopped reviewing the paper and started wondering what else was sitting there. Could this find
something new, or would it only ever hand back things people already knew?

## The bug

Chasing that took me to equations. Find every whole number solution, prove there are no others. We built a pipeline
that produced proofs about thousands of curves. It ran clean. Every check passed.

It was wrong. One step was assuming two things it never verified, and a wrong answer looked exactly like a right one
from the outside. No batch test could catch it. The only way to find it was to go through each step and ask what it
was taking for granted. We found it, fixed it, and threw out about half of a batch of earlier results.

Same lesson as every technical project I've worked on. The danger isn't the part you know is shaky. It's the part
that looks finished.

After that the rule was simple. If we can prove it ourselves, we don't borrow it. Nothing gets believed on one
source. That's why I trust the rest of this.

## The equation

There's a [list of equations like this](https://arxiv.org/abs/2412.11933), ordered by size, with the unsolved ones marked. The
smallest one nobody had done was

  x⁴ + 2y³ + z³ = 0

Three solutions are known. Two are obvious. The third is 43, −203, 237, which is the whole problem in one line. You
can't search your way to certainty. A computer can check billions, find nothing, and the answer is still out past
where you looked.

A day of standard work turned it into a question about six curves. Four we handled. Two hit a wall. There's a
classical method that finds every solution, and it only works when a number attached to your curve is small enough.
Ours was one too big. The method doesn't struggle. It says nothing.

Then I found that [Greg Villines](https://github.com/gvillines-hub/h40-x4-2y3-z3) had done the same thing in June with professional
software, reached the same six curves, and stopped at the same wall.

## One minus sign

Our two curves look plain from where we were standing. From a bigger number system they have 48 hidden symmetries. I
asked whether we could use one, even though it doesn't live where the problem does.

The worry is that a symmetry borrowed from somewhere else washes out when you ask about ordinary whole numbers. So
we counted how it washes out. One symmetry flips where all the others stay put. One minus sign in a table.

That was the whole thing. Build the machinery with a matching flip and it doesn't cancel. And there was exactly one
way to build it. Not a family to search through. One.

It gave the same answer at both known solutions, matching to nineteen digits, and the version with the sign the
other way round failed, which is how you know you understood it instead of got lucky. Then a lot of grinding, and
four solutions left standing at the end. The four we already had.

## Checking it

A proof leaning on someone else's software isn't really yours, so the next day went to replacing the borrowed parts.
We tested our version against 24 curves with published answers. Half came out wrong by one.

I'd misread a column and was comparing against the wrong number entirely. The mistake made the test better. The two
numbers I was accidentally comparing had to line up in a way that made "wrong by one" impossible, so chasing it
turned up three real bugs. After the fixes all 24 matched. Then we ran the whole thing again from a different
starting point, to be sure the answer wasn't an accident of one choice we'd made. Same four solutions.

I also kept asking for it explained like I'm twelve. Not as a joke. If I can't say a step in plain words I don't
know whether I believe it, and "the computer said so" isn't something I'll put my name on.

## What's next

It isn't done. Everything is written down, it all runs on free software anyone can install, and where it overlaps
with Villines' work it agrees. But nobody outside the room has read it. So it's a probable solution until an expert
goes through the new part and somebody redoes the delicate bits with different tools. I'd rather say that now than
get corrected later. The [code and the write-up](https://github.com/marchfederico/fermat433) are public, mistakes included. If
this is your corner of math, take it apart.

One last thing, since I started with the paper. Did tensor logic solve this? No. Not one idea from it is in the
proof. What carried over was the habit it put me in: guess numerically, check exactly, believe nothing on a single
source. I went in to test somebody else's claims and came out with a result I wasn't looking for.

Now back to the original paper.
