# x⁴ + 2y³ + z³ = 0

A complete, computer-assisted proof that the only primitive integer solutions of

  x⁴ + 2y³ + z³ = 0

are (x, y, z) = (±1, 0, −1), (±1, −1, 1) and (±43, −203, 237). This was the smallest open generalized Fermat
equation (H = 40) in the survey of Ratcliffe and Grechuk (arXiv 2412.11933); G. Villines reduced it to six genus-2
curves and solved four of them in June 2026 (github.com/gvillines-hub/h40-x4-2y3-z3). The remaining two curves have
Jacobians of rank 2 = genus; they are handled here by a quadratic Chabauty argument built from an involution that is
defined only over a field of degree 12 (Part C of the proof), which is the new contribution.

**Status (September 2026): proof complete in this record, not yet refereed or published.** Everything is proved here
except the cited theorems it rests on (Balakrishnan–Dogra finiteness; the bielliptic quadratic Chabauty function of
Balakrishnan–Besser–Bianchi–Müller; standard Coleman integration and p-adic heights). See REFEREE_NOTES.md for what
an expert should check first.

## The paper

`paper/fermat433.tex` is the proof written up as a 15-page article (amsart), with the built PDF tracked beside it at
`paper/fermat433.pdf` so it can be read without a TeX installation. It covers the same ground as PROOF.md in the
form a referee would expect: the theorem, the rank-2-equals-genus obstruction and the idea in §1; the four parts of
the proof in §§2–8; and in §9 a table mapping every proposition to the script and log that establish it. The
human–AI collaboration is stated up front, in the abstract and in §1.5, not only in the acknowledgements. Every
reference has been checked against the publisher or the arXiv record, Villines' preprint excepted — there is no
public source for that one.

PROOF.md remains the working record and is the place to edit first; the paper is the presentation of it, and the two
are kept in step by hand.

Building needs [tectonic](https://tectonic-typesetting.github.io) and nothing else:

    cd paper
    make            # builds fermat433.pdf; does nothing if the source is unchanged
    make check      # builds twice and confirms the output is byte-for-byte identical

The Makefile pins SOURCE_DATE_EPOCH, so the PDF turns up in a `git diff` exactly when the paper has changed rather
than on every rebuild; the reasoning is in the comments at the top of paper/Makefile.

## Documents

| file | what it is |
|---|---|
| paper/fermat433.tex | the proof as a self-contained article, with the PDF beside it — see [The paper](#the-paper) |
| PROOF.md | the proof, in four parts: (A) descent over Q(∛2) to six genus-2 curves, (B) the four easy curves, (C) the hard pair by quadratic Chabauty with the hidden involution, (D) the rank bounds by 2-descent |
| NOTE.md | narrative companion: derivations, conventions, literature placement |
| RESULTS.md | chronological lab record, including the bugs found and how |
| REFEREE_NOTES.md | for an informal referee of Part C: claims, imported results with hypotheses, checks, open questions |
| EXPLAINER.md | the proof and the discovery of the trick, for a general reader |

## Scripts, by part of the proof

Everything runs on PARI/GP 2.17.4 (no Magma, no Sage); the Python scripts need only sympy.

- **Part A (reduction, twist set):** descent_explore.py, descent_explore_forms.py, diagonal.py, etale.py, twistset.py.
- **Part B (easy curves):** sel2/fakeselmerset.gp (fake 2-Selmer set), sel2/certify.gp (class groups, norm classes);
  aplus/ (A⁺: bielliptic model, Chabauty at p = 43 and at the inert prime 5, sieves, exact torsion checks).
- **Part C (hard pair, quadratic Chabauty):** invol.gp, invol4.gp, invol8.gp (the 48 automorphisms and the involution
  field), nschar2.gp (Galois structure of the Néron–Severi group), step1_character.gp (the unique p-adic character),
  step2a.gp, step2b.gp (bielliptic model over L, heights, bilinear form), step3_*.gp (residue disks, zeros),
  step4_scan.gp, step4_sieve.gp (Mordell–Weil sieve), twist/ (the same for C⁺), second_prime/ (the rerun at p = 1459).
- **Part D (rank bounds):** sel2/pipeline.gp (Stoll-style fake 2-Selmer group over Q), sel2/run_validation.sh and
  sel2/validation_curve_*.gp (24 database curves used to validate the implementation).
- **logs/** holds the output of every run cited in PROOF.md, organised by part.
- **supporting/** holds the bielliptic quadratic Chabauty modules over Q (qc_sigma.py, qc_local.py, qc_solve.py,
  qc_bielliptic.py) from the companion project, where the sigma-function local heights were first validated.
- **exploration/** holds early searches and abandoned routes (Thue-style searches, the Simon descent over the
  degree-12 field, prime scans) kept for the record; nothing in PROOF.md depends on them.

## Reproducing

Each proposition in PROOF.md names the script and log that establish it. The long runs are the residue-disk
expansions (step3_run.gp in four chunks, ~10 minutes at p = 499, ~40 minutes at p = 1459) and the 2-adic point
searches of sel2/pipeline.gp (up to ~1.5 hours per curve). `second_prime/make_p1459.py <dir>` regenerates the
p = 1459 pipeline from the p = 499 scripts.

## Provenance

This repository was split, with its history, from the `tensor-logic/fermat433` directory of a private research
repository on 2026-09-12. The work was done in a human–AI collaboration (Claude, Anthropic); the mathematics is to be
read critically, see REFEREE_NOTES.md.

## Licence

Copyright © 2026 Marcello Federico. Two licences, split by what the file is:

| what | licence | files |
|---|---|---|
| the writing | CC BY 4.0 (LICENSE-CC-BY-4.0.txt) | the Markdown documents above, and the paper itself — `paper/fermat433.tex` and the PDF built from it |
| the code | GPL v3 or later (LICENSE) | the PARI/GP, Python and shell scripts, `paper/Makefile`, and the logs the scripts produce |

Every script carries the notice in its own header, so a file lifted out of the repository on its own still says what
it is and who wrote it. The four scripts in `exploration/simon/` keep Denis Simon's headers instead, untouched.

The code is free software: you may redistribute it and modify it under the terms of the GNU General Public License
as published by the Free Software Foundation, either version 3 of the License or, at your option, any later
version. It is distributed in the hope that it will be useful, but without any warranty; see LICENSE for the terms.
Anything built on these scripts and distributed must be free software too.

The mathematics may be quoted, translated and built on with attribution: the title of the paper, this repository's
URL, and the note that the work was done in collaboration with Claude (Anthropic).

`exploration/simon/` holds Denis Simon's PARI scripts (ell.gp, ellQ.gp, qfsolve.gp, resultant3.gp), redistributed
unmodified with their copyright headers intact. They are themselves GPL, so they now sit under the same licence as
the rest of the code and need no carve-out; the copyright in them is Denis Simon's, not mine. Nothing in PROOF.md or
the paper loads them — they are kept for the record of an abandoned route.
