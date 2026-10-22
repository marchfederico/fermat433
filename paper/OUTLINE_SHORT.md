# Outline: a short version of the paper that cites Villines

*Draft, October 2026. This is a plan for a shorter companion to `fermat433.tex`, not a replacement. The
current paper re-proves everything on PARI/GP. This version would take Parts A, B and D from Villines
[Vi] and keep only what is new: the quadratic Chabauty argument for the hard pair.*

**Target length:** about 8–10 pages, down from 16. Sections 2, 3 and 7 of the current paper (descent,
the four accessible curves, rank bounds) take about 385 of the ~1100 body lines; they would shrink to
about a page of statements with citations.

**The trade-off to decide first.** [Vi] is a Zenodo preprint with Magma code. It has not been
refereed. Citing it for Parts A, B and D moves the trust for those parts onto it. Two mitigations,
both already in place:

- the independent PARI re-proofs in this repository (PROOF.md, Parts A, B, D), cited as supplementary
  material rather than reproduced;
- the Lean formalization (`lean/`), which machine-checks the reduction (Lemmas A.2–A.3 and the
  recovery of the solutions) given Lemma A.1 and the rational points of the six curves.

A referee may still ask for the full arguments. The current paper is the fallback.

---

## Title and abstract

*Title:* "Quadratic Chabauty through a hidden involution, and the equation x⁴ + 2y³ + z³ = 0".
Lead with the method, since that is the new contribution; the equation is the application.

*Abstract (sketch):* Villines reduced the generalised Fermat equation x⁴ + 2y³ + z³ = 0 to six genus-2
curves and determined the rational points on four of them. The remaining two have Jacobians of rank
2 = genus and Néron–Severi rank 1 over ℚ. We show that the extra Néron–Severi class comes from an
involution defined over a field of degree 12. We then apply the bielliptic quadratic Chabauty of
Balakrishnan–Besser–Bianchi–Müller over that field. This finishes the determination of the primitive
solutions: (±1, 0, −1), (±1, −1, 1) and (±43, −203, 237). State the human–AI collaboration here, as the
current abstract does.

## §1 Introduction (≈ 2 pages; mostly current §1, trimmed)

- **1.1 The result.** Theorem 1.1 unchanged.
- **1.2 What was known.** One paragraph: Ratcliffe–Grechuk list the equation as the smallest
  uninvestigated case (H = 40). State what [Vi] proves, as Theorem 1.2 (see §2 below).
- **1.3 The obstruction and the idea.** Keep the current §1.2 essentially verbatim: the
  Balakrishnan–Dogra count, ρ(J/ℚ) = ρ(J/ℚ(√−2)) = 1, the Bolza twist, the degree-12 field L, the
  selection rule, the identity for ρ(z).
- **1.4 What is new.** Items (1)–(5) of the current list, unchanged.
- **1.5 What the proof rests on.** Current list (i)–(v), plus a new item: the results of [Vi] in
  Theorem 1.2.
- **1.6 Provenance.** Current §1.5. Add: the reduction is machine-checked in Lean.

## §2 The reduction, after Villines (≈ 1 page; replaces current §§2, 3, 7)

**Theorem 2.1 [Vi].** Statements only, each with its pointer into [Vi]:

1. *(Reduction.)* Every primitive solution gives a rational point on one of
   A±: y² = ±(x⁶ − 40x³ − 32), B±: y² = ±C₃(x), C±: y² = ±2C₃(x), where
   C₃(x) = 17x⁶ − 72x⁵ + 90x⁴ + 40x³ − 180x² + 144x − 40. Write out the map back to (x, y, z).
2. *(Empty curves.)* A⁻, B⁺ and C⁻ have no rational points (empty fake 2-Selmer sets, Bruin–Stoll).
3. *(A⁺.)* A⁺(ℚ) = {∞±, (−1, ±3)}: the rank is 1, by Chabauty at p = 5. Note that [Vi]'s model
   differs by x ↦ −x.
4. *(Ranks.)* For X = B⁻ and C⁺, rk J(ℚ) = 2, with explicit generators, and J(ℚ)_tors = 0. Before
   relying on this, check that [Vi] proves the *upper* bound by a 2-descent and not just an analytic
   rank. If it doesn't, keep the current §7 (`prop:rank`) here in short form.

**Remark 2.2 (independent confirmation).** Items 1–4 were re-proved on PARI/GP: descent and twist set,
fake Selmer sets, Chabauty at the inert prime 5 with a sieve, and 2-descent validated on 24 database
curves. These proofs are in the repository (PROOF.md, Parts A, B, D) and agree with [Vi] throughout.
The passage from Lemma A.1 and the six curves back to the solutions is formalized in Lean 4 / Mathlib
(`lean/`). One paragraph, no proofs.

**What is cut:** Lemmas A.1–A.3 with proofs, Propositions B.1 and B.2 (including the p = 5
computation and its sieve), Propositions D.1–D.2, and the 24-curve validation.

## §3 The hard pair: automorphisms and Néron–Severi (current §4, unchanged)

Proposition 3.1 (Aut ≅ GL₂(𝔽₃); involutions over L; bielliptic model; E₁, E₂ with j = 8000).
Proposition 3.2 (Galois action on NS; ρ(J/ℚ) = ρ(J/F) = 1; one anti-invariant class).

## §4 The quadratic Chabauty identity (current §5, unchanged)

The imported theorems (Balakrishnan–Dogra, BBBM). The character (Proposition 4.3). The identity
(Theorem 4.4) and Lemma 4.5 (the prime 397). Computing the heights.

## §5 Zeros and the Mordell–Weil sieve (current §6, unchanged)

Proposition 5.1 (zeros), Proposition 5.2 (the sieve), the second prime p = 1459, and Corollary 5.3:
B⁻(ℚ) and C⁺(ℚ) are the four known points each. The sieve uses the generators and torsion from
Theorem 2.1(4); say so explicitly.

## §6 Proof of the Theorem (≈ ½ page)

Theorem 2.1(1) reduces to the six curves. Items 2–3 handle four of them, and Corollary 5.3 with item
4 handles the hard pair. Transport the points back: (1, ±1) gives (±1, −1, 1); (6/5, ±172/125) gives
(±43, −203, 237); (−1, ±15), (2, ±12) and (−1, ±3) give triples divisible by 3. Point to `lean/` for
a machine-checked version of this step.

## §7 Code and data (current §9, shortened)

Keep the table only for §§3–5 (Part C scripts and logs). Add one line each for `PROOF.md` (the
independent Parts A, B, D) and `lean/`.

## References

Current list, unchanged. [Vi] becomes a load-bearing citation: give the Zenodo DOI
`10.5281/zenodo.20672504` and the GitHub repository, and ideally the version or commit used.

---

## Before writing

1. **Confirm the scope of [Vi].** Check the four claims in Theorem 2.1 against the preprint itself,
   especially (4): RESULTS.md records that the rank upper bound was imported from Villines' Magma
   2-descent before the in-house one replaced it. Also check (1): whether [Vi] proves the twist set or
   only lists the six curves.
2. **Ask Villines.** A short note to say that the shorter version leans on his results, and to ask
   whether a refereed version of [Vi] is planned. If one appears, cite that instead.
3. **Decide where it goes.** Options: a separate `paper/fermat433-short.tex` sharing macros with the
   current paper; or the current paper reorganised, with Parts A, B and D moved to an appendix titled
   "Independent proofs of the results of [Vi]". The appendix route keeps one document and one
   numbering, and gives a referee both versions.
