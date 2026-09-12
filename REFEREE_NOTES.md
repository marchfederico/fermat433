# Notes for an informal referee of Part C (draft, not yet sent to anyone)

*Companion to PROOF.md, Part C. Purpose: state exactly what the new step claims, which external results it rests on
and with what hypotheses, what is proved in the record versus verified numerically, and where an expert's attention
would be most valuable. Everything else in the proof (the descent, the six curves, the 2-descents, the rank-1 Chabauty
on A⁺) is standard machinery, re-implemented and cross-checked against Villines' Magma computations.*

## 1. The claim

X = B⁻: y² = −C₃(x) (and its −2-twist C⁺), genus 2, rank J(Q) = 2, with J absolutely simple over Q but bielliptic
over the degree-12 field L = Q(∛2, √(∛2 − 1), √(1 + bc)) through a hidden involution τ. Claim: for a prime p that
splits completely in L (p = 499 in the record, repeated at p = 1459), the function

  ρ(z) = Σᵢ cᵢ[λᵢ(φ₁z) − λᵢ(φ₂z)] − 2 Σᵢ cᵢ log_p σᵢ(X(z)) − a(z)ᵀ G a(z)      (i over the 12 places of L above p)

is a locally analytic function on X(Q_p) taking the single value −Ω₃₉₇ on X(Q). Its zero set is finite and is
computed disk by disk; a Mordell–Weil sieve then leaves exactly the four known rational points on each curve.

The idea in one sentence: BBBM's bielliptic quadratic Chabauty function on X(L) uses an idele class character χ of
L; the Q-points of X see only the Galois-isotypic component of χ that matches the Néron–Severi class τ_* of the
involution, and there is exactly one such character (Prop. C.3), so one gets a genuine identity for X(Q) although
ρ(J/Q) = 1 and rank = genus. The count 2 < g − 1 + ρ(J) + rk NS(J_Q̄)^{c=−1} = 1 + 1 + 1 of Balakrishnan–Dogra is the
reason this is not a coincidence.

## 2. What is imported, with the hypotheses actually used

1. **p-adic heights on elliptic curves over a number field for a non-cyclotomic character.** For E/L and a continuous
   idele class character χ: A_L^×/L^× → Q_p with χ_𝔭 = c_𝔭·log_p at 𝔭 | p, the height h^χ: E(L) → Q_p is a quadratic
   form, decomposes as a sum of local heights, and the local height at a place w ∤ p of good reduction is
   χ_w(π_w)·max(0, −v_w(x(Q))) on a model minimal at w (with the normalisation fixed by PARI's ellpadicheight
   convention, see §4). At 𝔭 | p with good ordinary reduction the local height is the canonical one, computed from
   the Mazur–Tate sigma function of E ⊗_{σ} Q_p: λ(Q) = −(2/m²)(log σ(mQ) − log ψ_m(Q)), m = #E(F_p).
   *Used in:* Prop. C.4. *Reference:* Mazur–Tate; BBBM §2–3 (explicit quadratic Chabauty over number fields); Bianchi's
   sigma-function description of the local height at p.
   *Referee check:* the factor conventions (the 2 in "−2 log X", the 1/2 or 1 in the away-from-p term, the sign of
   the height) — all are pinned numerically by the vanishing ρ(Pₖ) + Ω₃₉₇ = O(499¹⁹) at the two known points and by
   the failure of the opposite sign, but the derivation in C.4 should match the theory without appeal to numerics.
2. **The vanishing of the local heights at the bad places of E₁, E₂.** The minimal discriminants are supported above
   2 and 3, where χ_Z vanishes on the uniformisers (Prop. C.3). The local height at a bad place w ∤ p is a rational
   multiple of χ_w(π_w) (it is the correction-term times the logarithm of the uniformiser), hence 0. No reduction-type
   analysis is needed. *Referee check:* that the local height at w ∤ p is indeed χ_w(π_w)·(rational number) for every
   reduction type.
3. **Finiteness of X(Q_p)₂ (Balakrishnan–Dogra, QC II, IMRN 2021).** Only motivational: the finiteness of the zero
   set is established computationally (Strassman index 2 on every disk). The proof does not depend on the exact
   statement of BD's proposition, but the write-up quotes it; the quotation should be checked.
4. **Coleman integration on residue disks.** The logarithms log_p σᵢ(X(z)) and the elliptic logarithms Log(φₖ z) are
   expanded on each residue disk by termwise integration (tiny integrals). Standard.

## 3. What is proved in the record

- Prop. C.1–C.2 (automorphisms, field of definition of τ, Galois structure of NS): exact computations, checked
  independently (invol*.gp, nschar2.gp; the Frobenius-trace argument for NS(J_Q̄) ⊗ Q ≅ 1 ⊕ (sgn_F ⊗ sgn ⊗ std)).
- Prop. C.3 (uniqueness of the character): linear algebra over Q_p with exact dimension checks (9, 3, 6, 2, 1).
- Prop. C.4 (the identity): derived from items 1–2 of §2 plus the case analysis at the two primes above 397 where
  the natural quotient models are non-minimal (the Lemma; a referee can verify the table v(X) ↦ m_w(φ₁) − m_w(φ₂)
  directly from the scalings v(u₁) = −2, v(u₂) = −1).
- Prop. C.5 (zeros): the analytic continuation on the 24 special disks (2cᵢ[log(s/X) + v(s)] with the formal
  parameter s, as in Bianchi–Padurariu Remark 2.5) and the Strassman bounds; precision justified by the observed
  linear growth of coefficient valuations, confirmed at 20 digits.
- Prop. C.6 (sieve): index-free because all logarithms lie in pZ_p and the log matrix of the generators has
  determinant of valuation 2 (so [J(Q) : ⟨D₁, D₂⟩ + torsion] is a p-unit); 2-torsion translates vanish mod p.

## 4. Consistency checks performed

- Parallelogram law for the χ_Z-height on both quotients to O(499¹⁹), and h(2Q) = 4h(Q).
- Calibration log σ(kQ₀) − k² log σ(Q₀) = log ψ_k(Q₀), k = 2, 3, 4, to O(499¹⁹) (fixes PARI's division-polynomial
  parity convention and the a₁ = a₃ = 0 requirement of the sigma identities).
- ρ(P₁) + Ω₃₉₇ = ρ(P₂) + Ω₃₉₇ = O(499¹⁹); the +2 log X sign fails.
- On every disk the Z_p-roots recomputed at 20 digits and O(T²⁰) agree with the 14-digit run to 8 digits.
- Independent prime: the whole pipeline was rerun at p = 1459 (the next prime with the needed splitting and no
  Weierstrass disk): same structural facts (unique character, vanishing above 2 and 3, parallelogram law), identity at
  the known points to O(1459¹⁹), 1464 disks per curve, 1546 resp. 1426 zeros, sieve primes above 2917, 26261, 96293,
  and again exactly the four known points on each curve. One disk on C⁺ needed 22 working digits for its coefficient
  vectors (14 digits left them with no significant digits); this is a point a referee may want to see handled
  systematically (a per-disk precision check on a(z), not only on ρ).
- The Néron–Severi structure predicted by the sign rule agrees with Balakrishnan–Dogra's rk NS(J_Q̄)^{c=−1} term.

## 5. Questions I would put to an expert

1. Is the identity of Prop. C.4 a direct instance of BBBM Theorem 1.5 (character χ_Z, points of X(L) restricted to
   X(Q)), with T^χ collapsing to the single constant −Ω₃₉₇ because of Prop. C.3 and the 397-analysis? Or does the
   restriction to Q-points need an argument beyond BBBM (e.g. that a(z) ∈ J(Q) ⊗ Q rather than J(L) ⊗ Q is used in
   the quadratic term)? [Our derivation uses J(Q) only: φ₁(z) = a₁Q₁ + a₂Q₂ + torsion in E₁(L) for z ∈ X(Q).]
2. Is the normalisation of the away-from-p local heights (χ_w(π_w)·max(0, −v_w(x)) with PARI's sign convention)
   the one compatible with the sigma-function local height at p as computed? The numerics say yes; a reference for
   the convention pairing would be welcome.
3. Does the vanishing of χ_Z at the uniformisers above 2 and 3 (a property of this field and this isotypic
   component) have a structural explanation? It is what makes the identity independent of the reduction types at 2, 3.
4. Any concern about using integer models congruent to E ⊗_σ Q_p modulo p³⁰ (so that ellpadics2 applies) for the
   sigma constant? We regard this as harmless since all quantities are determined mod p^N.
5. Is the "sign rule" (only characters in the isotypic component of the Néron–Severi class survive on Q-points) a
   known formulation, and is the method — a QC identity for Q-points built from a class defined only over an
   extension — already in the literature in this form (Dogra's *Unlikely intersections* treats X(L) for [L:Q] > 1)?

## 6. Reproducibility

All scripts and logs are in this directory (step1_character.gp, step2a/b.gp, step3_*.gp, step4_*.gp, twist/,
logs/); PARI/GP 2.17.4, no other dependencies. Each proposition points to the script and log
that establish it.
