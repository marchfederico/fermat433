/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Main
import Fermat433.Sieve.Sound.Main

/-!
# The theorem with the Mordell–Weil sieve proved in Lean

`fermat433` assumes the rational points of `B⁻` and `C⁺` outright (`Inputs.B_minus`,
`Inputs.C_plus`). Here those two hypotheses are replaced by what the quadratic Chabauty computation
and the sieve's setup provide (Propositions 6.1–6.2), and the sieve itself is the Lean theorem
`sieve_B_minus_sound` / `sieve_C_plus_sound`. For a rational point `(X, W)` of the curve:

1. its coefficient vector modulo 499 is one of the quadratic Chabauty candidates;
2. at each sieving prime `q` of `L`, the sieve condition holds for that vector
   (`SieveCompatible`: the reduction of the point satisfies both equations in the 499-parts);
3. if the vector is one of the four surviving ones, the point is one of the known points.

Everything else in Part C, the finite sieve over 𝔽₉₉₇ and 𝔽₁₂₉₇₃, is proved here.
-/

open Fermat433.Sieve

/-- The survivors of the sieves, and the known points they belong to. -/
def survivorsB : List (ℕ × ℕ) := [(1, 0), (498, 0), (0, 1), (0, 498)]
def survivorsC : List (ℕ × ℕ) := [(0, 1), (0, 498), (1, 0), (498, 0)]

/-- The hypotheses of `fermat433`, with `B⁻(ℚ)` and `C⁺(ℚ)` replaced by Propositions 6.1–6.2. -/
structure InputsQC : Prop where
  /-- Lemma A.1, as in `Inputs.descent`. -/
  descent : ∀ x y z : ℤ, x ^ 4 + 2 * y ^ 3 + z ^ 3 = 0 → Primitive x y z →
    ∃ k < 4, ∃ γ : ZT, (⟨z, y, 0⟩ : ZT) = -(ZT.ε ^ k * γ ^ 4)
  /-- Proposition B.1, as in `Inputs.A_minus`. -/
  A_minus : ∀ X W : ℚ, W ^ 2 ≠ -FA X
  /-- Proposition B.1, as in `Inputs.B_plus`. -/
  B_plus : ∀ X W : ℚ, W ^ 2 ≠ C3 X
  /-- Proposition B.1, as in `Inputs.C_minus`. -/
  C_minus : ∀ X W : ℚ, W ^ 2 ≠ -2 * C3 X
  /-- Proposition B.2, as in `Inputs.A_plus`. -/
  A_plus : ∀ X W : ℚ, W ^ 2 = FA X → X = -1
  /-- Propositions 6.1–6.2 for `B⁻ : y² = −C₃(x)` at `p = 499`. -/
  B_minus_qc : ∀ X W : ℚ, W ^ 2 = -C3 X → ∃ a ∈ Bminus.inputs.cands,
    (a ∈ survivorsB → X = 1 ∨ X = -1) ∧ ∀ C ∈ Bminus.certs, SieveCompatible Bminus.inputs C a
  /-- Propositions 6.1–6.2 for `C⁺ : y² = 2C₃(x)` at `p = 499`. -/
  C_plus_qc : ∀ X W : ℚ, W ^ 2 = 2 * C3 X → ∃ a ∈ Cplus.inputs.cands,
    (a ∈ survivorsC → X = 6 / 5 ∨ X = 2) ∧ ∀ C ∈ Cplus.certs, SieveCompatible Cplus.inputs C a

namespace InputsQC

variable (H : InputsQC)
include H

/-- `B⁻(ℚ)`, from quadratic Chabauty and the sieve proved in Lean. -/
theorem B_minus : ∀ X W : ℚ, W ^ 2 = -C3 X → X = 1 ∨ X = -1 := by
  intro X W h
  obtain ⟨a, ha, hsurv, hcomp⟩ := H.B_minus_qc X W h
  by_cases hs : a ∈ survivorsB
  · exact hsurv hs
  · obtain ⟨C, hC, hrem⟩ := sieve_B_minus_sound a ha hs
    exact (hrem.not_compatible (hcomp C hC)).elim

/-- `C⁺(ℚ)`, from quadratic Chabauty and the sieve proved in Lean. -/
theorem C_plus : ∀ X W : ℚ, W ^ 2 = 2 * C3 X → X = 6 / 5 ∨ X = 2 := by
  intro X W h
  obtain ⟨a, ha, hsurv, hcomp⟩ := H.C_plus_qc X W h
  by_cases hs : a ∈ survivorsC
  · exact hsurv hs
  · obtain ⟨C, hC, hrem⟩ := sieve_C_plus_sound a ha hs
    exact (hrem.not_compatible (hcomp C hC)).elim

theorem toInputs : _root_.Inputs :=
  ⟨H.descent, H.A_minus, H.B_plus, H.C_minus, H.A_plus, H.B_minus, H.C_plus⟩

end InputsQC

/-- **Theorem.** Given Lemma A.1, Propositions B.1–B.2 and Propositions 6.1–6.2 (`InputsQC`), the
primitive integer solutions of `x⁴ + 2y³ + z³ = 0` are exactly `(±1, 0, −1)`, `(±1, −1, 1)` and
`(±43, −203, 237)`. The Mordell–Weil sieve of Part C is proved in Lean, by the kernel. -/
theorem fermat433_qc (H : InputsQC) (x y z : ℤ) (hp : Primitive x y z) :
    x ^ 4 + 2 * y ^ 3 + z ^ 3 = 0 ↔ (x, y, z) ∈ solutions :=
  fermat433 H.toInputs x y z hp
