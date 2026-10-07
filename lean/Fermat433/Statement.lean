/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.ZTheta

/-!
# The statement, and the results the Lean proof takes as input

The theorem of PROOF.md: the primitive integer solutions of `x⁴ + 2y³ + z³ = 0` are
`(±1, 0, −1)`, `(±1, −1, 1)` and `(±43, −203, 237)`.

Lean proves this *from* the hypotheses collected in `Inputs` below. They are the parts of the
proof that rest on machinery Mathlib does not have (class groups and unit groups of number fields,
2-descent on Jacobians, Chabauty and quadratic Chabauty). Each field cites the place in PROOF.md
that establishes it. Everything else is proved in `Fermat433.Reduction`: the norm bookkeeping, the
parity and 2-adic conditions of Lemma A.2, the conics and twist set of Lemma A.3, and the recovery
of `(x, y, z)` from the rational points on the six curves (Part E).
-/

open ZT

/-- `gcd(x, y, z) = 1`, stated without reference to `gcd`. -/
def Primitive (x y z : ℤ) : Prop := ∀ d : ℤ, d ∣ x → d ∣ y → d ∣ z → IsUnit d

/-- `C₃(x) = 17x⁶ − 72x⁵ + 90x⁴ + 40x³ − 180x² + 144x − 40`. -/
def C3 (X : ℚ) : ℚ :=
  17 * X ^ 6 - 72 * X ^ 5 + 90 * X ^ 4 + 40 * X ^ 3 - 180 * X ^ 2 + 144 * X - 40

/-- `x⁶ − 40x³ − 32`, the sextic of the curves `A±`. -/
def FA (X : ℚ) : ℚ := X ^ 6 - 40 * X ^ 3 - 32

/-- The results imported from outside Lean. For the six curves only the affine rational points
matter (points at infinity are handled directly), and only their `x`-coordinates are used. -/
structure Inputs : Prop where
  /-- Lemma A.1: `K = ℚ(∛2)` has class number 1 and unit group `⟨−1, ε⟩`, so for a primitive
  solution `z + yθ = −εᵏγ⁴` with `γ ∈ ℤ[θ]` and `0 ≤ k < 4`. -/
  descent : ∀ x y z : ℤ, x ^ 4 + 2 * y ^ 3 + z ^ 3 = 0 → Primitive x y z →
    ∃ k < 4, ∃ γ : ZT, (⟨z, y, 0⟩ : ZT) = -(ε ^ k * γ ^ 4)
  /-- Proposition B.1: `A⁻ : y² = −(x⁶ − 40x³ − 32)` has no rational points. -/
  A_minus : ∀ X W : ℚ, W ^ 2 ≠ -FA X
  /-- Proposition B.1: `B⁺ : y² = C₃(x)` has no rational points. -/
  B_plus : ∀ X W : ℚ, W ^ 2 ≠ C3 X
  /-- Proposition B.1: `C⁻ : y² = −2C₃(x)` has no rational points. -/
  C_minus : ∀ X W : ℚ, W ^ 2 ≠ -2 * C3 X
  /-- Proposition B.2: `A⁺(ℚ) = {∞±, (−1, ±3)}`. -/
  A_plus : ∀ X W : ℚ, W ^ 2 = FA X → X = -1
  /-- Part C (with the rank bound D.1): `B⁻(ℚ) = {(1, ±1), (−1, ±15)}`. -/
  B_minus : ∀ X W : ℚ, W ^ 2 = -C3 X → X = 1 ∨ X = -1
  /-- Part C (with the rank bound D.2): `C⁺(ℚ) = {(6/5, ±172/125), (2, ±12)}`. -/
  C_plus : ∀ X W : ℚ, W ^ 2 = 2 * C3 X → X = 6 / 5 ∨ X = 2

/-- The six primitive solutions. -/
def solutions : List (ℤ × ℤ × ℤ) :=
  [(1, 0, -1), (-1, 0, -1), (1, -1, 1), (-1, -1, 1), (43, -203, 237), (-43, -203, 237)]
