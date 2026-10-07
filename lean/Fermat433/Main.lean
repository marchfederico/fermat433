/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Fermat433.Reduction

/-!
# The theorem, conditional on `Inputs`

`fermat433` is the theorem of PROOF.md with every step proved in Lean except those collected in
`Inputs` (Lemma A.1, Propositions B.1 and B.2, and the determination of `B⁻(ℚ)` and `C⁺(ℚ)` in
Parts C and D). `solutions_primitive` checks that the six triples really are primitive, so the
statement is not vacuous on its right-hand side.
-/

open ZT Fermat433

theorem solutions_primitive : ∀ s ∈ solutions, Primitive s.1 s.2.1 s.2.2 := by
  intro s hs d hx _ hz
  have h := Int.dvd_coe_gcd hx hz
  simp only [solutions, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact isUnit_of_dvd_one (by rwa [show Int.gcd _ _ = 1 by decide, Nat.cast_one] at h)

theorem solutions_solve : ∀ s ∈ solutions, s.1 ^ 4 + 2 * s.2.1 ^ 3 + s.2.2 ^ 3 = 0 := by
  decide

/-- **Theorem.** Given the results imported in `Inputs`, the primitive integer solutions of
`x⁴ + 2y³ + z³ = 0` are exactly `(±1, 0, −1)`, `(±1, −1, 1)` and `(±43, −203, 237)`. -/
theorem fermat433 (H : Inputs) (x y z : ℤ) (hp : Primitive x y z) :
    x ^ 4 + 2 * y ^ 3 + z ^ 3 = 0 ↔ (x, y, z) ∈ solutions := by
  refine ⟨fun heq => ?_, fun hs => solutions_solve _ hs⟩
  obtain ⟨k, hk, γ, hα⟩ := H.descent x y z heq hp
  have D := descended heq hp hα
  interval_cases k
  · exact case_k0 H hp D
  · exact case_k1 H hp D
  · exact (not_k23 (Or.inl rfl) (odd_r0 heq hp hα) hα).elim
  · exact (not_k23 (Or.inr rfl) (odd_r0 heq hp hα) hα).elim
