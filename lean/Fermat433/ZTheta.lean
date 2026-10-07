/-
Copyright (C) 2026 Marcello Federico
SPDX-License-Identifier: GPL-3.0-or-later
-/
import Mathlib

/-!
# The ring ℤ[θ], θ = ∛2, in coordinates

An element `⟨a, b, c⟩ : ZT` stands for `a + bθ + cθ²`. We only need the multiplicative structure
(the descent writes `z + yθ = -εᵏγ⁴`) and the norm `N`, so `ZT` is given a `CommMonoid` instance
and a negation, nothing more. This mirrors `mul` and `norm` in `descent_explore.py`.
-/

@[ext]
structure ZT where
  r0 : ℤ
  r1 : ℤ
  r2 : ℤ
  deriving DecidableEq

namespace ZT

instance : Mul ZT :=
  ⟨fun u v => ⟨u.r0 * v.r0 + 2 * (u.r1 * v.r2 + u.r2 * v.r1),
               u.r0 * v.r1 + u.r1 * v.r0 + 2 * u.r2 * v.r2,
               u.r0 * v.r2 + u.r1 * v.r1 + u.r2 * v.r0⟩⟩

instance : One ZT := ⟨⟨1, 0, 0⟩⟩

instance : Neg ZT := ⟨fun u => ⟨-u.r0, -u.r1, -u.r2⟩⟩

@[simp] lemma mul_r0 (u v : ZT) : (u * v).r0 = u.r0 * v.r0 + 2 * (u.r1 * v.r2 + u.r2 * v.r1) := rfl
@[simp] lemma mul_r1 (u v : ZT) : (u * v).r1 = u.r0 * v.r1 + u.r1 * v.r0 + 2 * u.r2 * v.r2 := rfl
@[simp] lemma mul_r2 (u v : ZT) : (u * v).r2 = u.r0 * v.r2 + u.r1 * v.r1 + u.r2 * v.r0 := rfl
@[simp] lemma one_r0 : (1 : ZT).r0 = 1 := rfl
@[simp] lemma one_r1 : (1 : ZT).r1 = 0 := rfl
@[simp] lemma one_r2 : (1 : ZT).r2 = 0 := rfl
@[simp] lemma neg_r0 (u : ZT) : (-u).r0 = -u.r0 := rfl
@[simp] lemma neg_r1 (u : ZT) : (-u).r1 = -u.r1 := rfl
@[simp] lemma neg_r2 (u : ZT) : (-u).r2 = -u.r2 := rfl

instance : CommMonoid ZT where
  mul_assoc u v w := by ext <;> simp <;> ring
  one_mul u := by ext <;> simp
  mul_one u := by ext <;> simp
  mul_comm u v := by ext <;> simp <;> ring

lemma neg_mul_eq (u v : ZT) : -(u * v) = u * -v := by ext <;> simp <;> ring

lemma sq_def (u : ZT) : u ^ 2 = u * u := pow_two u

/-- θ = ∛2. -/
def θ : ZT := ⟨0, 1, 0⟩

/-- The fundamental unit ε = θ − 1 (norm 1). -/
def ε : ZT := ⟨-1, 1, 0⟩

/-- The norm `N(a + bθ + cθ²) = a³ + 2b³ + 4c³ − 6abc`. -/
def N (u : ZT) : ℤ := u.r0 ^ 3 + 2 * u.r1 ^ 3 + 4 * u.r2 ^ 3 - 6 * u.r0 * u.r1 * u.r2

lemma N_mul (u v : ZT) : N (u * v) = N u * N v := by
  simp only [N, mul_r0, mul_r1, mul_r2]; ring

lemma N_pow (u : ZT) (n : ℕ) : N (u ^ n) = N u ^ n := by
  induction n with
  | zero => simp [N]
  | succ n ih => rw [pow_succ, N_mul, ih, pow_succ]

lemma N_neg (u : ZT) : N (-u) = -N u := by simp only [N, neg_r0, neg_r1, neg_r2]; ring

lemma N_ε : N ε = 1 := by decide

end ZT
